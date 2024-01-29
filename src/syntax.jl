export parse_node, purge_line_numbers, @pit, @pct 

const base_domains = [:Z, :I, :R, :C]

macro pit(expr, ctx)
    expr = purge_line_numbers(expr)
    if isa(expr, Symbol) || isa(expr, Number) || expr.head != :block
        top_level_nodes = [parse_node(expr)]
    else
        top_level_nodes = map(parse_node, expr.args)
    end

    statements = filter(n->isa(n, Statement), top_level_nodes)
    non_statements = filter(n->!isa(n, Statement), top_level_nodes)

    if isa(last(top_level_nodes), Statement)
        return_node = statement_to_let(statements, :(var($(QuoteNode(:_)))))
    else 
        return_node = last(non_statements)
        return_node = statement_to_let(statements, return_node)
        non_statements = non_statements[1:end-1]
    end

    return esc(:(
        begin
            _ctx = $(ctx)
            $(non_statements...)
            ($(return_node), _ctx)
        end
    ))
end

"""
    @pct(expr, [ctx = :(TypeContext())])

The syntax `f, ctx = @pct expr` is used for starting a pct program.
`f` will be the last syntax node of the program, whereas `ctx` will
be the context containing the types that have been declared.
"""
macro pct(expr, ctx=:(TypeContext()))
    esc(:(let (f, ctx) = @pit($(expr), $(ctx))
        inference(f), ctx
    end))
end

"""
    @pct(f, ctx, expr)

The syntax `g = @pct f ctx expr` is used for continuing a pct program.
`f` can be a unfinished function defined in a previous pct program section.
An unfinished function serves the role of declaring variables.

`ctx` contains the types that have been declared so far. It will be 
mutated as more types are declared. The last expression of the section 
will be returned and put in `g`.
"""
macro pct(f, ctx, expr)
    f == :_ && return esc(:(first(@pct($(expr), $(ctx)))))
    return esc(:(inference(set_content($(f), first(@pit($(expr), $(ctx)))))))
end


# There are line number nodes in Julia's AST. They get in the way and are of no 
# use to as for now, so we are purging them from the start.

purge_line_numbers(e::Any) = e
function purge_line_numbers(expr::Expr)
    expr.args = filter(a -> !isa(a, LineNumberNode), expr.args)
    expr.args = map(purge_line_numbers, expr.args)
    return expr
end

function parse_node(::LineNumberNode)
    return nothing
end

struct Statement
    lhs::Expr
    rhs::Expr
end
lhs(s::Statement) = s.lhs
rhs(s::Statement) = s.rhs

struct Block
    statements::Vector{Statement}
    return_value::Expr
end

function parse_node(n::Expr)
    n = purge_line_numbers(n)
    n.head == Symbol(:quote) && return n.args[1]
    if n.head == :macrocall
        n.args[1] == Symbol("@space") && return parse_node(MapType, n)
        n.args[1] == Symbol("@domain") && return parse_node(Domain, n)
    end
    n.head == Symbol("->") && return parse_node(Map, n)
    if n.head == :call
        func = n.args[1]
        (func == :∑ || func == :sum) && return parse_node(Sum, n)
        (func == :∫ || func == :int) && return parse_node(Integral, n)
        (func == :∏ || func == :prod) && return parse_node(Prod, n)
        func == :delta && return parse_node(Delta, n)
        func == :delta_not && return parse_node(DeltaNot, n)
        func == :+ && return parse_node(Add, n)
        func == :- && return parse_node(Negate, n)
        func == :* && return parse_node(Mul, n)
        func == :^ && return parse_node(Monomial, n)
        func == :pullback && return parse_node(Pullback, n)
        return parse_node(AbstractCall, n)
    end
    n.head == :block && return parse_node(Block, n)
    n.head == :let && return parse_node(Let, n)
    n.head == Symbol("'") && return parse_node(Conjugate, n)
    n.head == :(=) && return parse_node(Statement, n)
    n.head == :tuple && return parse_node(PCTVector, n)
    return :()
    #= n.head == :tuple && return parse_tuple_node(n) =#
end

function parse_node(::Type{MapType}, s::Expr)
    s = purge_line_numbers(s)
    @assert s.args[1] == Symbol("@space")
    name = s.args[2]
    block = s.args[3]

    parse_pair(::Val{:symmetries}, t::Expr) = t
    parse_pair(::Val{:linear}, t::Bool) = t
    function parse_pair(::Val{:type}, t::Expr)
        from_type(a::Symbol) = a in base_domains ? :($(a)()) : :(_ctx[$(QuoteNode(a))])
        params = :(VecType([$([from_type(a) for a in t.args[1].args]...)]))
        return_type = :($(from_type(first(t.args[2].args))))
        return (params, return_type)
    end

    pairs = Dict(a.args[1] => parse_pair(Val(a.args[1]), a.args[2]) for a in block.args)

    supported_properties = [:symmetries, :linear]
    properties = [:($(QuoteNode(k)) => $(pairs[k])) for k in supported_properties if haskey(pairs, k)]
    dict = :(Dict(:name => $(QuoteNode(name)), $(properties...)))
    return :(pct_push!(_ctx, $(QuoteNode(name)),
        MapType($(pairs[:type]...), $(dict),);
        replace=true))
end

function parse_node(::Type{Domain}, n::Expr)
    name = n.args[2]
    block = n.args[3]
    periodic = QuoteNode(false)
    contractable = QuoteNode(true)
    symmetric = QuoteNode(false)
    if isa(block, Expr)
        pairs = Dict(a.args[1] => a.args[2] for a in block.args)
        base = haskey(pairs, :base) ? pairs[:base] : :Z
        lower = haskey(pairs, :lower) ? parse_node(pairs[:lower]) : mul(constant(-1), var(:Infty))
        upper = haskey(pairs, :upper) ? parse_node(pairs[:upper]) : var(:Infty)
        periodic = QuoteNode(haskey(pairs, :periodic) && (pairs[:periodic]))
        symmetric = QuoteNode(haskey(pairs, :symmetric) && (pairs[:symmetric]))
        contractable = QuoteNode(haskey(pairs, :contractable) ? (pairs[:contractable]) : true)
    else
        base = n.args[3]
        lower, upper = parse_node(n.args[4]), parse_node(n.args[5])
    end
    return :(
        pct_push!(_ctx, $(QuoteNode(name)), inference(Domain(
            $(base)(), $(lower), $(upper),
            meta = Dict(:name => $(QuoteNode(name)), 
            :periodic => $(periodic),
            :symmetric => $(symmetric),
            :contractable => $(contractable)
            )
        )); replace=true))
end

struct Param <: APN end

function parse_node(::Type{Map}, f::Expr)
    @assert f.head == Symbol("->")
    params = f.args[1].head == :tuple ? f.args[1].args : Vector{Expr}([f.args[1]])
    body = f.args[2]

    return :(pct_map($(map(p -> parse_node(Param, p), params)...), $(parse_node(body))))
end


function parse_node(::Type{Param}, p::Union{Expr,Symbol})
    if isa(p, Symbol)
        return :(var($(QuoteNode(p))))
    end

    if p.head == Symbol("::")
        name, type = p.args
        type = type in base_domains ? :($(type)()) : :(_ctx[$(QuoteNode(type))])
        isa(name, Symbol) && return :(var($(QuoteNode(name)), $(type)))
    end
    if p.head == :call && p.args[1] == :∈
        param = p.args[2]
        domain = p.args[3]
        if param.head == Symbol("::")
            name, type = param.args
            type = type in base_domains ? :($(type)()) : :(_ctx[$(QuoteNode(type))])
            return :(var($(parse_node(domain)), $(QuoteNode(name)), $(type)))
        end
        return :(var($(parse_node(param)), $(parse_node(domain))))
    end

end

parse_node(p::Symbol) = :(var($(QuoteNode(p))))

parse_node(i::Number) = :(constant($(i)))

function parse_node(::Type{AbstractCall}, c::Expr)
    @assert c.head == :call
    func = c.args[1]

    return :(call($(parse_node(func)), $(parse_node.(c.args[2:end])...)))
end

function parse_node(::Type{Add}, a::Expr)
    @assert a.args[1] == :+
    return :(add($(parse_node.(a.args[2:end])...)))
end

function parse_node(::Type{Negate}, n::Expr)
    @assert n.args[1] == :-
    length(n.args) == 2 && return :(mul(constant(-1), $(parse_node(n.args[2]))))
    return :(add($(parse_node(n.args[2])), mul(constant(-1), $(parse_node(n.args[3])))))
end

function parse_node(::Type{Mul}, m::Expr)
    @assert m.args[1] == :*
    return :(mul($(parse_node.(m.args[2:end])...)))
end


function parse_node(::Type{Monomial}, m::Expr)
    @assert m.args[1] == :^
    return :(monomial($(parse_node.(m.args[2:end])...)))
end

function parse_node(::Type{T}, s::Expr) where {T<:Contraction}
    @assert s.args[1] in [:sum, :int, :∑, :∫]
    if hasfield(typeof(s.args[2]), :head) && s.args[2].head == :tuple
        params = s.args[2].args
    else
        params = [s.args[2]]
    end

    param_nodes = (n -> parse_node(Param, n)).(params)
    constructor = T == Sum ? pct_sum : pct_int
    return :($(constructor)($(param_nodes...), $(parse_node(s.args[3]))))
end

function parse_node(::Type{Prod}, s::Expr)
    @assert s.args[1] in [:prod, :∏]
    if hasfield(typeof(s.args[2]), :head) && s.args[2].head == :tuple
        params = s.args[2].args
    else
        params = [s.args[2]]
    end

    param_nodes = (n -> parse_node(Param, n)).(params)
    return :(pct_product($(param_nodes...), $(parse_node(s.args[3]))))
end

function parse_node(::Type{Let}, l::Expr)
    @assert l.head == Symbol("let")

    substitutions = l.args[1].head == :block ? l.args[1].args : [l.args[1]]

    froms = []
    args = []

    function parse_subst!(a::Expr)
        @assert a.head == Symbol("=")
        push!(froms, :($(parse_node(a.args[1]))))
        push!(args, :($(parse_node(a.args[2]))))
    end

    parse_subst!.(substitutions)
    content = parse_node(l.args[2])

    return :(make_node(
        Let,
        pct_vec($(froms...)),
        pct_vec($(args...)),
        $(content),
    ))
end

function parse_node(::Type{Pullback}, p::Expr)
    @assert p.args[1] == :pullback
    mapp = parse_node(p.args[2])
    p = isa(p.args[2], Symbol) ? PrimitivePullback : Pullback
    return :(make_node($(p), $(mapp)))
end


function parse_node(::Type{T}, d::Expr) where T <: AbstractDelta
    @assert d.args[1] in [:delta, :delta_not]
    upper_params = isa(d.args[2], Symbol) ? [d.args[2]] : d.args[2].args
    lower_params = isa(d.args[3], Symbol) ? [d.args[3]] : d.args[3].args
    upper_nodes = map(n -> parse_node(Param, n), upper_params)
    lower_nodes = map(n -> parse_node(Param, n), lower_params)
    constructor = T == Delta ? :delta : :delta_not
    return :($(constructor)($(upper_nodes...), $(lower_nodes...), $(parse_node(d.args[4]))))
end

function parse_node(::Type{Conjugate}, c::Expr)
    return :(conjugate($(parse_node(c.args[1]))))
end

function parse_node(::Type{Statement}, n::Expr)
    lhs = parse_node(n.args[1])
    rhs = parse_node(n.args[2])
    return Statement(lhs, rhs)
end

function parse_node(::Type{Block}, n::Expr)
    parsed_body = parse_node.(n.args)
    statements = parsed_body[1:end-1]
    return_value = parsed_body[end]
    return statement_to_let(statements, return_value)
end

function statement_to_let(statements::Vector, return_value::Expr)
    isempty(statements) && return return_value
    from, args = lhs.(statements), rhs.(statements)
    return :(make_node(Let, pct_vec($(from...)), pct_vec($(args...)), $(return_value)))
end

function parse_node(::Type{PCTVector}, n::Expr)
    return :(pct_vec($(map(parse_node, n.args)...)))
end
