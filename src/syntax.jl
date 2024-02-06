using REPL
export parse_node,
 purge_line_numbers,
 @pit,
 @pct,
 activate_interactive_mode!,
 pct_ast_transform,
 current_ast_transforms,
 @pluto_support,
 pct_ast_transform_pluto

const base_domains = [:Z, :I, :R, :C]

interactive_context = default_context()
interactive_let = nothing
interactive_result = nothing
interactive_placeholder = nothing

macro pit(expr, ctx=interactive_context, use_global_state=false)
    !use_global_state && ctx == interactive_context && error("must give a context if not using the global context")
    expr = purge_line_numbers(expr)
    if isa(expr, Symbol) || isa(expr, Number) || expr.head != :block
        top_level_nodes = [parse_node(expr)]
    else
        top_level_nodes = map(parse_node, expr.args)
    end

    statements = filter(n -> isa(n, Statement), top_level_nodes)
    domains = map(get_expr, filter(n -> isa(n, DomainNode), top_level_nodes))
    maps_types = map(get_expr, filter(n -> isa(n, MapTypeNode), top_level_nodes))
    return_node_list = filter(n -> isa(n, Expr), top_level_nodes)

    if !isempty(return_node_list)
        return_node = statement_to_let(statements, first(return_node_list))
        lhs = :(PCT.interactive_result, PCT.interactive_context)
    elseif !isempty(statements)
        return_node = statement_to_let(statements, :(var($(QuoteNode(:_)))))
        lhs = :(PCT.interactive_let, PCT.interactive_context)
    else
        return_node = nothing
        lhs = :(interactive_placeholder, PCT.interactive_context)
    end

    rhs = :(
        begin
            _ctx = $(ctx)
            $(domains...)
            $(maps_types...)
            ($(return_node), _ctx)
        end
    )
    !use_global_state && return esc(rhs)
    return esc(:(
        begin
            $(lhs) = $(rhs)
            first($(lhs)) 
        end))

end
    # elseif return_node === nothing
    #  esc(:(
    #     _, PCT.interactive_context = begin
    #         _ctx = $(ctx)
    #         $(domains...)
    #         $(maps_types...)
    #         ($(return_node), _ctx)
    #     end
    # ))
    # elseif !isempty(return_node_list)
    #  esc(:(
    #     PCT.interactive_result, PCT.interactive_context = begin
    #         _ctx = $(ctx)
    #         $(domains...)
    #         $(maps_types...)
    #         ($(return_node), _ctx)
    #     end
    # ))

    # end

"""
    @pct(expr, [ctx = :(TypeContext())])

The syntax `f, ctx = @pct expr` is used for starting a pct program.
`f` will be the last syntax node of the program, whereas `ctx` will
be the context containing the types that have been declared.
"""
macro pct(expr, ctx=:(TypeContext()))
    esc(:(
        let (f, ctx) = @pit($(expr), $(ctx))
            inference(f), ctx
        end
    ))
end

"""
    @pct(f, ctx, expr)

The syntax `g, _ = @pct f ctx expr` is used for continuing a pct program.
`f` can be a unfinished function defined in a previous pct program section.
An unfinished function serves the role of declaring variables.

`ctx` contains the types that have been declared so far. It will be 
mutated as more types are declared. The last expression of the section 
will be returned and put in `g`.
"""
macro pct(f, ctx, expr)
    f == :_ && return esc(:(@pct($(expr), $(ctx))))
    return esc(:(
        let (content, ctx) = @pit($(expr), $(ctx))
            inference(set_content($(f), content)), ctx
        end))
end

function pct_ast_transform(expr::Expr, repl=:cmd)
    expr = purge_line_numbers(expr)
    expr = purge_empty_exprs(expr)
    # @show expr
    # expr.args[2] = expr.args[2].args[1]
    expr = repl == :cmd ? expr.args[1] : expr
    expr = Expr(:macrocall, Symbol("@pct"), :(PCT.interactive_context), expr.args[1])
    return :(
        let (f, PCT.interactive_context) = $(expr)
            process_directive(f), PCT.interactive_context
        end
    )
end

current_ast_transforms() = isdefined(Base, :active_repl_backend) ?
                           Base.active_repl_backend.ast_transforms :
                           REPL.repl_ast_transforms

function pct_ast_transform_pluto(expr::Expr)
    expr.head == :block && return expr
    expr = purge_line_numbers(expr)
    expr = purge_empty_exprs(expr)

    expr = Expr(:macrocall, Symbol("@pct"), :(PCT.interactive_context), expr)
    expr = :(
        let (f, PCT.interactive_context) = $(expr)
            process_directive(f), PCT.interactive_context
        end
    )

    println(expr)
    println("-------------")

    return expr
end

macro pluto_support()
    esc(:(function Pluto.preprocess_expr(expr::Expr) 
        expr = pct_ast_transform_pluto(expr)
        if expr.head === :toplevel
            result = Expr(:block, expr.args...)
        elseif expr.head === :module
            result = Expr(:toplevel, expr)
        elseif expr.head === :(=) && (expr.args[1] isa Expr && expr.args[1].head == :curly)
            result = Expr(:const, expr)
        elseif expr.head === :incomplete
            result = Expr(:call, :(PlutoRunner.throw_syntax_error), expr.args...)
        else
            result = expr
        end
        
        return result
    end))
end

function activate_interactive_mode!()
    if isdefined(Main, :Pluto)
        eval(:(function Pluto.preprocess_expr(expr::Expr) 
            if expr.head === :toplevel
                result = Expr(:block, expr.args...)
            elseif expr.head === :module
                result = Expr(:toplevel, expr)
            elseif expr.head === :(=) && (expr.args[1] isa Expr && expr.args[1].head == :curly)
                result = Expr(:const, expr)
            elseif expr.head === :incomplete
                result = Expr(:call, :(PlutoRunner.throw_syntax_error), expr.args...)
            else
                result = expr
            end
            return pct_ast_transform(result)
        end))
    else
        current_transforms = current_ast_transforms()
        while !isempty(current_transforms)
            pop!(current_transforms)
        end
        pushfirst!(current_transforms, pct_ast_transform)
    end
end

# There are line number nodes in Julia's AST. They get in the way and are of no 
# use to as for now, so we are purging them from the start.

purge_line_numbers(e::Any) = e
function purge_line_numbers(expr::Expr)
    expr.args = filter(a -> !isa(a, LineNumberNode), expr.args)
    expr.args = map(purge_line_numbers, expr.args)
    return expr
end
purge_empty_exprs(e::Any) = e
function purge_empty_exprs(expr::Expr)
    expr.args = filter(a -> a != :(), expr.args)
    expr.args = map(purge_empty_exprs, expr.args)
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
        (func == :pullback || func == :𝒫) && return parse_node(Pullback, n)
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

struct MapTypeNode
    expr::Expr
end

get_expr(n::MapTypeNode) = n.expr

function parse_node(::Type{MapType}, s::Expr)
    s = purge_line_numbers(s)
    @assert s.args[1] == Symbol("@space")
    name = s.args[2]
    block = s.args[3]

    parse_pair(::Val{:symmetries}, t::Expr) = t
    parse_pair(::Val{:linear}, t::Bool) = t
    function parse_pair(::Val{:type}, t::Expr)
        bound_type(a::Symbol) = a in base_domains ? :($(a)()) : :(_ctx[$(QuoteNode(a))])
        params = :(VecType([$([bound_type(a) for a in t.args[1].args]...)]))
        return_type = :($(bound_type(first(t.args[2].args))))
        return (params, return_type)
    end

    pairs = Dict(a.args[1] => parse_pair(Val(a.args[1]), a.args[2]) for a in block.args)

    supported_properties = [:symmetries, :linear]
    properties = [:($(QuoteNode(k)) => $(pairs[k])) for k in supported_properties if haskey(pairs, k)]
    dict = :(Dict(:name => $(QuoteNode(name)), $(properties...)))
    return MapTypeNode(:(pct_push!(_ctx, $(QuoteNode(name)),
        MapType($(pairs[:type]...), $(dict),);
        replace=true)))
end

struct DomainNode
    expr::Expr
end

get_expr(n::DomainNode) = n.expr

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
    return DomainNode(:(
        pct_push!(_ctx, $(QuoteNode(name)), inference(Domain(
            $(base)(), $(lower), $(upper),
            meta=Dict(:name => $(QuoteNode(name)),
                :periodic => $(periodic),
                :symmetric => $(symmetric),
                :contractable => $(contractable)
            )
        )); replace=true)))
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
function parse_node(p::QuoteNode)
    name = "__" * string(p.value)
    :(var(Symbol($(name))))
end

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

    bounds = []
    args = []

    function parse_subst!(a::Expr)
        @assert a.head == Symbol("=")
        push!(bounds, :($(parse_node(a.args[1]))))
        push!(args, :($(parse_node(a.args[2]))))
    end

    parse_subst!.(substitutions)
    content = parse_node(l.args[2])

    return :(make_node(
        Let,
        pct_vec($(bounds...)),
        pct_vec($(args...)),
        $(content),
    ))
end

function parse_node(::Type{Pullback}, p::Expr)
    @assert p.args[1] == :pullback || p.args[1] == :𝒫
    mapp = parse_node(p.args[2])
    p = isa(p.args[2], Symbol) ? PrimitivePullback : Pullback
    return :(make_node($(p), $(mapp)))
end


function parse_node(::Type{T}, d::Expr) where {T<:AbstractDelta}
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
    bound, args = lhs.(statements), rhs.(statements)
    return :(make_node(Let, pct_vec($(bound...)), pct_vec($(args...)), $(return_value)))
end

function parse_node(::Type{PCTVector}, n::Expr)
    return :(pct_vec($(map(parse_node, n.args)...)))
end
