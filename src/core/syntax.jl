using REPL
export parse_node,
    purge_line_numbers,
    @pit,
    @pct,
    activate_interactive_mode!,
    pct_ast_transform,
    current_ast_transforms,
    @pluto_support,
    pct_ast_transform_pluto,
    continuition,
    convert_pct_type

const base_domains = [:N, :I, :R, :C, :FOT, :FField]

interactive_context = default_context()
interactive_let = nothing
interactive_result = nothing
interactive_placeholder = nothing

macro pit(expr, ctx=interactive_context, use_global_state=false, capture_local_scope=false)
    !use_global_state && ctx == interactive_context && error("must give a context if not using the global context")
    expr = purge_line_numbers(expr)
    if isa(expr, Symbol) || isa(expr, Number) || isa(expr, QuoteNode) || expr.head != :block
        top_level_nodes = [parse_node(expr)]
    else
        top_level_nodes = map(parse_node, expr.args)
    end

    statements = filter(n -> isa(n, Statement), top_level_nodes)
    domains = map(get_expr, filter(n -> isa(n, DomainNode), top_level_nodes))
    sizes = map(get_expr, filter(n -> isa(n, SizeNode), top_level_nodes))
    maps_types = map(get_expr, filter(n -> isa(n, MapTypeNode), top_level_nodes))
    return_node_list = filter(n -> isa(n, Expr) || isa(n, Symbol), top_level_nodes)

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
            $(sizes...)
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
            inference(continuition($(f), content)), ctx
        end))
end

function continuition(f::APN, new_body)
    new_terms..., body = terms(f)
    if isa(body, Var) && name(body) == :_
        return set_terms(f, new_terms..., new_body)
    else
        return set_terms(f, new_terms..., continuition(body, new_body))
    end
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

const univariate_symbols = [:log, :exp]

function parse_node(n::Expr)
    n = purge_line_numbers(n)
    n.head == Symbol(:quote) && return parse_quantum_field_node(n)
    n.head == :. && return parse_escape_node(n)
    if n.head == :macrocall
        n.args[1] == Symbol("@space") && return parse_maptype_node(n)
        n.args[1] == Symbol("@domain") && return parse_domain_node(n)
        n.args[1] == Symbol("@size") && return parse_size_node(n)
    end
    n.head == Symbol("->") && return parse_map_node(n)
    if n.head == :call
        func = n.args[1]
        (func == :∑ || func == :sum) && return parse_contraction_node(Sum, n)
        (func == :∫ || func == :int) && return parse_contraction_node(Integral, n)
        (func == :∏ || func == :prod) && return parse_prod_node(n)
        (func == :delta || func == :δ) && return parse_delta_node(Delta, n)
        func == :delta_not && return parse_delta_node(DeltaNot, n)
        (func == :indicator || func == :𝕀) && return parse_indicator_node(Indicator, n)
        (func == :in || func == :∈) && return parse_domain_indicator_node(Indicator, n)
        func == :+ && return parse_add_node(n)
        func == :- && return parse_negate_node(n)
        func == :* && return parse_mul_node(n)
        (func == :÷ || func == :div || func == :/) && return parse_div_node(n)
        func == :^ && return parse_monomial_node(n)
        func == :∘ && return parse_composite_node(n)
        func == :▷ && return parse_reverse_composite_node(n)
        func == :∇ && return parse_grad_node(n)
        func == :vac_exp && return parse_vac_exp_node(n)
        func in univariate_symbols && return parse_univariate_node(n)
        (func == :pullback || func == :𝒫) && return parse_pullback_node(n)
        return parse_node(AbstractCall, n)
    end
    n.head == :block && return parse_block_node(n)
    n.head == :let && return parse_let_node(n)
    n.head == Symbol("'") && return parse_conjugate_node(n)
    n.head == :(=) && return parse_statement_node(n)
    n.head == :tuple && return parse_pctvector_node(n)
    return :()
end

# The handling of division is adhoc.  There will be so many bugs because of this.
# TODO: Fix this abomination
function parse_div_node(n)
    nom = parse_node(n.args[2])
    denominator = parse_node(n.args[3])
    
    if n.args[1] == :/
        return :(mul($(nom), monomial($(denominator), constant(-1))))
    else
        return :(int_div($(nom), $(denominator)))
    end
end

function parse_composite_node(n::Expr)
    f1 = parse_node(n.args[2])
    f2 = parse_node(n.args[3])

    return :(composite($(f1), $(f2)))
end
function parse_grad_node(n::Expr)
    :(call(nabla(), ($(parse_node(n.args[2])))))
end

function parse_reverse_composite_node(n::Expr)
    f1 = parse_node(n.args[2])
    f2 = parse_node(n.args[3])

    return :(rev_composite($(f2), $(f1)))
end

function parse_univariate_node(n::Expr)
    if n.args[1] == :exp
        return :(pct_exp($(parse_node(n.args[2]))))
    elseif n.args[1] == :log
        return :(pct_log($(parse_node(n.args[2]))))
    end
end

function parse_escape_node(n::Expr)
    n.args[1] == :jl || error("Escape node must start with jl.")
    return n.args[2].value
end

struct MapTypeNode
    expr::Expr
end

get_expr(n::MapTypeNode) = n.expr

function parse_maptype_node(s::Expr)
    s = purge_line_numbers(s)
    @assert s.args[1] == Symbol("@space")
    name = s.args[2]
    type_params = nothing
    if isa(name, Expr) && name.head == :curly
        type_params = name.args[2:end]
        name = name.args[1]
    end
    block = s.args[3]

    parse_pair(::Val{:symmetries}, t::Expr) = t
    parse_pair(::Val{:linear}, t::Bool) = t
    parse_pair(::Val{:off_diag}, t::Bool) = t
    function parse_pair(::Val{:type}, t::Expr)
        bound_type(a::Symbol) = a in base_domains ? :($(a)()) : :(_ctx[$(QuoteNode(a))])
        bound_type(a::Expr) = :(parametrize_type(_ctx[$(QuoteNode(a.args[1]))], $(map(parse_node, a.args[2:end])...)))
        params = :(VecType([$([bound_type(a) for a in t.args[1].args]...)]))
        return_type = :($(bound_type(first(t.args[2].args))))
        return (params, return_type)
    end

    pairs = Dict(a.args[1] => parse_pair(Val(a.args[1]), a.args[2]) for a in block.args)

    supported_properties = [:symmetries, :linear, :off_diag]
    properties = [:($(QuoteNode(k)) => $(pairs[k])) for k in supported_properties if haskey(pairs, k)]
    dict = :(Dict(:name => $(QuoteNode(name)), $(properties...)))
    maptype = :(MapType($(pairs[:type]...), $(dict),))

    if type_params !== nothing
        type_params = map(parse_node, type_params)
        maptype = :(ParametricMapType([$(type_params...)], $(maptype)))
    end

    return MapTypeNode(:(push_type!(_ctx, $(QuoteNode(name)),
        $(maptype); replace=true)))
end

struct DomainNode
    expr::Expr
end

get_expr(n::DomainNode) = n.expr

function parse_domain_node(n::Expr)
    name = n.args[2]
    type_params = nothing
    if isa(name, Expr) && name.head == :curly
        type_params = name.args[2:end]
        name = name.args[1]
    end
    block = n.args[3]
    periodic = QuoteNode(false)
    contractable = QuoteNode(true)
    symmetric = QuoteNode(false)
    tensorize = QuoteNode(true)
    domain = :()
    if isa(block, Expr) && block.head == :block
        pairs = Dict(a.args[1] => a.args[2] for a in block.args)
        base = haskey(pairs, :base) ? pairs[:base] : :N
        #= (haskey(pairs, :lower) || haskey(pairs, :upper)) && @warn "Domain boundaries are not yet properly implemented. Do not use." =#
        lower = haskey(pairs, :lower) ? parse_node(pairs[:lower]) : minfty()
        upper = haskey(pairs, :upper) ? parse_node(pairs[:upper]) : infty()
        periodic = haskey(pairs, :periodic) && (pairs[:periodic])
        tensorize = haskey(pairs, :tensorize) && (pairs[:tensorize])
        symmetric = haskey(pairs, :symmetric) && (pairs[:symmetric])
        contractable = haskey(pairs, :contractable) ? (pairs[:contractable]) : true
        domain = :(inference(Domain(
            $(base)(), $(lower), $(upper),
            meta=Dict(:name => $(QuoteNode(name)),
                      :periodic => $(periodic),
                      :tensorize => $(tensorize),
                      :symmetric => $(symmetric),
                      :contractable => $(contractable)
                      )
        ), _ctx))
    elseif isa(block, Expr) && block.head == :curly
        param_args = parse_node.(block.args[2:end])
        domain_name = block.args[1]
        domain = :(parametrize_type(_ctx[$(QuoteNode(domain_name))], $(param_args...)))
    end
    if type_params !== nothing
        type_params = map(parse_node, type_params)
        domain = :(ParametricDomain([$(type_params...)], $(domain)))
    end

    return DomainNode(:(push_type!(_ctx, $(QuoteNode(name)), $(domain)); replace = true))
end

struct SizeNode
    expr::Expr
end

get_expr(n::SizeNode) = n.expr

function parse_size_node(n::Expr)
    base, names = n.args[2], n.args[3:end]

    if base in base_domains
        type = :($(base)())
    elseif isa(base, Expr)
        type = :(parametrize_type(_ctx[$(QuoteNode(base.args[1]))], $(map(parse_node, a.args[2:end])...)))
    end

    pushes = map(name -> :(
            push_var!(_ctx, $(QuoteNode(name)),
            var($(QuoteNode(name)), $(type))
        )
        ), names)
    return SizeNode(:(
        begin
            $(pushes...)
        end
    ))
end

struct Param <: APN end

function parse_map_node(f::Expr)
    @assert f.head == Symbol("->")

    bound = f.args[1]
    parametric_types = nothing
    if bound.head == :call
        parametric_types = bound.args[1].args
        bound = bound.args[2:end]
    elseif bound.head == :tuple
        params = bound.args
    else
        params = Vector{Expr}([bound])
    end

    body = f.args[2]

    result_map = :(pct_map($(map(p -> parse_node(Param, p), params)...), $(parse_node(body))))
    parametric_types === nothing && return result_map

    return :(set_type($(result_map),
        ParametricMapType($(map(parse_node, parametric_types)),
            UndeterminedPCTType()
        )))
end


function parse_node(::Type{Param}, p::Union{Expr,Symbol})
    if isa(p, Symbol)
        return :(var($(QuoteNode(p))))
    end

    if p.head == Symbol("::")
        name, type = p.args
        type_params = []
        if isa(type, Expr)
            type_params = type.args[2:end]
            type = type.args[1]
        end
        type = type in base_domains ? :($(type)()) : :(_ctx[$(QuoteNode(type))])
        type = :(parametrize_type($(type), $(map(parse_node, type_params)...)))
        isa(name, Symbol) && return :(var($(QuoteNode(name)), $(type)))
    end
    if p.head == :call && p.args[1] == :∈
        param = p.args[2]
        domain = p.args[3]
        lower, upper = parse_node(domain.args[1]), parse_node(domain.args[2])
        if param.head == Symbol("::")
            name, type = param.args
            type = type in base_domains ? :($(type)()) : :(_ctx[$(QuoteNode(type))])
            return :(var($(QuoteNode(name)), (Domain($(type), $(lower), $(upper), Dict(:name => :_λ)))))
        end
        return :(var($(parse_node(param)), $(parse_node(domain))))
    end

end

function parse_node(p::Symbol)
    (p == :∞ || p == :infty) && return :(infty())
    :(var($(QuoteNode(p))))
end
function parse_node(p::QuoteNode)
    return parse_quantum_field_node(p)
    #= name = "__" * string(p.value)
    :(var(Symbol($(name)))) =#
end
function parse_quantum_field_node(n::QuoteNode)
    x = :(var(:x, C()))
    n.value == :II && return :(pct_map($x, fermi_scalar($x)))

    return :(annihilate($(QuoteNode(n.value))))
end

function parse_vac_exp_node(n::Expr)
    return :(make_node(VacExp, $(parse_node.(n.args[2:end])...)))
end

parse_node(i::Number) = :(constant($(i)))

function parse_node(::Type{AbstractCall}, c::Expr)
    @assert c.head == :call
    func = c.args[1]

    return :(call($(parse_node(func)), $(parse_node.(c.args[2:end])...)))
end

function parse_add_node(a::Expr)
    @assert a.args[1] == :+
    return :(add($(parse_node.(a.args[2:end])...)))
end

function parse_negate_node(n::Expr)
    @assert n.args[1] == :-
    length(n.args) == 2 && return :(mul(constant(-1), $(parse_node(n.args[2]))))
    return :(add($(parse_node(n.args[2])), mul(constant(-1), $(parse_node(n.args[3])))))
end

function parse_mul_node(m::Expr)
    @assert m.args[1] == :*
    return :(mul($(parse_node.(m.args[2:end])...)))
end


function parse_monomial_node(m::Expr)
    @assert m.args[1] == :^
    return :(monomial($(parse_node.(m.args[2:end])...)))
end

function parse_contraction_node(::Type{T}, s::Expr) where {T<:Contraction}
    @assert s.args[1] in [:sum, :int, :∑, :∫]
    if hasfield(typeof(s.args[2]), :head) && s.args[2].head == :tuple
        params = s.args[2].args
    else
        params = s.args[2:end-1]
    end

    param_nodes = (n -> parse_node(Param, n)).(params)
    constructor = T == Sum ? pct_sum : pct_int
    return :($(constructor)($(param_nodes...), $(parse_node(s.args[end]))))
end

function parse_prod_node(s::Expr)
    @assert s.args[1] in [:prod, :∏]
    if hasfield(typeof(s.args[2]), :head) && s.args[2].head == :tuple
        params = s.args[2].args
    else
        params = s.args[2:end-1]
    end

    param_nodes = (n -> parse_node(Param, n)).(params)
    return :(pct_product($(param_nodes...), $(parse_node(s.args[end]))))
end

function parse_let_node(l::Expr)
    @assert l.head == Symbol("let")

    substitutions = l.args[1].head == :block ? l.args[1].args : [l.args[1]]

    bounds = []
    args = []

    function parse_subst!(a::Expr)
        if a.head == Symbol("=")
            push!(bounds, :($(parse_node(a.args[1]))))
            push!(args, :($(parse_node(a.args[2]))))
        else
            a = a.args[1]
            push!(bounds, :(pct_copy($(parse_node(a.args[1])))))
            push!(args, :($(parse_node(a.args[2]))))
        end
    end

    parse_subst!.(substitutions)
    content = parse_node(l.args[2])

    return :(pct_let(
        $(bounds...),
        $(args...),
        $(content),
    ))
end

function parse_pullback_node(p::Expr)
    @assert p.args[1] == :pullback || p.args[1] == :𝒫
    mapp = parse_node(p.args[2])
    p = isa(p.args[2], Symbol) ? PrimitivePullback : Pullback
    return :(make_node($(p), $(mapp)))
end


function parse_delta_node(::Type{T}, d::Expr) where {T<:AbstractDelta}
    @assert d.args[1] in [:delta, :delta_not, :δ]
    upper_params = isa(d.args[2], Symbol) ? [d.args[2]] : d.args[2].args
    lower_params = isa(d.args[3], Symbol) ? [d.args[3]] : d.args[3].args
    upper_nodes = map(n -> parse_node(Param, n), upper_params)
    lower_nodes = map(n -> parse_node(Param, n), lower_params)
    constructor = T == Delta ? :delta : :delta_not
    return :($(constructor)($(upper_nodes...), $(lower_nodes...), $(parse_node(d.args[4]))))
end

function parse_conjugate_node(c::Expr)
    return :(conjugate($(parse_node(c.args[1]))))
end

function parse_statement_node(n::Expr)
    lhs = parse_node(n.args[1])
    rhs = parse_node(n.args[2])
    return Statement(lhs, rhs)
end

function parse_block_node(n::Expr)
    parsed_body = parse_node.(n.args)
    statements = parsed_body[1:end-1]
    return_value = parsed_body[end]
    return statement_to_let(statements, return_value)
end

function statement_to_let(statements::Vector, return_value::Union{Expr,Symbol})
    isempty(statements) && return return_value
    bound, args = lhs.(statements), rhs.(statements)
    return :(pct_let($(bound...), $(args...), $(return_value)))
end

function parse_pctvector_node(n::Expr)
    return :(pct_vec($(map(parse_node, n.args)...)))
end

function parse_indicator_node(::Type{Indicator}, n::Expr)
    args = map(parse_node, n.args[2:end])

    return :(indicator($(args[2]), $(args[1]), $(args[end])))
end

function parse_domain_indicator_node(Indicator, n)
    i = parse_node(n.args[2])
    d = :(_ctx[$(QuoteNode(n.args[3]))])
    body = parse_node(n.args[end])

    return :(domain_indicator($(i), $(d), $(body)))
end

function convert_pct_type(::T) where T <: Number
    if T <: Integer
        return I()
    elseif T <: Real
        return R()
    elseif T <: Number
        return C()
    else
        error("type $(T) not supported")
    end
end

function convert_pct_type(tensor::RangedTensor{S, T}) where {S <: Number, T}
    return  MapType(VecType([Domain(N(), constant(l), constant(u)) for (l, u) in tensor.ranges]), convert_pct_type(S(0)))
end

function convert_pct_type(::T) where T
    elem_type, n_dims = if T.name.name == :Array
         T.parameters
    elseif T.name.name == :Vector
        first(T.parameters), 1
    else
        error("type $(T) not supported")
    end
    output_type = convert_pct_type(elem_type(0))
    return MapType(VecType(fill(N(), n_dims)), output_type)
end

