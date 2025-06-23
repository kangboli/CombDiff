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

macro pit(expr, ctx=interactive_context)
    top_level_nodes = hasfield(typeof(expr), :head) && expr.head == :block ?
                      map(parse_node, expr.args) : [parse_node(expr)]

    statements = filter(n -> isa(n, AbstractStatement), top_level_nodes)
    typenodes = map(get_expr, filter(n -> (isa(n, DomainNode) ||
                                           isa(n, MapTypeNode) ||
                                           isa(n, ProductTypeNode) ||
                                           isa(n, AliasNode)), top_level_nodes))
    return_node_list = filter(n -> isa(n, Expr) || isa(n, Symbol), top_level_nodes)

    return_node = isempty(return_node_list) ? :(var($(QuoteNode(:_)))) : first(return_node_list)
    return_node = statement_to_let(statements, return_node)

    rhs = :(
        begin
            _ctx = $(ctx)
            $(typenodes...)
            ($(return_node), _ctx)
        end
    )
    return esc(rhs)
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
            f, ctx
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
            continuition($(f), content), ctx
        end))
end

function continuition(f::APN, new_body)
    isa(f, Var) && name(f) == :_ && return new_body
    new_terms..., body = terms(f)
    isa(body, Var) && name(body) == :_ && return set_terms(f, new_terms..., new_body)
    return set_terms(f, new_terms..., continuition(body, new_body))
end

function pct_ast_transform(expr::Expr, repl=:cmd)
    expr = purge_line_numbers(expr)
    expr = purge_empty_exprs(expr)
    # @show expr
    # expr.args[2] = expr.args[2].args[1]
    expr = repl == :cmd ? expr.args[1] : expr
    expr = Expr(:macrocall, Symbol("@pct"), :(CombDiff.interactive_context), expr.args[1])
    return :(
        let (f, CombDiff.interactive_context) = $(expr)
            process_directive(f), CombDiff.interactive_context
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

    expr = Expr(:macrocall, Symbol("@pct"), :(CombDiff.interactive_context), expr)
    expr = :(
        let (f, CombDiff.interactive_context) = $(expr)
            process_directive(f), CombDiff.interactive_context
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
# use to us for now, so we are purging them from the start.

purge_line_numbers(e::Any) = e
function purge_line_numbers(expr::Expr)
    #= expr.args = filter(a -> !isa(a, LineNumberNode), expr.args)
    expr.args = map(purge_line_numbers, expr.args) =#
    expr.args = [purge_line_numbers(a) for a in expr.args if !isa(a, LineNumberNode)]
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

abstract type AbstractStatement end

struct InLineStatement <: AbstractStatement
    lhs::Expr
    rhs::Expr
end

struct Statement <: AbstractStatement
    lhs::Expr
    rhs::Expr
end

struct MutatingStatement <: AbstractStatement
    lhs::Expr
    rhs::Expr
end

lhs(s::AbstractStatement) = s.lhs
lhs(s::Statement) = :(CombDiff.pct_copy($(s.lhs)))
rhs(s::AbstractStatement) = s.rhs

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
        n.args[1] == Symbol("@alias") && return parse_alias_node(n)
        #= n.args[1] == Symbol("@size") && return parse_size_node(n) =#
    end
    n.head == :struct && return parse_product_type_node(n)
    n.head == Symbol("->") && return parse_map_node(n)
    if n.head == :call
        func = n.args[1]
        (func == :∑ || func == :sum) && return parse_contraction_node(Sum, n)
        (func == :∫ || func == :int) && return parse_contraction_node(Integral, n)
        (func == :∏ || func == :prod) && return parse_prod_node(n)
        (func == :∧ || func == :fold || func == :seq) && return parse_fold_node(n)
        func == :fixed && return parse_fixed_node(n)
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
        (func == :∇ || func == :grad) && return parse_grad_node(n)
        #= (func == :𝒥 || func == :jacobian) && return parse_jacobian_node(n) =#
        func == :vac_exp && return parse_vac_exp_node(n)
        func in univariate_symbols && return parse_univariate_node(n)
        (func == :pullback || func == :𝒫) && return parse_pullback_node(n)
        (func == :pushforward || func == :ℱ) && return parse_pushforward_node(n)
        (isa(func, Expr) && func.head == :curly) && return parse_parametric_call_node(n)
        return parse_node(AbstractCall, n)
    end
    n.head == :block && return parse_block_node(n)
    n.head == :let && return parse_let_node(n)
    n.head == Symbol("'") && return parse_conjugate_node(n)
    (n.head == :(=) || n.head == :(:=)) && return parse_statement_node(n)
    n.head == :tuple && isa(n.args[1], Expr) && n.args[1].head == :parameters && return parse_group_index_node(n)
    n.head == :tuple && return parse_pctvector_node(n)
    n.head == Symbol("::") && return parse_node(Param, n)
    return :()
end

struct ProductTypeNode
    expr::Expr
end

get_expr(n::ProductTypeNode) = n.expr

function parse_product_type_node(n)
    if isa(n.args[2], Symbol)
        type_name = n.args[2]
        fields = n.args[end].args
        fields = :([$(map(f -> parse_node(Param, f), fields)...)])
        vectype = :(
            let field_vars = $(fields)
                ProductType($(QuoteNode(type_name)), get_type.(field_vars), name.(field_vars))
            end
        )

        return ProductTypeNode(:(push_type!(_ctx, $(QuoteNode(type_name)),
            $(vectype); replace=true)))

    else
        type_name = n.args[2].args[1]
        parameters = map(parse_node, n.args[2].args[2:end])
        fields = n.args[end].args
        fields = :([$(map(f -> parse_node(Param, f), fields)...)])
        vectype = :(
            let field_vars = $(fields)
                ProductType($(QuoteNode(type_name)), get_type.(field_vars), name.(field_vars))
            end
        )

        return ProductTypeNode(:(push_type!(_ctx, $(QuoteNode(type_name)),
            ParametricProductType(
                [$(parameters...)],
                $(vectype))
        )))
    end
end

# The handling of division is adhoc.  There will be so many bugs because of this.
# TODO: Fix this abomination
function parse_div_node(n)
    nom = parse_node(n.args[2])
    denominator = parse_node(n.args[3])

    if n.args[1] == :/
        return :(CombDiff.mul($(nom), monomial($(denominator), constant(-1))))
    else
        return :(CombDiff.int_div($(nom), $(denominator)))
    end
end

function parse_composite_node(n::Expr)
    f1 = parse_node(n.args[2])
    f2 = parse_node(n.args[3])

    return :(CombDiff.composite($(f1), $(f2)))
end
function parse_grad_node(n::Expr)
    :(CombDiff.grad($(parse_node(n.args[2]))))
    #= :(CombDiff.propagate_k(CombDiff.pullback($(parse_node(n.args[2]))))) =#
end

#= function parse_jacobian_node(n)
    :(CombDiff.jacobian($(parse_node(n.args[2]))))
end =#

function parse_pushforward_node(n)
    :(CombDiff.pushforward($(parse_node(n.args[2]))))
end

function parse_reverse_composite_node(n::Expr)
    f1 = parse_node(n.args[2])
    f2 = parse_node(n.args[3])

    return :(CombDiff.rev_composite($(f2), $(f1)))
end

function parse_univariate_node(n::Expr)
    if n.args[1] == :exp
        return :(CombDiff.pct_exp($(parse_node(n.args[2]))))
    elseif n.args[1] == :log
        return :(CombDiff.pct_log($(parse_node(n.args[2]))))
    end
end

function parse_escape_node(n::Expr)
    n.args[1] == :jl && return n.args[2].value

    return :(pct_dot(var($(QuoteNode(n.args[1]))), $(QuoteNode(n.args[2].value))))

    #= name = Symbol("$(n.args[1])__dot__$(n.args[2].value)")
    return :(var($(QuoteNode(name)))) =#
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

    parse_pair(::Val{:symmetries}, t::Expr) = parse_node(t)
    parse_pair(::Val{:linear}, t::Bool) = t
    parse_pair(::Val{:off_diag}, t::Bool) = t
    function parse_pair(::Val{:type}, t::Expr)
        bound_type(a::Symbol) = a in base_domains ? :($(a)()) : :(_ctx[$(QuoteNode(a))])
        bound_type(a::Expr) = :(CombDiff.parametrize_type(_ctx[$(QuoteNode(a.args[1]))], $(map(parse_node, a.args[2:end])...)))
        params = :(VecType([$([bound_type(a) for a in t.args[1].args]...)]))
        return_type = :($(bound_type(first(t.args[2].args))))
        return (params, return_type)
    end

    pairs = Dict(a.args[1] => parse_pair(Val(a.args[1]), a.args[2]) for a in block.args)

    supported_properties = [:symmetries, :linear, :off_diag]
    properties = [:($(QuoteNode(k)) => $(pairs[k])) for k in supported_properties if haskey(pairs, k)]
    dict = :(Dict(:name => $(QuoteNode(name)), $(properties...)))
    maptype = :(CombDiff.MapType($(pairs[:type]...), $(dict),))

    if type_params !== nothing
        type_params = map(parse_node, type_params)
        maptype = :(CombDiff.ParametricMapType([$(type_params...)], $(maptype)))
    end

    return MapTypeNode(:(push_type!(_ctx, $(QuoteNode(name)),
        $(maptype); replace=true)))
end

struct DomainNode
    expr::Expr
end

get_expr(n::DomainNode) = n.expr

struct AliasNode
    alias::Symbol
    aliased_type::Expr
end

get_alias(a::AliasNode) = a.alias
get_aliased_type(a::AliasNode) = a.aliased_type

get_expr(a::AliasNode) = :(push_type!(_ctx, $(QuoteNode(get_alias(a))), $(get_aliased_type(a))))

function parse_alias_node(n::Expr)
    alias = n.args[2]
    type_expr = n.args[3]
    type = if type_expr.head == :curly
        :(parametrize_type(_ctx[$(QuoteNode(type_expr.args[1]))], $(parse_node.(type_expr.args[2:end])...)))
    else
        :(_ctx[$(QuoteNode(type_expr))])
    end

    return AliasNode(alias, type)
end

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
        domain = :(Domain(
            $(base)(), $(lower), $(upper),
            meta=Dict(:name => $(QuoteNode(name)),
                :periodic => $(periodic),
                :tensorize => $(tensorize),
                :symmetric => $(symmetric),
                :contractable => $(contractable)
            )
        ))
    elseif isa(block, Expr) && block.head == :curly
        param_args = parse_node.(block.args[2:end])
        domain_name = block.args[1]
        domain = :(CombDiff.parametrize_type(_ctx[$(QuoteNode(domain_name))], $(param_args...)))
    end
    if type_params !== nothing
        type_params = map(parse_node, type_params)
        domain = :(CombDiff.ParametricDomain([$(type_params...)], $(domain)))
    end

    return DomainNode(:(push_type!(_ctx, $(QuoteNode(name)), $(domain); replace=true)))
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
        type = :(CombDiff.parametrize_type(_ctx[$(QuoteNode(base.args[1]))], $(map(parse_node, a.args[2:end])...)))
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
    if isa(bound, Symbol)
        params = Vector([bound])
    elseif bound.head == :call
        parametric_types = bound.args[1].args
        params = bound.args[2:end]
    elseif bound.head == :tuple
        params = bound.args
    else
        params = Vector{Expr}([bound])
    end

    body = f.args[2]
    result_map = :(CombDiff.pct_map($(map(p -> parse_node(Param, p), params)...), $(parse_node(body))))
    parametric_types === nothing && return result_map

    return :(CombDiff.parametric_map($(map(parse_node, parametric_types)...), $(result_map)))
end

function parse_anonymouse_function_type(n)
    parameter_expr = n.args[1]
    if isa(parameter_expr, Symbol)
        parameters = [parse_anonymous_type(parameter_expr)]
    else
        parameters = map(parse_anonymous_type, parameter_expr.args)
    end
    body = parse_anonymous_type(n.args[2])

    return :(CombDiff.MapType(VecType([$(parameters...)]), $(body)))
end

function parse_anonymouse_map_type(n)

    map_fields = Dict()

    supported_properties = [:symmetries, :linear, :off_diag]
    for a in n.args
        if a.args[1] == :type
            map_fields[:type] = parse_anonymous_type(a.args[2])
        elseif a.args[1] in supported_properties
            map_fields[a.args[1]] = parse_node(a.args[2])
        else
            error("field $(a.args[1]) not supported.")
        end
    end
    properties = [:($(QuoteNode(k)) => $(map_fields[k])) for k in supported_properties if haskey(map_fields, k)]
    dict = :(Dict($(properties...)))
    return :(CombDiff.MapType($(map_fields[:type]...), $(dict),))
end

function parse_anonymouse_product_type(n)
    prod_fields = map(parse_anonymous_type, first(n.args).args)

    return :(CombDiff.ProductType(:__anonymous, [$(prod_fields...)],
        [$([QuoteNode(Symbol("_$(i)")) for i in 1:length(prod_fields)]...)]))
end

function parse_named_type(n::Symbol)
    n in [:N, :C, :I, :R] && return :($n())
end

function parse_parametrized_type(n)
    :(CombDiff.parametrize_type($(parse_anonymous_type(n.args[1])), $(map(parse_node, n.args[2:end])...)))
end

function parse_anonymous_type(n)
    is_assignment(n) = isa(n, Expr) && n.head == :(=)
    is_product(n) = isa(n, Expr) && n.head == :parameters
    isa(n, Symbol) && return parse_named_type(n)
    n.head == :-> && return parse_anonymouse_function_type(n)
    n.head == :tuple && all(is_assignment, n.args) && return parse_anonymouse_map_type(n)
    n.head == :tuple && all(is_product, n.args) && return parse_anonymouse_product_type(n)
    n.head == :curly && return parse_parametrized_type(n)
    n.head == :block && return parse_anonymous_type(first(n.args))
end

function parse_node(::Type{Param}, p::Union{Expr,Symbol,Number})

    if isa(p, Number)
        return :(CombDiff.constant($(p)))
    end

    if isa(p, Symbol)
        return :(CombDiff.var($(QuoteNode(p)), UndeterminedPCTType()))
    end

    if p.head == :parameters
        return parse_anonymous_product_node(:(($p),))
    end
    if p.head == :tuple
        return parse_anonymous_product_node(p)
    end

    if p.head == Symbol("::")
        name, type = p.args


        type_params = []
        if isa(type, Symbol) || (isa(type, Expr) && type.head == :curly)
            if isa(type, Expr)
                type_params = type.args[2:end]
                type = type.args[1]
            end
            type = type in base_domains ? :($(type)()) : :(_ctx[$(QuoteNode(type))])
            type = :(CombDiff.parametrize_type($(type), $(map(parse_node, type_params)...)))
            isa(name, Symbol) && return :(CombDiff.var($(QuoteNode(name)), $(type)))

        else
            return :(CombDiff.var($(QuoteNode(name)), $(parse_anonymous_type(type))))
        end
    end
    if p.head == :call && p.args[1] == :∈
        param = p.args[2]
        domain = p.args[3]
        lower, upper = parse_node(domain.args[1]), parse_node(domain.args[2])
        if param.head == Symbol("::")
            name, type = param.args
            type = type in base_domains ? :($(type)()) : :(_ctx[$(QuoteNode(type))])
            return :(CombDiff.var($(QuoteNode(name)), (Domain($(type), $(lower), $(upper), Dict(:name => :_λ)))))
        end
        return :(CombDiff.var($(parse_node(param)), $(parse_node(domain))))
    end

end

function parse_node(p::Symbol)
    (p == :∞ || p == :infty) && return :(CombDiff.infty())
    :(CombDiff.var($(QuoteNode(p))))
end
function parse_node(p::QuoteNode)
    return parse_quantum_field_node(p)
    #= name = "__" * string(p.value)
    :(var(Symbol($(name)))) =#
end
function parse_quantum_field_node(n::QuoteNode)
    x = :(CombDiff.var(:x, $(C())))
    n.value == :II && return :($(pct_map)($x, fermi_scalar($x)))

    return :(CombDiff.annihilate($(QuoteNode(n.value))))
end

function parse_vac_exp_node(n::Expr)
    return :(CombDiff.make_node(VacExp, $(parse_node.(n.args[2:end])...)))
end

parse_node(i::Number) = :(CombDiff.constant($(i)))

function parse_parametric_call_node(n::Expr)
    param_func = n.args[1]
    func = parse_node(param_func.args[1])
    params = parse_node.(param_func.args[2:end])
    return :(CombDiff.call(CombDiff.parametric_var($(func), $(params...)), $(parse_node.(n.args[2:end])...)))
end

function parse_node(::Type{AbstractCall}, c::Expr)
    @assert c.head == :call
    func = c.args[1]

    return :(CombDiff.call($(parse_node(func)), $(parse_node.(c.args[2:end])...)))
end

function parse_add_node(a::Expr)
    @assert a.args[1] == :+
    return :(CombDiff.add($(parse_node.(a.args[2:end])...)))
end

function parse_negate_node(n::Expr)
    @assert n.args[1] == :-
    length(n.args) == 2 && return :(CombDiff.mul(constant(-1), $(parse_node(n.args[2]))))
    return :(CombDiff.add($(parse_node(n.args[2])), CombDiff.mul(constant(-1), $(parse_node(n.args[3])))))
end

function parse_mul_node(m::Expr)
    @assert m.args[1] == :*
    return :(CombDiff.mul($(parse_node.(m.args[2:end])...)))
end


function parse_monomial_node(m::Expr)
    @assert m.args[1] == :^
    return :(CombDiff.monomial($(parse_node.(m.args[2:end])...)))
end

function parse_contraction_node(::Type{T}, s::Expr) where {T<:Contraction}
    @assert s.args[1] in [:sum, :int, :∑, :∫]
    length(s.args) > 3 && error("summation: multiple indices must be in a tuple, and there can be only one summand.")
    if hasfield(typeof(s.args[2]), :head) && s.args[2].head == :tuple
        params = s.args[2].args
    else
        params = s.args[2:end-1]
    end

    param_nodes = (n -> parse_node(Param, n)).(params)
    constructor = T == Sum ? pct_sum : pct_int
    return :($(constructor)($(param_nodes...), $(parse_node(s.args[end]))))
end
function parse_fixed_node(n)
    return :(CombDiff.fixed_point($(parse_node(n.args[2]))))
end
function parse_fold_node(s::Expr)
    params = if hasfield(typeof(s.args[2]), :head) && s.args[2].head == :tuple
        s.args[2].args
    else
        s.args[2:end-1]
    end

    param_nodes = (n -> parse_node(Param, n)).(params)
    return :(CombDiff.pct_fold($(param_nodes...), $(parse_node(s.args[end]))))
end

function parse_prod_node(s::Expr)
    @assert s.args[1] in [:prod, :∏]
    if hasfield(typeof(s.args[2]), :head) && s.args[2].head == :tuple
        params = s.args[2].args
    else
        params = s.args[2:end-1]
    end

    param_nodes = (n -> parse_node(Param, n)).(params)
    return :(CombDiff.pct_product($(param_nodes...), $(parse_node(s.args[end]))))
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
            push!(bounds, :(CombDiff.pct_copy($(parse_node(a.args[1])))))
            push!(args, :($(parse_node(a.args[2]))))
        end
    end

    parse_subst!.(substitutions)
    content = parse_node(l.args[2])

    return :(CombDiff.pct_let(
        $(bounds...),
        $(args...),
        $(content),
    ))
end

function parse_pullback_node(p::Expr)
    @assert p.args[1] == :pullback || p.args[1] == :𝒫
    mapp = parse_node(p.args[2])
    p = isa(p.args[2], Symbol) ? PrimitivePullback : Pullback
    return :(CombDiff.make_node($(p), $(mapp)))
end


function parse_delta_node(::Type{T}, d::Expr) where {T<:AbstractDelta}
    @assert d.args[1] in [:delta, :delta_not, :δ]
    is_tuple(expr) = isa(expr, Expr) && expr.head == :tuple
    upper_params = is_tuple(d.args[2]) ? d.args[2].args : [d.args[2]]
    lower_params = is_tuple(d.args[3]) ? d.args[3].args : [d.args[3]]
    upper_nodes = map(parse_node, upper_params)
    lower_nodes = map(parse_node, lower_params)
    constructor = T == Delta ? :(CombDiff.delta) : :(CombDiff.delta_not)
    return :($(constructor)($(upper_nodes...), $(lower_nodes...), $(parse_node(d.args[4]))))
end

function parse_conjugate_node(c::Expr)
    return :(CombDiff.conjugate($(parse_node(c.args[1]))))
end

function parse_statement_node(n::Expr)
    if hasfield(typeof(n.args[1]), :head) && n.args[1].head == :call
        params = n.args[1].args[2:end]
        func = n.args[1].args[1]
        body = n.args[2]
        return MutatingStatement(parse_node(func), :(CombDiff.pct_map($(parse_node.(params)...), $(parse_node(body)))))
    else
        lhs = parse_node(n.args[1])
        rhs = parse_node(n.args[2])
        return n.head == :(=) ? Statement(lhs, rhs) : InLineStatement(lhs, rhs)
    end
end

function parse_block_node(n::Expr)
    parsed_body = parse_node.(n.args)
    i = findfirst(t -> isa(t, DomainNode) || isa(t, MapTypeNode), parsed_body)
    i === nothing || error("$(n.args[i]): types have to be global.")
    alias_indices = findall(t -> isa(t, AliasNode), parsed_body)
    rest_indices = findall(t -> !isa(t, AliasNode), parsed_body)
    isempty(alias_indices) || length(alias_indices) == maximum(alias_indices) || error("alias nodes must be at the begining of a block")
    alias_nodes = parsed_body[alias_indices]
    parsed_body = parsed_body[rest_indices]
    nodes = parsed_body[1:end-1]
    return_value = parsed_body[end]
    result = statement_to_let(nodes, return_value)
    pushes = [:(push_type!(_ctx, $(QuoteNode(get_alias(a))), $(get_aliased_type(a)))) for a in alias_nodes]
    pops = [:(pop_type!(_ctx, $(QuoteNode(get_alias(a))))) for a in alias_nodes]
    result = :(
        begin
            $(pushes...)
            __out = $(result)
            $(pops...)
            __out
        end
    )

end

function statement_to_let(statements::Vector, return_value::Union{Expr,Symbol})
    isempty(statements) && return return_value
    bound, args = lhs.(statements), rhs.(statements)
    #= bound = [:(CombDiff.pct_copy($(b))) for b in bound] =#
    return :(CombDiff.pct_let($(bound...), $(args...), $(return_value)))
end

function statement_to_mut(statements::Vector, return_value::Union{Expr,Symbol})
    isempty(statements) && return return_value
    bound, args = lhs.(statements), rhs.(statements)
    return :(CombDiff.mutate($(bound...), $(args...), $(return_value)))
end

function parse_group_index_node(n)
    parameters = map(parse_node, n.args[1].args)
    prod_type = parse_anonymous_product_node(n)
    return :(
        CombDiff.primitive_call(CombDiff.make_constructor($(prod_type)), $(parameters...))
    )
end

function parse_anonymous_product_node(n::Expr)
    parameters = map(parse_node, n.args[1].args)

    return :(
        let params = [$(parameters...)]
            CombDiff.ProductType(:__anonymous, CombDiff.get_type.(params), CombDiff.name.(params))
        end
    )

end

function parse_pctvector_node(n::Expr)
    return :(CombDiff.pct_vec($(map(parse_node, n.args)...)))
end

function parse_indicator_node(::Type{Indicator}, n::Expr)
    args = map(parse_node, n.args[2:end])

    return :(CombDiff.indicator($(args[2]), $(args[1]), $(args[end])))
end

function parse_domain_indicator_node(Indicator, n)
    i = parse_node(n.args[2])
    d = :(_ctx[$(QuoteNode(n.args[3]))])
    body = parse_node(n.args[end])

    return :(CombDiff.domain_indicator($(i), $(d), $(body)))
end

function convert_pct_type(::Type{T})::ElementType where {T<:Number}
    if T <: Unsigned
        return N()
    elseif T <: Integer
        return I()
    elseif T <: Real
        return R()
    else
        return C()
    end
end

function convert_pct_type(tensor::RangedTensor{S,T}) where {S<:Number,T}
    return MapType(VecType([Domain(N(), constant(l), constant(u)) for (l, u) in tensor.ranges]), convert_pct_type(S(0)))
end

#= eltype(::Type{<:AbstractArray{T}}) where {T} = T =#
function convert_pct_type(t::DataType)
    t.name.name == :Array || error("type $(t.name.name) is not supported.")
    T, D = t.parameters
    output_type = convert_pct_type(T)
    return MapType(VecType(fill(N(), D)), output_type)
end

function convert_pct_type(::T) where {T<:Union{Number,AbstractArray}}
    return convert_pct_type(T)
end


function convert_parametric_type(f)
    sig = methods(f)[1].sig
    _, arg_types... = sig.body.parameters

    complexified_types = []
    for t in arg_types
        t.name.name == :Array || error("type $(t.name.name) is not supported.")
        _, D = t.parameters
        push!(complexified_types, Array{ComplexF64,D})
    end

    arg_pct_types = map(convert_pct_type, complexified_types)
    return_type = Base.return_types(f, tuple(complexified_types...))[1]
    return_pct_type = convert_pct_type(return_type)

    return MapType(VecType(arg_pct_types), return_pct_type)

end

#= convert_pct_type(f::T) where {T<:Function} = MultiType(f) =#
convert_pct_type(f::Any) = MultiType(f)

to_julia_type(::N) = UInt
to_julia_type(::I) = Int
to_julia_type(::R) = Float64
to_julia_type(::C) = ComplexF64
to_julia_type(m::MultiType) = typeof(get_func_obj(m))

to_julia_type(d::AbstractDomain) = to_julia_type(base(d))

function to_julia_type(m::MapType)
    if all(t -> base(t) == N(), get_content_type(get_bound_type(m)))
        return Function
        #= error("cannot convert $(m)") =#
    end
    return Array{to_julia_type(get_body_type(m)),length(get_bound_type(m))}
end


function dedot(s::Symbol)
    contains(string(s), "__dot__") || return s
    mod, var = split(string(s), "__dot__")
    return Expr(Symbol("."), Symbol(mod), QuoteNode(Symbol(var)))
end

