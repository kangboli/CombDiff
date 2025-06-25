export codegen, remove_line_numbers

function find_dimensions(v::Var, summand::APN, existing_dims=[])
    for t in terms(summand)
        append!(existing_dims, find_dimensions(v, t))
    end
    return existing_dims
end

function find_dimensions(v::Var, c::PrimitiveCall, existing_dims=[])
    i = findfirst(t -> isa(t, Var) && get_body(t) == get_body(v), content(args(c)))
    if i !== nothing
        isa(mapp(c), AbstractCall) &&
            @warn "dimension inference failed for $(pretty(args(c)[i])): $(pretty(mapp(c))) may not have fixed dimensions
            the type of $(pretty(args(c)[i])) may need to be explicitly declared."
        push!(existing_dims, [:(1), :(size($(codegen(mapp(c))), $(i)))])
    end
    for t in terms(c)
        append!(existing_dims, find_dimensions(v, t))
    end
    return existing_dims
end

function find_dimensions(::Var, ::T) where {T<:Union{Var,Constant}}
    return []
end

function dimensions(b, summand)
    isa(get_type(b), ElementType) || return []

    if upper(get_type(b)) == infty() && (lower(get_type(b)) == constant(1) || lower(get_type(b)) == minfty())
        lu = find_dimensions(b, summand)
        isempty(lu) && return []
        return first(lu)
    else
        u, l = upper(get_type(b)), lower(get_type(b))
        return [codegen(l), codegen(u)]
    end
end

function codegen(n::Sum)
    summand = get_body(n)
    sizes = map(b -> dimensions(b, summand), content(get_bound(n)))
    loop = codegen(summand)
    sum_var_name = first(new_symbol(n))

    for (b, s) in zip(get_bound(n), sizes)
        loop = :(
            let $(sum_var_name) = 0
                @inbounds for $(codegen(b)) in $(first(s)):$(last(s))
                    $(sum_var_name) += $(loop)
                end
                $(sum_var_name)
            end
        )
    end
    return loop
end

function codegen(v::Var)
    (v == infty() || v == minfty()) && @warn("Infinity detected.")
    return get_body(v)
end

codegen(c::Constant) = get_body(c)

function codegen(a::Add)
    terms = content(get_body(a))
    :(+($(codegen.(terms)...)))
end

function codegen(m::Mul)

    negative_first = sort(content(get_body(m)), by=is_negative, rev=true)

    d = group(t -> isa(t, Monomial) && power(t) == constant(-1), negative_first)
    nominators = get(d, false, [constant(1)])
    denominators = map(base, get(d, true, []))

    isempty(denominators) && return :(*($(codegen.(nominators)...)))

    # if all(t -> base(get_type(t)) == I() || base(get_type(t)) == N(), denominators)
    #     return :(div($(codegen(mul(nominators...))), $(codegen(mul(denominators...)))))
    # else
    return :($(codegen(CombDiff.mul(nominators...))) / $(codegen(CombDiff.mul(denominators...))))
    # end
end

function codegen(i::IntDiv)
    return :(div($(codegen(get_nom(i))), $(codegen(get_denom(i)))))
end

function codegen(m::Map, memory_target=nothing)
    if length(get_bound(m)) == 1 && isa(get_body(m), Fold) && length(get_bound(get_body(m))) == 1

        fold = get_body(m)
        b = first(get_bound(m))
        b_fold = first(get_bound(fold))
        if name(upper(get_type(b_fold))) == name(b) && lower(get_type(b_fold)) == lower(get_type(b))
            return generate_accumulator(m)
        end
    end


    isempty(get_bound(m)) && return :(() -> $(codegen(get_body(m))))

    sizes = map(b -> dimensions(b, get_body(m)), content(get_bound(m)))
    if any(isempty, sizes) || any(b -> !tensorize(get_type(b)), content(get_bound(m)))
        return :(($(codegen.(get_bound(m))...),) -> (
            begin
                $(codegen(get_body(m)))
            end
        ))
    end
    offset_bounds = map(b -> first(simplify(add(subtract(b, lower(get_type(b))), constant(1)); settings=custom_settings(:expand_mul => true, :gcd => false, :logging => false))), get_bound(m))

    tensor_var_name = first(new_symbol(m))

    loop_lhs = any(s -> first(s) != 1, sizes) ? :(get_data($(tensor_var_name))) : :($(tensor_var_name))

    ranges = [Expr(:call, Symbol("=>"), l, r) for (l, r) in sizes]
    body_type = get_type(get_body(m))

    memory_target = if memory_target !== nothing
        codegen(memory_target)
    elseif any(s -> first(s) != 1, sizes)
        :(ranged_tensor($(codegen(get_type(get_body(m)))), $(ranges...)))
    elseif isa(body_type, ElementType)
        :(zeros($(codegen(body_type)), $(last.(sizes)...)))
    else
        :(Array{$(codegen(body_type)),$(length(sizes))}(undef, $(last.(sizes)...)))
    end

    loop = :($(loop_lhs)[$(codegen.(offset_bounds)...)] = $(codegen(get_body(m))))
    for (b, s) in zip(content(get_bound(m)), sizes)
        loop = :(
            @inbounds for $(codegen(b)) in $(first(s)):$(last(s))
            $(loop)
        end
        )
    end

    return :(
        let $(tensor_var_name) = $(memory_target)
            $(loop)
            $(tensor_var_name)
        end
    )
end

function equate_param_with_size(p, f_types::Vector{<:AbstractPCTType})
    for (i, t) in enumerate(f_types)
        for (j, s) in enumerate(get_bound_type(t))
            isa(t, MapType) || continue
            lower(s) == constant(1) || continue
            upper(s) == p || continue
            return (i, j)
        end
    end
    return (nothing, nothing)
end

function codegen(pm::ParametricMap)
    params = Expr(:tuple, codegen.(get_bound(pm))...)
    return :($(params) -> $(codegen(get_body(pm))))
end

codegen(d::Domain) = codegen(base(d))
codegen(::Union{N,I}) = :(Int)
codegen(::R) = :(Float64)
codegen(::C) = :(ComplexF64)
function codegen(t::MapType)
    if all(b -> isa(b, ElementType) && base(b) == N(), get_bound_type(t))
        :(Array{$(codegen(get_body_type(t))),$(length(get_bound_type(t)))})
    else
        error("$(pretty(t)) cannot be converted to an array type.")
    end
end


function codegen(c::Conjugate)
    :(conj($(codegen(get_body(c)))))
end

function codegen(c::PrimitiveCall)
    maptype = get_type(mapp(c))
    #= isa(maptype, ParametricMapType) && (maptype = get_param_body(maptype)) =#

    isa(maptype, MultiType) || length(get_bound_type(maptype)) == length(args(c)) ||
        error("$(pretty(mapp(c))) takes $(length(get_bound_type(maptype))) inputs, but $(length(args(c))) are given.")
    if all(t -> isa(get_type(t), ElementType) && (base(get_type(t)) == N() || base(get_type(t)) == I()), args(c))
        offsets = lower.(get_content_type(get_bound_type(get_type(mapp(c)))))
        new_args = map((t, o) -> first(simplify(add(subtract(t, o), constant(1)); settings=custom_settings(:expand_mul => true, :gcd => false, :logging => false))), content(args(c)), offsets)
        if all(x -> x == 1, get_body.(offsets))
            :($(codegen(mapp(c)))[$(codegen.(new_args)...)])
        else
            :(get_data($(codegen(mapp(c))))[$(codegen.(new_args)...)])
        end
    else
        :($(codegen(mapp(c)))($(codegen.(args(c))...)))
    end
end

function codegen(v::PCTVector)
    return :([$(codegen.(content(v))...)])
end

function codegen(m::Monomial)
    return :($(codegen(base(m)))^($(codegen(power(m)))))
end

function codegen(d::DeltaNot)
    return :(
        if $(codegen(upper(d))) == $(codegen(lower(d)))
            0
        else
            $(codegen(get_body(d)))
        end
    )
end

function codegen(d::Delta)
    return :(
        if $(codegen(upper(d))) == $(codegen(lower(d)))
            $(codegen(get_body(d)))
        else
            0
        end
    )
end

function codegen(n::Exp)
    return :(exp($(codegen(get_body(n)))))
end

function codegen(n::Log)
    return :(log($(codegen(get_body(n)))))
end

function codegen(n::BlasMul)
    :(*($(map(codegen, content(get_body(n)))...)))
end

function codegen(n::BlasTranspose)
    :(transpose($(codegen(get_body(n)))))
end

function codegen(n::MatrixInnerProd)
    l_matrix, r_matrix = content(get_body(n))
    :(dot(vec($(codegen(l_matrix))), vec($(codegen(r_matrix)))))
end

function codegen(n::BlasTrace)
    :(tr($(codegen(get_body(n)))))
end

function codegen(n::ScalarTensorProduct)
    return :($(codegen(n.scalar)) .* $(codegen(n.tensor)))
end

function codegen(n::BlasIndexing)
    :($(codegen(mapp(n)))[$(map(codegen, content(args(n)))...)])
end

codegen(n::Copy) = codegen(get_body(n))


function codegen(n::Mutate)
    length(get_bound(n)) > 1 && error("multiple mutation is not yet supported.")
    target = first(get_bound(n))
    src = first(args(n))
    return :(
        $(codegen(src, target))
    )
end

function codegen(n::Let)
    assignments = [:($(codegen(b)) = $(codegen(a))) for (b, a) in zip(get_bound(n), args(n))]
    return :(
        begin
            $(assignments...)
            $(codegen(get_body(n)))
        end
    )
end


function codegen(n::Indicator)
    :(
        if $(codegen(lower(n))) <= $(codegen(upper(n)))
            $(codegen(get_body(n)))
        else
            0
        end
    )
end

function codegen(n::Fold)
    b = first(get_bound(n))

    body = get_body(n)
    inputs = get_bound(body)
    if length(inputs) > 0
        assignment = :($(codegen.(inputs)...) = $(codegen(body))($(codegen.(inputs)...)))
    else
        assignment = :($(codegen(body))($(codegen.(inputs)...)))
    end

    return :(
        ($(codegen.(inputs)...),) -> begin
            for $(codegen(b)) in $(codegen(lower(get_type(b)))):$(codegen(upper(get_type(b))))
                $(assignment)
            end
            $(codegen.(inputs)...)
        end
    )
end

function generate_accumulator(m::Map)
    @assert length(get_bound(m)) == 1
    @assert length(get_bound(get_body(m))) == 1
    @assert isa(get_body(m), Fold)

    tensor_var_name = first(new_symbol(m))
    b = first(get_bound(m))

    fold = get_body(m)
    fold_b = first(get_bound(fold))
    func = get_body(fold)

    inputs = get_bound(func)
    length(inputs) != 1 && error("Multiple return in accumulator not yet supported")
    input = first(inputs)



    range = (codegen(lower(get_type(b))), codegen(upper(get_type(b))))
    if lower(get_type(b)) != constant(1)
        memory_target = :(ranged_tensor($(codegen(get_type(get_body(m)))), $(first(range)):$(last(range))))
    elseif isa(get_type(input), ElementType)
        memory_target = :(zeros($(codegen(get_type(input))), $(last(range))))
    else
        memory_target = :(Array{$(codegen(get_type(input))),1}(undef, $(last(range))))
    end

    return :(
        ($(codegen(input)),) -> begin
            let $(tensor_var_name) = $(memory_target)
                for $(codegen(fold_b)) in $(first(range)):$(last(range))
                    $(codegen(input)) = $(codegen(func))($(codegen(input)))
                    $(tensor_var_name)[$(codegen(fold_b))] = $(codegen(input))
                end
                tensor_var_name
            end
        end
    )
end

function codegen(n::PrimitivePullback)
    return :(CombDiff.find_pullback(Val($(codegen(get_body(n))))))
end

find_pullback(n) = error("pullback $(n) not found")

function codegen(c::Constructor)
    product_type = get_body_type(get_type(c))
    fields = get_names(product_type)
    field_types = get_content_type(get_bound_type(get_type(c)))
    args = Expr(:tuple,
        [Expr(:(::), f, codegen(t)) for (f, t) in zip(fields, field_types)]...)
    return_value = Expr(:tuple, [Expr(:(=), f, f) for f in fields]...,
        Expr(:(=), :__type_name, QuoteNode(get_typename(product_type))),
    )

    :($args -> $return_value)
end


remove_line_numbers(e::Any) = e
function remove_line_numbers(expr::Expr)
    #= expr.args = filter(a -> !isa(a, LineNumberNode), expr.args)
    expr.args = map(purge_line_numbers, expr.args) =#
    if expr.head == :macrocall
        return expr
    end
    @set expr.args = [remove_line_numbers(a) for a in expr.args if !isa(a, LineNumberNode)]
end

