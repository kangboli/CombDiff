export codegen

function find_dimensions(v::Var, summand::APN, existing_dims=[])
    for t in terms(summand)
        append!(existing_dims, find_dimensions(v, t))
    end
    return existing_dims
end

function find_dimensions(v::Var, c::PrimitiveCall, existing_dims=[])
    i = findfirst(t -> isa(t, Var) && get_body(t) == get_body(v), content(args(c)))
    i !== nothing && push!(existing_dims, [:(1), :(size($(codegen(mapp(c))), $(i)))])
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

    for (b, s) in zip(get_bound(n), sizes)
        loop = :(
            let _sum = 0
                @inbounds for $(codegen(b)) in $(first(s)):$(last(s))
                    _sum += $(loop)
                end
                _sum
            end
        )
    end
    return loop
end

codegen(v::Var) = get_body(v)

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
    return :($(codegen(mul(nominators...))) / $(codegen(mul(denominators...))))
    # end
end

function codegen(i::IntDiv)
    return :(div($(codegen(get_nom(i))), $(codegen(get_denom(i)))))
end

function codegen(m::Map)

    if isempty(get_bound(m))
        return :(() -> $(codegen(get_body(m))))
    end

    sizes = map(b -> dimensions(b, get_body(m)), content(get_bound(m)))
    if any(isempty, sizes) || any(b -> !tensorize(get_type(b)), content(get_bound(m)))
        return :(($(codegen.(get_bound(m))...),) -> (
            begin
                $(codegen(get_body(m)))
            end
        ))
    else
        offset_bounds = map(b->first(simplify(add(subtract(b, lower(get_type(b))), constant(1)); settings=custom_settings(:expand_mul=>true, :gcd=>false, :logging=>false))), get_bound(m))
        loop = :(get_data(_t)[$(codegen.(offset_bounds)...)] = $(codegen(get_body(m))))
        @inbounds for (b, s) in zip(content(get_bound(m)), sizes)
            loop = :(
                for $(codegen(b)) in $(first(s)):$(last(s))
                    $(loop)
                end
            )
        end

        ranges = [Expr(:call, Symbol("=>"), l, r) for (l, r) in sizes]

        return :(
            let _t = ranged_tensor($(codegen(get_type(get_body(m)))), $(ranges...))
                $(loop)
                _t
            end
        )
    end
end

codegen(d::Domain) = codegen(base(d))   
codegen(d::Union{N, I}) = :(Int)
codegen(d::R) = :(Float64)
codegen(d::C) = :(ComplexF64)


function codegen(c::Conjugate)
    :(conj($(codegen(get_body(c)))))
end

function codegen(c::PrimitiveCall)
    if all(t -> base(get_type(t)) == N() || base(get_type(t)) == I(), args(c))
        offsets = lower.(get_content_type(get_bound_type(get_type(mapp(c)))))
        new_args = map((t, o)->first(simplify(add(subtract(t, o), constant(1)); settings=custom_settings(:expand_mul=>true, :gcd=>false, :logging=>false) )), content(args(c)), offsets)
        :(get_data($(codegen(mapp(c))))[$(codegen.(new_args)...)])
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


function codegen(n::Let)
    assignments = [:($(codegen(b)) = $(codegen(a))) for (b, a) in zip(get_bound(n), args(n))]
    return :(
        let $(assignments...)
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
#= function Base.getindex(t::RangedTensor, indices::Vararg{Int})
    return t.data[(1 .+ collect(indices) - first.(t.ranges))...]
end


function Base.setindex!(t::RangedTensor, new_data::Number, indices::Vararg{Int})
    return t.data[(1 .+ collect(indices) - first.(t.ranges))...] = new_data
end
 =#
