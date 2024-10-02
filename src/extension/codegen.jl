export codegen

function find_dimensions(v::Var, summand::APN, existing_dims=[])
    for t in terms(summand)
        append!(existing_dims, find_dimensions(v, t))
    end
    return existing_dims
end

function find_dimensions(v::Var, c::PrimitiveCall, existing_dims=[])
    i = findfirst(t -> get_body(t) == get_body(v), content(args(c)))
    i !== nothing && push!(existing_dims, :(size($(codegen(mapp(c))), $(i))))
    for t in terms(c)
        append!(existing_dims, find_dimensions(v, t))
    end
    return existing_dims
end

function find_dimensions(::Var, ::T) where {T<:Union{Var,Constant}}
    return []
end

function codegen(n::Sum)
    summand = get_body(n)
    sizes = map(b -> first(find_dimensions(b, summand)), content(get_bound(n)))
    loop = codegen(summand)

    for (b, s) in zip(get_bound(n), sizes)
        loop = :(
            let _sum = 0
                @inbounds for $(codegen(b)) in 1:$(s)
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

function codegen(a::Mul)
    terms = content(get_body(a))
    :(*($(codegen.(terms)...)))
end

function codegen(m::Map)
    sizes = map(b -> find_dimensions(b, get_body(m)), content(get_bound(m)))
    if any(isempty, sizes) || any(b -> !tensorize(get_type(b)), content(get_bound(m)))
        return :(($(codegen.(get_bound(m))...),) -> (
            begin
                $(codegen(get_body(m)))
            end
        ))
    else
        loop = :(_t[$(codegen.(get_bound(m))...)] = $(codegen(get_body(m))))
        @inbounds for (b, s) in zip(content(get_bound(m)), first.(sizes))
            loop = :(
                for $(codegen(b)) in 1:$(s)
                    $(loop)
                end
            )
        end
        return :(
            let _t = zeros($(first.(sizes)...))
                $(loop)
                _t
            end
        )
    end

end

function codegen(c::Conjugate)
    :(conj($(codegen(get_body(c)))))
end

function codegen(c::PrimitiveCall)
    if all(t -> base(get_type(t)) == N() || base(get_type(t)) == I(), args(c))
        :($(codegen(mapp(c)))[$(codegen.(args(c))...)])
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
        if $(codege(upper(d))) == $(codegen(lower(d)))
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

