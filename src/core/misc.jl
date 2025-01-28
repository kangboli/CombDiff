export group, ranged_tensor, RangedTensor, get_data

function group(f::Function, vec::AbstractVector{T}) where T
    d = Dict{Bool, Vector{T}}()
    for v in vec
        predicate = f(v)
        d[predicate] = push!(get(d, predicate, Vector{T}()), v)
    end
    return d
end

function tee(f::Function, vec::AbstractVector{T}) where T
    d = group(f::Function, vec::AbstractVector{T})
    
    return get(d, true, Vector{T}()), get(d, false, Vector{T}())
end



struct RangedTensor{T, S} 
    data::Array{T, S} 
    ranges::Vector{Pair{Int, Int}}
end

get_data(n::Array) = n
get_data(n::RangedTensor) = n.data

function ranged_tensor(::Type{T}, ranges::Vararg) where T <: Number
    ranges = [l=>r for (l, r) in ranges]
    dims = [1 + r - l for (l, r) in ranges]
    data = zeros(T, dims...)
    all(r->first(r)==1, ranges) && return data
    return RangedTensor{T, length(dims)}(data, ranges)
end

function ranged_tensor(::Type{T}, ranges::Vararg) where T <: AbstractArray
    ranges = [l=>r for (l, r) in ranges]
    dims = [1 + r - l for (l, r) in ranges]
    data = Array{T, length(dims)}(undef, dims...)
    all(r->first(r)==1, ranges) && return data
    return RangedTensor{T, length(dims)}(data, ranges)
end

function Base.:+(t_1::RangedTensor, t_2::RangedTensor)
    @assert t_1.ranges == t_2.ranges
    return RangedTensor(t_1.data + t_2.data, t_1.ranges)
end
