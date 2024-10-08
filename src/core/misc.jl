export group

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


