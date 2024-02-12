export blaserize

abstract type BlasNode <: APN end

struct BlasMul <: BlasNode
    type::AbstractPCTType
    body::PCTVector
end

function blas_mul(terms::Vararg)
    return make_node(BlasMul, pct_vec(terms...))
end

function partial_inference(::Type{BlasMul}, terms::PCTVector)
    terms = content(terms)
    x, y = first(terms), last(terms)
    x_bound_types = get_content_type(get_bound_type(get_type(x)))
    y_bound_types = get_content_type(get_bound_type(get_type(y)))
    body_type = escalate(map(get_bound_type, map(get_type, terms))...)
    if length(x_bound_types) == length(y_bound_types) == 1
        return body_type
    elseif length(x_bound_types) == 1 && length(y_bound_types) == 2
        primal_type = MapType(VecType([last(y_bound_types)]), body_type)
        return MapType(VecType([primal_type]), body_type)
    elseif length(x_bound_types) == 2 && length(y_bound_types) == 1
        return MapType(VecType([first(x_bound_types)]), body_type)
    else
        return MapType(VecType([first(x_bound_types), last(y_bound_types)]), body_type)
    end
end

function is_dual_vector(n::BlasMul)
    return isa(first(get_content_type(get_bound_type(get_type(n)))), MapType)
end
is_dual_vector(n::APN) = false

function pretty(n::BlasMul)
    join(map(pretty, content(get_body(n))), "⋅")
end

struct BlasTranspose <: BlasNode
    type::AbstractPCTType
    body::APN
end

function blas_transpose(body)
    return make_node(BlasTranspose, body)
end

blas_transpose(body::BlasTranspose) = get_body(body)
function e_class_reduction(::Type{BlasTranspose}, body::T) where T <: APN
    if T == BlasTranspose 
        body = get_body(body)
        println(pretty(body))
        return typeof(body), terms(body), get_type(body)
    end
    
    return BlasTranspose, [body], partial_inference(BlasTranspose, body) 
end

function blas_transpose(body::BlasMul)
    return blas_mul(map(blas_transpose, content(get_body(body)))...)
end

function partial_inference(::Type{BlasTranspose}, body)
    bound_types = get_content_type(get_bound_type(get_type(body)))
    if length(bound_types) == 1
        if isa(first(bound_types), MapType)
            return MapType(get_bound_type(first(bound_types)), get_body_type(get_type(body)))
        else
            primal_type = MapType(VecType([first(bound_types)]), get_type(body))
            return MapType(VecType([primal_type]), get_type(body))
        end
    end
    return MapType(VecType(reverse(bound_types)), get_body_type(get_type(body)))
end

function pretty(n::BlasTranspose)
    body = get_body(n)
    isa(body, Conjugate) && return "$(pretty(get_body(body)))⁺"
    return "$(pretty(body))ᵀ"
end

struct BlasIndexing <: AbstractCall
    type::AbstractPCTType
    mapp::APN
    args::PCTVector
end

call(mapp::APN, args::Vararg) = make_node(BlasIndexing, mapp, make_node(PCTVector, args...))
pretty(c::BlasIndexing) = "($(pretty(c.mapp)))($(join(map(pretty, content(args(c))), ", ")))"

function sub_blaserize_neighbors(n::APN)
    result = NeighborList()
    sub_terms = content(n)
    for (i, t) in enumerate(sub_terms)
        neighbor_list = blaserize_neighbors(t)
        for (h, d, s) in zip(nodes(neighbor_list), directed(neighbor_list), names(neighbor_list))
            push!(result, set_content(n, set_at(sub_terms, i, h)...); dired=d, name=s)
        end
    end
    return result
end

blaserize_neighbors(n::APN) = sub_blaserize_neighbors(n)
blaserize_neighbors(::TerminalNode) = NeighborList()

function as_blas_mul(s::Var, t_1, t_2)
    if length(args(t_1)) == length(args(t_2)) == 1
        t_1, t_2 = sort([t_1, t_2], by=t -> is_dual_vector(mapp(t)), rev=true)
        left = is_dual_vector(mapp(t_1)) ? mapp(t_1) : blas_transpose(mapp(t_1))
        return blas_mul(left, mapp(t_2))
    elseif length(args(t_1)) == 1 && length(args(t_2)) == 2
        i = findfirst(t -> t == s, content(args(t_2)))
        if i == 1
            return call(blas_mul(blas_transpose(mapp(t_1)), mapp(t_2)), last(content(args(t_2))))
        end
        if i == 2
            return call(blas_mul(mapp(t_2), mapp(t_1)), first(content(args(t_2))))
        end
    elseif length(args(t_1)) == length(args(t_2)) == 2
        # matrix matrix
        i = findfirst(t -> t == s, content(args(t_1)))
        j = findfirst(t -> t == s, content(args(t_2)))
        if i == j == 1
            return call(blas_mul(blas_transpose(mapp(t_1)), mapp(t_2)),
                last(content(args(t_1))), last(content(args(t_2))))
        elseif i == j == 2
            return call(blas_mul(mapp(t_1), blas_transpose(mapp(t_2))),
                first(content(args(t_1))), first(content(args(t_2))))
        elseif i == 1 && j == 2
            return call(blas_mul(mapp(t_2), mapp(t_1)),
                first(content(args(t_2))), last(content(args(t_1))))
        else
            return call(blas_mul(mapp(t_1), mapp(t_2)),
                first(content(args(t_1))), last(content(args(t_2))))
        end
    else
        return pct_sum(s, t_1, t_2)
    end
end

struct MatrixInnerProd <: BlasNode
    type::AbstractPCTType
    body::PCTVector
end

function matrix_inner_prod(body::Vararg)
    return make_node(MatrixInnerProd, pct_vec(body...))
end

function partial_inference(::Type{MatrixInnerProd}, body)
    return escalate(map(b -> get_body_type(get_type(b)), content(body))...)
end

function pretty(n::MatrixInnerProd)
    matrices = content(get_body(n))
    return "⟨$(pretty(first(matrices))), $(pretty(last(matrices)))⟩"
end

struct BlasTrace <: BlasNode
    type::AbstractPCTType
    body::APN
end

function blas_trace(body::APN)
    return make_node(BlasTrace, body)
end

function blas_trace(body::BlasMul)
    factors = content(get_body(body))
    if length(factors) == 2
        return matrix_inner_prod(blas_transpose(conjugate(first(factors))), last(factors))
    end
    return invoke(blas_trace, Tuple{APN}, body)
end

function partial_inference(::Type{BlasTrace}, body)
    return get_body_type(get_type(body))
end

pretty(n::BlasTrace) = "tr($(pretty(get_body(n))))"

function index_info(b::Var, c::AbstractCall)
    indices = filter(t -> tensorize(get_type(t)), content(args(c)))
    return findall(t -> t == b, indices), length(indices)
end

function blaserize_neighbors(s::Sum)
    result = NeighborList()
    bounds, body = get_bound(s), get_body(s)
    terms = isa(body, Mul) ? content(get_body(body)) : [body]
    append!(result, sub_blaserize_neighbors(s))
    all(t -> isa(t, AbstractCall), terms) || return result
    for (i, b) in enumerate(content(bounds))
        infos = map(t -> index_info(b, t), terms)
        indices = findall(info -> !isempty(first(info)), infos)
        any(i -> last(infos[i]) > 2, indices) && continue
        skip_loop = false
        for i in indices
            if any(x -> !tensorize(get_type(x)), content(args(terms[i])))
                skip_loop = true
            end
        end
        skip_loop && continue
        remaining_bound = content(bounds)[1:end.!=i]

        if length(indices) == 1
            i = first(indices)
            content(args(terms[i])) == [b, b] || continue
            trace_term = blas_trace(mapp(terms[i]))
            remaining_terms = terms[1:end.!=first(indices)]
            push!(result, pct_sum(remaining_bound..., mul(remaining_terms..., trace_term)); dired=true, name="matrix trace")
        elseif length(indices) == 2
            i, j = indices
            length(first(infos[i])) == length(first(infos[j])) == 1 || continue
            t_1, t_2 = sort([terms[i], terms[j]], by=t -> length(args(t)))
            product = as_blas_mul(b, t_1, t_2)
            remaining_terms = terms[1:end.!=i.&&1:end.!=j]
            push!(result, pct_sum(remaining_bound..., mul(remaining_terms..., product)); dired=true, name="blas mul")
        end
    end
    return result
end

function conjugate_call_neighbors(c::Conjugate)
    result = NeighborList()
    isa(get_body(c), AbstractCall) || return result
    push!(result, call(conjugate(mapp(get_body(c))), content(args(get_body(c)))...);
        dired=true, name="conjugate call")
    return result
end

function conjugate_blas_mul_neighbors(c::Conjugate)
    result = NeighborList()
    mul = get_body(c)
    isa(mul, BlasMul) || return result
    push!(result, blas_mul(map(conjugate, content(get_body(mul)))...); dired=true, name="conjugate blas mul")
    return result
end

function conjugate_transpose_neighbors(c::Conjugate)
    result = NeighborList()
    trans = get_body(c)
    isa(trans, BlasTranspose) || return result
    push!(result, blas_transpose(conjugate(get_body(trans))); dired=true, name="conjugate transpose")
    return result
end

function blaserize_neighbors(c::Conjugate)
    result = NeighborList()
    append!(result, conjugate_call_neighbors(c))
    append!(result, conjugate_blas_mul_neighbors(c))
    append!(result, conjugate_transpose_neighbors(c))
    append!(result, sub_blaserize_neighbors(c))
    return result
end

function tensor_addition_neighbors(a::Add)
    result = NeighborList()
    addants = content(get_body(a))
    all(t -> isa(t, AbstractCall), addants) || return result
    reduce(isequal, map(args, addants)) || return result
    common_args = args(first(addants))
    new_node = call(add(map(mapp, addants)...), content(common_args)...)
    push!(result, new_node; dired=true, name="tensor addition")
    return result
end

function blaserize_neighbors(a::Add)
    result = NeighborList()
    append!(result, tensor_addition_neighbors(a))
    append!(result, sub_blaserize_neighbors(a))
    return result
end

function map_cancel_neighbors(m::Map)
    result = NeighborList()
    isa(get_body(m), AbstractCall) || return result
    args(get_body(m)) == get_bound(m) || return result
    push!(result, mapp(get_body(m)); dired=true, name="map cancel")
end

function blaserize_neighbors(m::Map)
    result = NeighborList()
    append!(result, map_cancel_neighbors(m))
    append!(result, sub_blaserize_neighbors(m))
    return result
end

struct ScalarTensorProduct <: BlasNode
    type::AbstractPCTType
    scalar::APN
    tensor::APN
end

content_fields(::Type{ScalarTensorProduct}) = [:scalar, :tensor]

function scalar_tensor_product(scalar, tensor)
    return make_node(ScalarTensorProduct, scalar, tensor)
end

function partial_inference(::Type{ScalarTensorProduct}, scalar, tensor)
    return get_type(tensor)
end

function pretty(n::ScalarTensorProduct)
    return "$(pretty(n.scalar))⋅$(pretty(n.tensor))"
end

function scalar_tensor_product_neighbors(m::Mul)
    result = NeighborList()
    productant = content(get_body(m))
    d = group(t -> isa(t, AbstractCall), productant)
    scalars = get(d, false, [])
    isempty(scalars) || return result
    tensors = get(d, true, [])
    length(tensors) == 1 || return result
    new_term = call(scalar_tensor_product(mul(scalars...), mapp(first(tensors))),
        content(args(first(tensors)))...)

    push!(result, new_term; dired=true, name="scalar tensor product")
    return result
end

function blaserize_neighbors(m::Mul)
    result = NeighborList()
    append!(result, scalar_tensor_product_neighbors(m))
    append!(result, sub_blaserize_neighbors(m))
    return result
end

function blaserize(n::APN)
    return simplify(n; settings=blaserize_settings)
end
