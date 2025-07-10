export to_cbi, gen_range

struct CBI <: AbstractMap
    type::AbstractPCTType
    bound::PCTVector
    body::APN
end


function type_length(t::ElementType)
    return add(constant(1), subtract(upper(t), lower(t)))
end

function type_length(t::ProductType)
    #= return pct_vec(map(type_length, get_content_type(t))...) =#
    return mul(map(type_length, get_content_type(t))...)
end

#= function call_by_indexing(bound::PCTVector, body::APN)
    return make_node(CBI, bound, body)
end =#

function call_by_indexing(body::Map)
    bounds = get_bound(body)
    new_bound_types = map(l -> parametrize_type(N(), l), type_length.(get_type.(bounds)))
    new_bounds = map((b, t) -> set_type(b, t), bounds, new_bound_types)

    indexings = map((b, t) -> pct_indexing(b, t), new_bounds, get_type(bounds))

    result = make_node(CBI, pct_vec(new_bounds...), ecall(body, indexings...), type=get_type(body))
    return result
end

function pretty(m::CBI)
    params = map(v -> "$(pretty(v))", content(get_bound(m)))
    "[($(join(params, ", "))) -> $(pretty(get_body(m)))]"
end

function verbose(m::CBI)
    params = map(v -> "$(verbose(v))", content(get_bound(m)))
    "[($(join(params, ", "))) -> $(verbose(get_body(m)))]::$(verbose(get_type(m)))"
end

"""
Given an linear index, return an element in the set.
"""
struct Indexing <: APN
    type::AbstractPCTType
    body::APN
end

function pct_indexing(i::APN, type::AbstractPCTType)
    # indexing{N{1:M}}(i) = i
    #= base(type) == N() && return subtract(add(i, lower(type)), constant(1)) =#
    return make_node(Indexing, i, type=type)
end

print_colors_defaults[:indexing] = Crayon(foreground=(200, 100, 130))

function pretty(i::Indexing)
    type_str = isa(get_type(i), ProductType) ? string(get_typename(get_type(i))) : pretty(get_type(i))
    if type_str == "__anonymous"
        print_colors_defaults[:indexing]("|$(pretty(get_body(i)))|")
    else
        print_colors_defaults[:indexing]("($type_str)($(pretty(get_body(i)))))")
    end
end

"""
Given a element in a set, return the linear index in the set.

The linear index is from 1 to number of elements in the set.
"""
struct Serialize <: APN
    type::AbstractPCTType
    body::APN
end

function serialize(body::APN, type=parametrize_type(N(), type_length(get_type(body))))
    result = make_node(Serialize, body, type=type)
    return result
end

pretty(s::Serialize) = "serial($(pretty(get_body(s))))"


"""
serial((;a, b))
->
serial(a) + (serial(b)-1) * M
"""
function serialize_product(s::Serialize)
    result = NeighborList()
    p = get_body(s)
    isa(get_type(p), ProductType) || return result
    isa(p, AbstractCall) || return result

    indices = args(p)

    dims = [constant(1), accumulate(mul, (t -> mul(v_wrap(type_length(t))...)).(get_content_type(get_type(indices))))...]

    new_s = add(map((prefactor, c, a) -> mul(prefactor, subtract(strip_indexing(c, a), constant(1))), dims,
            map(t -> parametrize_type(N(), type_length(t)), get_content_type(get_type(p))),
            indices)..., constant(1))
    push!(result, new_s; dired=true, name="serialize_product")
    return result
end

"""
serial(index((;a, b))) = (;a, b)
"""
function serialization_canceling(s::Serialize)
    result = NeighborList()
    isa(get_body(s), Indexing) || return result
    serial = get_body(get_body(s))
    @assert get_type(s) == get_type(serial)
    push!(result, get_body(get_body(s)); dired=true, name="serialization_canceling")
    return result
end

#= """
serial(N{A, B}, i) = i - A + 1
"""
function serialize_domain(s::Serialize)
    result = NeighborList()
    body = get_body(s)
    isa(get_type(body), Domain) || return result
    push!(result, subtract(add(body, lower(get_type(body))), constant(1)); dired=true, name="serialize_domain")
    return result
end =#

function neighbors(s::Serialize; _...)
    result = NeighborList()
    append!(result, serialization_canceling(s))
    append!(result, serialize_product(s))
    #= append!(result, serialize_domain(s)) =#
    return result
end

struct GetData <: AbstractMap
    type::AbstractPCTType
    body::APN
end

function call(mapp::Union{GetData,Dot}, args::Vararg)
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end

function get_data(body::APN)
    make_node(GetData, body)
end


function partial_inference(::Type{GetData}, body)
    body_type = get_type(body)

    function inference_maptype(body_type)
        bound_types = get_bound_type(body_type)
        new_bound_types = map(l -> parametrize_type(N(), l), type_length.(bound_types))
        return MapType(VecType(new_bound_types), get_body_type(get_type(body)))
    end

    return inference_maptype(body_type)
end

pretty(g::GetData) = "get_data($(pretty(get_body(g))))"

partial_inference(::Type{T}, body...) where {T<:Union{CBI,Indexing,Serialize}} = UndeterminedPCTType()


cbi_applicable(t::AbstractPCTType) = false

function cbi_applicable(t::MapType)
    isempty(get_bound_type(t)) && return false
    all(is_cbi_type, get_bound_type(t))
end

is_cbi_type(t::AbstractPCTType) = false
is_cbi_type(::N) = true

is_cbi_type(t::ProductType) = all(is_cbi_type, get_content_type(t))

function is_cbi_type(t::Domain)
    base(t) == N() && return true
    base(t) == I() || return false
    l = type_length(t)
    l == infty() && return false
    l == minfty() && return false
    return true
end

is_basic_tensor(t::MapType) = all(is_basic_type, get_content_type(t))
is_basic_type(t::AbstractPCTType) = false
is_basic_type(::N) = true
is_basic_type(t::Domain) = base(t) == N() && lower(t) == constant(1)

function map_cbi(m::Map; settings=default_settings())
    result = NeighborList()
    settings[:cbi] || return result
    cbi_applicable(get_type(m)) || return result
    push!(result, call_by_indexing(m); dired=true, name="map_cbi")
    return result
end

push!(neighbor_registry[Map],  map_cbi)


function to_cbi(n::APN)
    simplify(n; settings=custom_settings(:cbi => true))
end


# This is likely unnecessary abstraction. TODO: remove this.
strip_indexing(::AbstractPCTType, i::Indexing) = get_body(i)
strip_indexing(t::AbstractPCTType, i::APN) = serialize(i, t)

"""
t(a, b) 
->
get_data(t)(serial(a), serial(b))
"""
function call_get_data(c::AbstractCall)
    result = NeighborList()
    m = mapp(c)
    isa(m, Var) || return result
    cbi_applicable(get_type(m)) || return result
    all(is_basic_type, get_bound_type(get_type(m))) && return result
    data = get_data(m)

    push!(result, call(data, map(strip_indexing,
            map(t -> parametrize_type(N(), type_length(t)), get_bound_type(get_type(data))),
            args(c))...); dired=true, name="get_data")
    return result
end

push!(neighbor_registry[AbstractCall], :cbi => call_get_data)

"""
sum(((;a, b))->t((;a, b)))
->
sum((p::N{1,M*M}) -> t((;index(p).a, index(p).b)) )
"""
function sum_cbi(s::Sum)
    result = NeighborList()

    bounds = get_bound(s)
    m = pct_map(bounds..., get_body(s))
    cbi_applicable(get_type(m)) || return result
    all(is_basic_type, get_type.(bounds)) && return result

    new_bound_types = map(l -> parametrize_type(N(), l), type_length.(get_type.(bounds)))
    new_bounds = map((b, t) -> set_type(b, t), bounds, new_bound_types)
    indexings = map((b, t) -> pct_indexing(b, t), new_bounds, get_type(bounds))
    new_sum = make_node(Sum, pct_vec(new_bounds...), ecall(m, indexings...))

    push!(result, new_sum; dired=true, name="sum_cbi")
    return result
end

push!(neighbor_registry[Sum], :cbi=>sum_cbi)

"""
Given a linear index, find the fields of the corresponding struct.

index(p).a -> div(rem(p, M*M), M)
index(p).b -> div(rem(p, M), 1)
"""
function indexing_get_field_neighbor(c::AbstractCall)
    result = NeighborList()
    isa(mapp(c), Indexing) || return result

    length(args(c)) == 1 || return result
    field = first(args(c))
    i = get_body(field)

    type, index = get_type(mapp(c)), get_body(mapp(c))
    dim = [constant(1), accumulate(mul, type_length.(get_content_type(type)))...]
    offset = subtract(lower(get_content_type(type)[i]), constant(1))
    new_index = add(call(var(:div, MultiType(div)), call(var(:rem, MultiType(rem)), index, dim[i+1]), dim[i]), offset)
    push!(result, new_index; dired=true, name="index_get_field")
    return result
end

push!(neighbor_registry[AbstractCall], :cbi => indexing_get_field_neighbor)


function codegen(c::CBI)
    ranges = map(t -> :($(codegen(lower(t))) => $(codegen(upper(t)))), get_bound_type(get_type(c)))

    sizes = type_length.(get_type(get_bound(c)))

    body = get_body(c)

    tensor_var_name = first(new_symbol(c))
    memory_target = :(zeros($(codegen(get_type(body))), $(codegen.(sizes)...)))

    loop = :(@inbounds $(tensor_var_name)[$(codegen.(get_bound(c))...)] = $(codegen(get_body(c))))


    for (b, s) in zip(get_bound(c), sizes)
        loop = :(
            for $(codegen(b)) in 1:$(codegen(s))
                $(loop)
            end
        )
    end

    return :(
        let $(tensor_var_name) = $(memory_target)
            $(loop)
            CombDiff.cbi_tensor([$(ranges...)], $(tensor_var_name))
        end
    )
end

function gen_range(t::Domain)
    return :($(codegen(lower(t))) => $(codegen(upper(t))))
end

function gen_range(t::ProductType)

    entries = map((n, r) -> :($(n) = $(r)), get_names(t),
        map(gen_range, get_content_type(t)))

    return :(
        typename=$(QuoteNode(get_typename(t))),
        $(entries...)
    )
end

function codegen(g::GetData)
    return :(get_data($(codegen(get_body(g)))))
end

struct CBITensor
    ranges::Vector
    tensor::Array
end

get_data(t::CBITensor) = t.tensor
cbi_tensor(ranges, tensor) = CBITensor(ranges, tensor)

function codegen(i::Indexing)
    return :(CombDiff.construct_from_index($(gen_range(get_type(i))), $(codegen(get_body(i)))))
end

function construct_from_index((l, u), i::Int)
    return i + l
end

function find_dimensions(::Var, ::T) where {T<:Dot}
    return []
end

function contains_name(d::Dot, s::Symbol)
    return contains_name(get_body(d), s)
end


function codegen(d::Dot)
    return :($(codegen(get_body(d))).$(get_field(d)))
end

abstract type AbstractBLAS <: APN end

struct GEMM <: AbstractBLAS
    type::AbstractPCTType
    body::PCTVector
end

function gemm(s_1::APN, s_2::APN)
    return make_node(GEMM, pct_vec(s_1, s_2))
end

function pretty(g::GEMM)
    return "gemm($(pretty(get_body(g), false)))"
end

function verbose(g::GEMM)
    return "gemm($(verbose(get_body(g))))::$(pretty(get_type(g)))"
end

function codegen(g::GEMM)
    return :(LinearAlgebra.BLAS.gemm($(codegen.(get_body(g))...)))
end

function partial_inference(::Type{GEMM}, terms::PCTVector)
    s_1, s_2 = content(terms)
    m = first(get_content_type(get_bound_type(get_type(s_1))))
    n = last(get_content_type(get_bound_type(get_type(s_2))))
    body_type = escalate(get_body_type.(get_type.(terms))...)
    return MapType(VecType([m, n]), body_type)
end

function to_mat_mul(t_1, t_2, group_1, group_2, inner_bound, outer_bound)
    to_product_type = t -> length(t) > 1 ? product_type_from_vec(t) : first(t)
    p_1 = to_product_type(group_1)
    p_2 = to_product_type(group_2)
    p_inner = to_product_type(inner_bound)
    s_1 = call_by_indexing(pct_map(p_1, p_inner, t_1))
    s_2 = call_by_indexing(pct_map(p_inner, p_2, t_2))
    a_var = var(first(new_symbol(t_1, t_2, group_1..., group_2..., inner_bound..., outer_bound...; symbol=:_a)), get_type(s_1))
    b_var = var(first(new_symbol(t_1, t_2, group_1..., group_2..., inner_bound..., outer_bound...; symbol=:_b)), get_type(s_2))

    gemm_val = gemm(a_var, b_var)
    gemm_var = var(first(new_symbol(t_1, t_2, group_1..., group_2..., inner_bound..., outer_bound...; symbol=:_c)), get_type(gemm_val))
    result = pct_let(
        pct_copy(a_var),
        pct_copy(b_var),
        pct_copy(gemm_var),
        s_1,
        s_2,
        gemm_val,
        call_by_indexing(pct_map(outer_bound..., primitive_call(gemm_var, p_1, p_2))))
    return result
end

function cbi_to_blas(n::CBI)
    result = NeighborList()
    s = get_body(n)
    isa(s, Sum) || return result
    summand = get_body(s)
    isa(summand, Mul) || return result
    length(get_body(summand)) == 2 || return result
    t_1, t_2 = get_body(summand)
    isa(t_1, PrimitiveCall) && isa(t_2, PrimitiveCall) || return result
    outer_bound = pct_vec(map(set_type, get_bound(n), get_bound_type(get_type(n)))...)

    group_1, group_2 = index_partition(t_1, t_2, get_bound(s), outer_bound)
    #= group_1 = pct_vec(group_1...)
    group_2 = pct_vec(group_2...) =#
    isempty(intersect(group_1, group_2)) || return result

    if !isempty(group_1) && !isempty(group_2) && !isempty(get_bound(s))
        push!(result, to_mat_mul(t_1, t_2, group_1, group_2, content(get_bound(s)), outer_bound);
            dired=true, name="gemm")
        return result
    elseif isempty(group_1) && !isempty(group_2) && !isempty(get_bound(s))
        # matrix vector
    elseif !isempty(group_1) && isempty(group_2) && !isempty(get_bound(s))
        # the other matrix vector
    elseif !isempty(group_1) && !isempty(group_2) && isempty(get_bound(s))
        # outer product
    elseif isempty(group_1) && isempty(group_2) && !isempty(get_bound(s))
        # inner product
    else
        error("cannot convert $(pretty(n)) to blas.")
    end
    return result

    #= product_type_from_vec(group_1)
    product_type_from_vec(group_2)
    product_type_from_vec(get_bound(s)) =#
end

"""
[(i, j) -> A(i, j)] 
-> 
A
"""
function cbi_cancel(n::CBI)
    result = NeighborList()
    bound, body = get_bound(n), get_body(n)

    isa(body, AbstractCall) || return result
    bound == args(body) || return result

    #= push!(result, mapp(body); dired=true, name="cbi_cancel") =#
    return result
end

function neighbors(n::CBI; settings=default_settings())
    result = NeighborList()
    append!(result, sub_neighbors(n; settings=settings))
    append!(result, cbi_to_blas(n))
    append!(result, cbi_cancel(n))
    return result
end

function index_partition(t_1::PrimitiveCall, t_2::PrimitiveCall, bounds::PCTVector, outer_bounds::PCTVector)

    free_1, free_2 = get_free(args(t_1)), get_free(args(t_2))
    group_1 = filter(t -> !(t in bounds) && (t in free_1), content(outer_bounds))
    group_2 = filter(t -> !(t in bounds) && (t in free_2), content(outer_bounds))

    return [group_1...], [group_2...]
end

"""
(i, j) -> x * A(i, j)
->
x ⋅ (i, j) -> A(i, j)
"""
function map_out_neighbors(m::Union{CBI,Map})
    result = NeighborList()
    bounds = content(get_bound(m))
    all(t -> tensorize(get_type(t)), bounds) || return result
    if isa(get_body(m), Mul)
        subterms = content(get_body(get_body(m)))
        function contain_bound(t)
            free = first(free_and_dummy(t))
            return any(b -> b in free, content(get_bound(m)))
        end
        #= indices = findall(contain_bound, subterms) =#
        d = group(contain_bound, subterms)
        inner = get(d, true, [])
        outer = get(d, false, [])
        isempty(outer) && return result
        new_terms = scalar_tensor_product(mul(outer...), pct_map(bounds..., mul(inner...)))
        push!(result, new_terms; dired=true, name="map out neighbors")
    end
    return result
end

function map_dist_neighbors(m::Union{CBI,Map})
    result = NeighborList()
    term = get_body(m)
    isa(term, Add) || return result
    subterms = content(get_body(term))
    push!(result, add(map(t -> pct_map(content(get_bound(m))..., t), subterms)...);
        dired=false, name="map dist")
    return result
end

function map_elementwise_prod(m::Union{CBI,Map})
    result = NeighborList()
    term = get_body(m)
    isa(term, Mul) || return result
    subterms = content(get_body(term))
    all(t -> isa(t, AbstractCall), subterms) || return result
    if all(t -> isequal(t, get_bound(m)), map(args, subterms))
        push!(result, elementwise_mul(pct_vec(map(mapp, subterms)...)); dired=true, name="map elementwise prod")
    end
    return result
end

function map_cancel_neighbors(m::Union{CBI,Map})
    result = NeighborList()
    bounds = content(get_bound(m))
    if isa(get_body(m), AbstractCall)
        if args(get_body(m)) == get_bound(m)
            push!(result, mapp(get_body(m)); dired=true, name="map cancel")
        elseif length(content(args(get_body(m)))) == 2 &&
               content(args(get_body(m))) == reverse(bounds)
            push!(result, blas_transpose(mapp(get_body(m))); dired=true, name="map cancel transpose")
        end
    end
    return result
end


function blaserize_neighbors(m::Union{CBI,Map})
    result = NeighborList()
    append!(result, map_cancel_neighbors(m))
    append!(result, map_out_neighbors(m))
    append!(result, map_dist_neighbors(m))
    append!(result, map_elementwise_prod(m))
    append!(result, sub_blaserize_neighbors(m))
    return result
end


