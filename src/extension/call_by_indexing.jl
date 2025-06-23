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
    return pct_vec(map(type_length, get_content_type(t))...)
end

function call_by_indexing(bound::PCTVector, body::APN)
    return make_node(CBI, bound, body)
end

function call_by_indexing(body::Map)
    bounds = get_bound(body)
    new_bound_types = map(l -> parametrize_type(N(), l), type_length.(get_type.(bounds)))
    new_bounds = map((b, t) -> set_type(b, t), bounds, new_bound_types)

    indexings = map((b, t) -> pct_indexing(b, t), new_bounds, get_type(bounds))

    return make_node(CBI, pct_vec(new_bounds...), ecall(body, indexings...), type=get_type(body))
end

function pretty(m::CBI)
    params = map(v -> "$(pretty(v))", content(get_bound(m)))
    "[($(join(params, ", "))) -> $(pretty(get_body(m)))]"
end

function verbose(m::CBI)
    params = map(v -> "$(verbose(v))", content(get_bound(m)))
    "[($(join(params, ", "))) -> $(verbose(get_body(m)))]"
end

"""
Given an linear index, return an element in the set.
"""
struct Indexing <: APN
    type::AbstractPCTType
    body::APN
end

function pct_indexing(i::APN, type::AbstractPCTType)
    return make_node(Indexing, i, type=type)
end

print_colors_defaults[:indexing] = Crayon(foreground=(200, 100, 130))

function pretty(i::Indexing)
    type_str = isa(get_type(i), ProductType) ? string(get_typename(get_type(i))) : pretty(get_type(i))
    if type_str == "__anonymous"
        print_colors_defaults[:indexing]("|$(pretty(get_body(i)))|")
    else
        print_colors_defaults[:indexing]("($type_str)($(pretty(get_body(i))))")
    end
end

"""
indexing{N{1:M}}(i) = i
"""
function neighbors(i::Indexing; settings=default_settings())
    result = NeighborList()
    settings[:cbi] || return result
    index_type = get_type(i)
    base(index_type) == N() && lower(index_type) == constant(1) || return result
    push!(result, get_body(i); dired=true, name="trivial_indexing")
    return result
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


function serialize_product(s::Serialize)
    result = NeighborList()
    p = get_body(s)
    isa(get_type(p), ProductType) || return result

    indices = args(p)

    dims = [constant(1), accumulate(mul, type_length.(get_content_type(get_type(indices))))...]

    new_s = add(map((prefactor, c, a) -> mul(prefactor, subtract(strip_indexing(c, a), constant(1))), dims,
            map(t -> parametrize_type(N(), type_length(t)), get_content_type(get_type(p))),
            indices)..., constant(1))
    push!(result, new_s; dired=true, name="serialize_product")
    return result
end

function serialization_canceling(s::Serialize)
    result = NeighborList()
    isa(get_body(s), Indexing) || return result
    serial = get_body(get_body(s))
    #= println(pretty(get_type(s)))
    println(pretty(get_type(serial))) =#
    @assert get_type(s) == get_type(serial)
    push!(result, get_body(get_body(s)); dired=true, name="serialization_canceling")
    return result
end

"""
serialize{S}(index{S}(i)) = i
"""
function neighbors(s::Serialize; _...)
    result = NeighborList()
    append!(result, serialization_canceling(s))
    append!(result, serialize_product(s))
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

    #= if isa(body_type, ParametricMapType)
        return ParametricMapType(get_params(body_type), inference_maptype(get_body_type(body_type)))
    else
        return inference_maptype(body_type)
    end =#

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

push!(neighbor_registry[Map], map_cbi)


function to_cbi(n::APN)
    simplify(n; settings=custom_settings(:cbi => true))
end


strip_indexing(::AbstractPCTType, i::Indexing) = get_body(i)
strip_indexing(t::AbstractPCTType, i::APN) = serialize(i, t)

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

push!(neighbor_registry[AbstractCall], call_get_data)

function sum_cbi(s::Sum)
    result = NeighborList()

    bounds = get_bound(s)
    m = pct_map(bounds..., get_body(s))
    cbi_applicable(get_type(m)) || return result
    all(is_basic_type, get_type.(bounds)) && return result

    new_bound_types = map(l -> parametrize_type(N(), l), type_length.(get_type.(bounds)))
    new_bounds = map((b, t) -> set_type(b, t), bounds, new_bound_types)
    indexings = map((b, t) -> pct_indexing(b, t), new_bounds, get_type(bounds))
    new_sum = make_node(Sum, pct_vec(new_bounds...), ecall(m, indexings...), type=get_type(m))

    push!(result, new_sum; dired=true, name="sum_cbi")
    return result
end

push!(neighbor_registry[Sum], sum_cbi)

function codegen(c::CBI)
    ranges = map(codegen, get_type(get_bound(c)))

    sizes = type_length.(get_type(get_bound(c)))


    loop = codegen(get_body(c))

    body = get_body(c)

    for (b, s) in zip(get_bound(c), sizes)
        loop = :(@inbounds for $(codegen(b)) in $(codegen(s))
            $(loop)
        end
        )
    end

    tensor_var_name = first(new_symbol(c))
    memory_target = :(zeros($(codegen(get_type(body))), $(codegen.(sizes)...)))
    return :(
        let $(tensor_var_name) = $(memory_target)
            $(loop)
            CombDiff.cbi_tensor(ranges, tensor_var_name)
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

function cbi_to_blas(n::CBI)
    result = NeighborList()
    s = get_body(n)
    isa(s, Sum) || return result
    summand = get_body(s)
    isa(summand, Mul) || return result
    length(get_body(summand)) == 2 || return result
    t_1, t_2 = get_body(summand)
    isa(t_1, PrimitiveCall) && isa(t_2, PrimitiveCall) || return result

end

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

push!(neighbor_registry[AbstractCall], indexing_get_field_neighbor)


#= function matricize(t::PrimitiveCall, rows::PCTVector, cols::PCTVector)
    row_dim = [constant(1), accumulate(mul, type_length.(get_type.(rows)))...]
    col_dim = [constant(1), accumulate(mul, type_length.(get_type.(cols)))...]

    row_var = var(first(new_symbol(t, rows, cols; symbol=:_r)),
        parametrize_type(N(), row_dim[end]))
    col_var = var(first(new_symbol(t, rows, cols, row_var; symbol=:_c)),
        parametrize_type(N(), col_dim[end]))

    function get_index(v::Var)
        i = findfirst(t -> name(t) == name(v), collect(rows))
        if i !== nothing
            rc = row_var
            dim = row_dim
            offset = subtract(lower(get_type(rows[i])), constant(1))
        else
            i = findfirst(t -> name(t) == name(v), collect(cols))
            rc = col_var
            dim = col_dim
            offset = subtract(lower(get_type(cols[i])), constant(1))
        end

        return add(call(var(:div, MultiType(div)), call(var(:rem, MultiType(rem)), rc, dim[i+1]), dim[i]), offset)
    end

    result = pct_map(row_var, col_var, call(mapp(t), get_index.(args(t))...))
    return result
end =#
