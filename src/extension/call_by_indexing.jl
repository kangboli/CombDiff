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
    return mul(map(type_length, get_content_type(t))...)
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
    Crayon(italics=true)("($(join(params, ", "))) -> $(pretty(get_body(m)))")
end

struct Indexing <: APN
    type::AbstractPCTType
    body::APN
end

function pct_indexing(i::APN, type::AbstractPCTType)
    return make_node(Indexing, i, type=type)
end

function pretty(i::Indexing)
    RED_FG("($(pretty(get_type(i))))($(pretty(get_body(i))))")
end

function neighbors(i::Indexing; settings=default_settings())
    result = NeighborList()
    settings[:cbi] || return result
    index_type = get_type(i)
    base(index_type) == N() && lower(index_type) == constant(1) || return result
    push!(result, get_body(i); dired=true, name="trivial_indexing")
    return result
end

struct Serialize <: APN
    type::AbstractPCTType
    body::APN
end

function serialize(body::APN, type::AbstractPCTType)
    result = make_node(Serialize, body, type=type)
    return result
end

pretty(s::Serialize) = RED_FG("serial($(pretty(get_body(s))))")

function neighbors(s::Serialize; _...)
    result = NeighborList()
    isa(get_body(s), Indexing) || return result
    serial = get_body(get_body(s))
    @assert get_type(s) == get_type(serial)
    push!(result, get_body(get_body(s)); dired=true, name="serialization_canceling")
    return result
end

struct GetData <: AbstractMap
    type::AbstractPCTType
    body::APN
end

function call(mapp::Union{GetData, Dot}, args::Vararg)
    make_node(PrimitiveCall, mapp, make_node(PCTVector, args...))
end

function get_data(body::APN)
    make_node(GetData, body)
end


function partial_inference(::Type{GetData}, body)
    bound_types = get_bound_type(get_type(body))
    new_bound_types = map(l -> parametrize_type(N(), l), type_length.(bound_types))
    return MapType(VecType(new_bound_types), get_body_type(get_type(body)))
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

    push!(result, call(data, map(strip_indexing, get_bound_type(get_type(data)), args(c))...); dired=true, name="get_data")
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
        typename = $(QuoteNode(get_typename(t))),
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

#= function construct_from_index(domains, i::Int)
    sizes = [u - l + 1 for (u, l) in domains]

    result = Vector{Int}()
    for j in 1:length(domains)
        i, r = divrem(i, prod(sizes[j:end]))
        push!(result, r)
    end

end
 =#
