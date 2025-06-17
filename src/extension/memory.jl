using Accessors
export alloc_memory!, get_memory

abstract type AbstractMemory end

function get_id(m::AbstractMemory)
    return m._id
end

abstract type MemoryUnit <: AbstractMemory end

struct MemoryStack <: MemoryUnit
    _id::UInt
end

struct MemorySeg <: MemoryUnit
    _id::UInt
    _size::APN
end

MemorySeg(size::APN) = MemorySeg(1, size)
get_size(seg::MemorySeg) = seg._size

offset_id(m::MemorySeg, offset::UInt) = @set m._id += offset

struct MemoryBlock <: MemoryUnit
    _id::UInt
    sub_units::Vector{MemoryUnit}
    function MemoryBlock(_id, units)
        units = filter(t -> !isa(t, MemoryStack), units)
        units = filter(t -> !(isa(t, MemoryBlock) && length(t) == 0), units)

        return new(_id, units)
    end
end

MemoryBlock(_id) = MemoryBlock(_id, Vector{MemoryUnit}())
get_sub_units(b::MemoryBlock) = b.sub_units
pushfirst_unit(b::MemoryBlock, new_unit) = @set b.sub_units = [new_unit, b.sub_units...]
Base.length(b::MemoryBlock) = length(get_sub_units(b))

function offset_id(m::MemoryBlock, offset::UInt)
    MemoryBlock(
        get_id(m) + offset,
        map(u -> offset_id(u, offset), get_sub_units(m))
    )
end

abstract type MemoryIntermediate <: AbstractMemory end

"""
For some expressions, some of the memory is 
allcoated for intermediates and the rest for the 
output. The output memory is potentially bound 
to a variable whereas the intermediates should be marked invalid.
"""
mutable struct WorkMemory <: MemoryIntermediate
    _id::UInt
    buf::MemoryBlock
    value::AbstractMemory
end

function offset_id(m::WorkMemory, offset::UInt)
    return WorkMemory(
        get_id(m) + offset,
        offset_id(get_buf_mem(m), offset),
        offset_id(get_value_mem(m), offset))
end

get_buf_mem(lm::WorkMemory) = lm.buf
get_value_mem(lm::WorkMemory) = lm.value

struct MapMemory <: MemoryIntermediate
    _proto::WorkMemory
end

function instantiate(m::MapMemory, _id::UInt)
    return offset_id(m._proto, _id)
end

function get_proto(m::MapMemory)
    return m._proto
end


struct ParametricMapMemory <: MemoryIntermediate
    parametric_map::ParametricMap
    map_mem::MapMemory
end

function instantiate(pm::ParametricMapMemory, _id::UInt, args...)
    values = Dict()
    type_vars = get_bound(pm.parametric_map)
    m = get_body(pm.parametric_map)
    type_match!([type_vars...], values, get_bound_type(get_type(m)), VecType(get_type.([args...])))

    offseted = instantiate(pm.map_mem, _id)
    for t in type_vars
        offseted = mem_subst(offseted, t, values[t])
    end
    return offseted
end

function mem_subst(m::MemorySeg, old, new)
    return @set m._size = subst(m._size, old, new)
end

function mem_subst(m::MemoryBlock, old, new)
    return @set m.sub_units = map(t -> mem_subst(t, old, new), m.sub_units)
end

function mem_subst(m::WorkMemory, old, new)
    m = @set m.buf = mem_subst(m.buf, old, new)
    return @set m.value = mem_subst(m.value, old, new)
end

function mem_subst(m::MapMemory, old, new)
    return @set m._proto = mem_subst(m._proto, old, new)
end

function mem_subst(pm::ParametricMapMemory, old, new)
    ParametricMapMemory(
        subst(pm.parametric_map, old, new),
        mem_subst(pm.map_mem, old, new)
    )
end

max_id(m::Union{MemorySeg,MemPlaceHolder,MemoryStack}) = get_id(m)
max_id(m::Union{MemoryBlock,WorkMemory}) = max(get_id(m), max_id.(get_sub_units(m))...)
max_id(m::MapMemory) = max_id(m._proto)
max_id(m::ParametricMapMemory) = max_id(m.map_mem)


struct WithMemory <: APN
    type::AbstractPCTType
    memory::AbstractMemory
    body::APN
end

with_memory(memory, body) = make_node(WithMemory, memory, body)
set_memory(wm::WithMemory, new_mem) = @set wm.memory = new_mem
get_memory(wm::WithMemory) = wm.memory
get_memory(::APN) = MemoryStack(0)

type_size(t::ElementType) = type_size(base(t))
type_size(::Union{I,R,N}) = constant(8)
type_size(::Union{C}) = constant(16)
type_size(m::MapType) = mul(type_length.(get_bound_type(m))..., type_size(get_body_type(m)))
type_size(v::AbstractVecType) = add(type_size.(get_content_type(v))...)

function partial_inference(::Type{WithMemory}, memory, body)
    return get_type(body)
end

function alloc_memory!(n::CBI, _id::UInt)
    n_type = get_type(n)
    mem = MemorySeg(_id, type_size(n_type))
    return with_memory(mem, n), _id + 1
end

function alloc_memory!(n::APN, _id::UInt)
    new_terms = []
    for t in terms(n)
        new_t, _id = alloc_memory!(t, _id)
        push!(new_terms, new_t)
    end

    buf = MemoryBlock(_id + 1, get_memory.(new_terms))
    value_mem = MemorySeg(_id + 2, type_size(get_type(n)))
    return with_memory(WorkMemory(_id + 3, buf, value_mem), set_terms(n, new_terms...)), _id + 4
end

function alloc_memory!(n::TerminalNode, _id::UInt)
    mem = get_memory(n)
    mem = mem == :_ ? MemoryStack(0) : mem
    return with_memory(mem, n), _id
end

function alloc_memory!(lt::Let, _id::UInt)
    b, b_rest... = get_bound(lt)
    a, a_rest... = args(lt)

    a_new, _id = alloc_memory!(a, _id)
    b_new = set_memory(b, get_memory(a_new))

    let_rest = subst(pct_let(b_rest..., a_rest..., get_body(lt)), get_body(b), get_body(b_new))
    let_rest, _id = alloc_memory!(let_rest, _id)

    work_mem = get_memory(let_rest)

    if !isa(get_body(let_rest), Let)
        buf_mem = MemoryBlock(_id + 1)
        #= hasfield(typeof(get_memory(let_rest)), :_id) && println(get_id(get_memory(let_rest))) =#
        if !(isa(get_memory(a_new), MapMemory) || isa(get_memory(a_new), ParametricMapMemory))
            buf_mem = pushfirst_unit(buf_mem, get_memory(a_new))
        end

        mem = WorkMemory(_id + 2, buf_mem, work_mem)
        return with_memory(mem, pct_let(b_new, a_new, let_rest)), _id + 3
    else
        buf_mem = get_buf_mem(work_mem)
        if !(isa(get_memory(a_new), MapMemory) || isa(get_memory(a_new), ParametricMapMemory))
            buf_mem = pushfirst_unit(buf_mem, get_memory(a_new))
        end
        mem = WorkMemory(get_id(work_mem),
            buf_mem,
            get_value_mem(work_mem))

        return with_memory(mem, pct_let(b_new, a_new, get_body(let_rest))), _id + 1
    end

end

function alloc_memory!(m::Map, _id::UInt)
    body, _id_map = alloc_memory!(get_body(m), UInt(1))
    mem = if isa(get_memory(body), WorkMemory)
        MapMemory(get_memory(body))
    else
        MapMemory(WorkMemory(_id_map + 1, MemoryBlock(_id_map + 1, Vector{MemoryUnit}()), get_memory(body)))
    end
    return with_memory(mem, pct_map(get_bound(m)..., body)), _id
end

function alloc_memory!(m::ParametricMap, _id::UInt)
    new_body, _ = alloc_memory!(get_body(m), _id)
    new_map = parametric_map(get_bound(m)..., new_body)
    mem = ParametricMapMemory(new_map, get_memory(new_body))
    return with_memory(mem, new_map), _id
end

function alloc_memory!(c::PrimitiveCall, _id::UInt)
    m, ags = mapp(c), args(c)

    m, _id = alloc_memory!(m, _id)
    new_args = []
    for a in ags
        a_new, _id = alloc_memory!(a, _id)
        push!(new_args, a_new)
    end

    isa(get_memory(m), MapMemory) || isa(get_memory(m), ParametricMapMemory) ||
        error("allocating memory for $(pretty(m)) is not supported")

    exe_mem = instantiate(get_memory(m), _id, new_args...)
    _id = max_id(exe_mem) + 1

    buf = MemoryBlock(_id + 1, get_memory.(new_args))

    mem = WorkMemory(_id + 2, buf, exe_mem)

    return with_memory(mem, call(m, new_args...)), _id + 3
end

struct MemPlaceHolder <: AbstractMemory
    order::UInt
end

order(m::MemPlaceHolder) = m.order

order(m::MemorySeg) = length(string(get_id(m))) #+ 1 + length(string(pretty(m._size))) 
order(m::MemoryStack) = 0
function order(m::MemoryBlock)
    length(get_sub_units(m)) == 0 && return 0
    #= println("---")
    println(get_id(m))
    println(sum(order, get_sub_units(m); init=0))
    println(get_id.(get_sub_units(m)))
    println("---") =#
    return sum(order, get_sub_units(m); init=0) + length(get_sub_units(m)) - 1
end
function order(m::WorkMemory)
    result = order(get_buf_mem(m)) + order(get_value_mem(m)) + (order(get_buf_mem(m)) == 0 ? 0 : 1)
    #= println("->")
    println(get_id(m))
    println(order(get_buf_mem(m)))
    println(order(get_value_mem(m)))
    println(result)
    println("<-") =#
    return result
end
order(m::MapMemory) = 0


get_sub_units(b::WorkMemory) = [get_buf_mem(b), get_value_mem(b)]
get_sub_units(::AbstractMemory) = []


collect_segs(m::MemorySeg) = [m]

collect_segs(::MemoryStack) = []

collect_segs(m::AbstractMemory) = vcat(collect_segs.(get_sub_units(m))...)

function mem_summary(m::AbstractMemory)
    segs = collect_segs(m)
    sort!(segs, by=get_id)
    unique!(get_id, segs)
    return join(map(s -> Crayon(underline=true, background=(150, 230, 130), foreground=(30, 90, 10))("$(get_id(s)):$(pretty(get_size(s)))"), segs), " ")
end


function pretty(m::AbstractMemory)
    bg = Dict(
        MemorySeg => Crayon(background=(60, 120, 60), underline=true),
        MemoryBlock => Crayon(background=(80, 30, 80), underline=true),
        WorkMemory => Crayon(background=(20, 100, 120), underline=true),
    )

    function single_memory_str(m::T) where {T<:AbstractMemory}
        id = get_id(m)
        id_string = string(id)
        id_string = id_string[1:min(order(m), length(id_string))]

        padding = " "^(order(m) - length(id_string))
        return bg[T]("$(id_string)$(padding)")
        #= return "$(id_string)$(padding)" =#
    end

    function single_memory_str(seg::MemorySeg)
        id_string = string(get_id(seg))
        return bg[MemorySeg]("$(id_string)")
        #= return "$(id_string)" =#
    end
    function single_memory_str(seg::MemPlaceHolder)
        return " "^order(seg)
    end

    mem_list = [Crayon() => m]
    block_string = ""
    while !isempty(mem_list) && !all(t -> isa(last(t), MemPlaceHolder), mem_list)
        block_string = block_string == "" ? block_string : block_string * "\n"
        block_string *= join(map(((color, t),) -> color(single_memory_str(t)), mem_list),
            " ")
        new_mem_list = []

        for n in mem_list
            n = last(n)
            if isa(n, WorkMemory)
                buf_units = filter(u -> order(u) > 0, get_sub_units(get_buf_mem(n)))
                append!(new_mem_list, [Crayon(foreground=(210, 10, 10)) => t for t in buf_units])
                #= append!(new_mem_list, [Crayon(bold=true) => get_buf_mem(n)]) =#
                append!(new_mem_list, [Crayon(foreground=(10, 220, 10)) => get_value_mem(n)])
            elseif isa(n, MemoryBlock)
                sub_units = filter(u -> order(u) > 0, get_sub_units(n))
                append!(new_mem_list, [(x->x) => t for t in sub_units])
            elseif isa(n, MemorySeg) || isa(n, MemPlaceHolder)
                append!(new_mem_list, [(x->x) => MemPlaceHolder(order(n))])
            end
        end
        mem_list = filter(u -> order(last(u)) > 0, new_mem_list)
    end
    return "$(mem_summary(m))\n$(block_string)"
end

function pretty(wm::WithMemory)
    mem = get_memory(wm)
    if isa(mem, MemoryStack) || isa(mem, ParametricMapMemory)
        "$(pretty(get_body(wm)))"
    elseif isa(mem, MapMemory)
        if order(get_proto(mem)) > 0
            return "$(pretty(get_proto(mem)))\n$(pretty(get_body(wm)))"
        else
            return "$(pretty(get_body(wm)))"
        end
        #= elseif isa(mem, ParametricMapMemory)
            if order(get_proto(mem.map_mem)) > 0
                return "$(pretty(get_proto(mem.map_mem)))\n$(pretty(get_body(wm)))"
            else
                return "$(pretty(get_body(wm)))"
            end =#
    else
        if order(mem) > 0
            "($(pretty(get_body(wm))))@$(UNDERLINE(string(get_id(mem))))"
        else
            "($(pretty(get_body(wm))))"
        end
    end
end

