using Accessors
export alloc_memory!, get_memory, MemoryManager

abstract type AbstractMemory end

mutable struct MemoryManager
    curr_id::UInt
    depth::UInt
    ownerships::Dict{UInt,Stack{Bool}}
    memories::Dict{UInt,AbstractMemory}
end

MemoryManager() = MemoryManager(0, 1, Dict{UInt,Stack{Bool}}(), Dict{UInt,AbstractMemory}())

function register!(mm::MemoryManager, m::AbstractMemory)
    mm.memories[get_id(m)] = m
    return m
end

function allocate_segment!(mm::MemoryManager, size::APN)
    i = findfirst(j -> top(mm.ownerships[j]) && get_size(mm.memories[j]) == size, 1:get_curr_id(mm))
    i !== nothing && return mm.memories[i]
    seg = MemorySeg(next_id!(mm), size)
    mm.memories[get_id(seg)] = seg
    return seg
end

function next_id!(m::MemoryManager)
    m.curr_id = get_curr_id(m) + 1
    #= m.curr_id == 3 && error() =#
    m.ownerships[get_curr_id(m)] = Stack{Bool}()
    for _ in 1:get_depth(m)
        push!(m.ownerships[get_curr_id(m)], true)
    end
    return get_curr_id(m)
end

get_curr_id(m::MemoryManager) = m.curr_id

get_depth(mm::MemoryManager) = mm.depth



abstract type MemoryUnit <: AbstractMemory end

get_id(m::AbstractMemory) = 0
get_id(m::MemoryUnit) = m._id
struct MemoryStack <: MemoryUnit
    _id::UInt
end

struct MemorySeg <: MemoryUnit
    _id::UInt
    _size::APN
end

MemorySeg(size::APN) = MemorySeg(1, size)
get_size(seg::MemorySeg) = seg._size

function instantiate(m::MemoryStack, ::MemoryManager, _...)
    return m
end

function instantiate(m::MemorySeg, ::MemoryManager, args...)
    return m
end

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

function instantiate(m::MemoryBlock, mm::MemoryManager)
    register!(mm, MemoryBlock(
        next_id!(mm),
        map(u -> instantiate(u, mm), get_sub_units(m))
    ))
end

abstract type MemoryIntermediate <: AbstractMemory end

"""
For some expressions, some of the memory is 
allcoated for intermediates and the rest for the 
output. The output memory is potentially bound 
to a variable whereas the intermediates should be marked invalid.
"""
mutable struct WorkMemory <: MemoryUnit
    _id::UInt
    buf::MemoryBlock
    value::AbstractMemory
end

function instantiate(m::WorkMemory, mm::MemoryManager)
    register!(mm, WorkMemory(
        next_id!(mm),
        instantiate(get_buf_mem(m), mm),
        instantiate(get_value_mem(m), mm)))
end

get_buf_mem(lm::WorkMemory) = lm.buf
get_value_mem(lm::WorkMemory) = lm.value

struct MapMemory <: MemoryIntermediate
    _mapp::AbstractMap
    _proto::WorkMemory
end

function get_proto(m::MapMemory)
    return m._proto
end


struct ParametricMapMemory <: MemoryIntermediate
    _mapp::ParametricMap
    map_mem::MapMemory
end

function instantiate(m::Union{MapMemory,ParametricMapMemory}, mm::MemoryManager, new_args...)
    new_bounds = map((b, a) -> set_type(set_memory(b, get_memory(a)), get_type(a)), get_bound(get_body(m._mapp)), [new_args...])
    #= lock_ownership!(mm) =#
    result = alloc_memory!(ecall(m._mapp, new_bounds...), mm)
    #= pop_ownership!(mm) =#
    return get_memory(result)
end


#= function instantiate(pm::ParametricMapMemory, mm::MemoryManager, new_args...)
    new_bounds = map((b, a) -> set_memory(b, get_memory(a)), get_bound(pm._mapp), [new_args...])
    #= lock_ownership!(mm) =#
    result = alloc_memory!(ecall(pm._mapp, new_bounds...), mm)
    #= pop_ownership!(mm) =#
    return get_memory(result)
end =#

struct MemPlaceHolder <: AbstractMemory
    order::UInt
end

order(m::MemPlaceHolder) = m.order

function mem_subst(m::MemoryStack, _...)
    m
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
        subst(pm._mapp, old, new),
        mem_subst(pm.map_mem, old, new)
    )
end

max_id(m::Union{MemorySeg,MemPlaceHolder,MemoryStack}) = get_id(m)
max_id(m::Union{MemoryBlock,WorkMemory}) = max(get_id(m), max_id.(get_sub_units(m))...)
max_id(m::MapMemory) = 0
max_id(m::ParametricMapMemory) = 0
#= max_id(m::MapMemory) = max_id(m._proto)
max_id(m::ParametricMapMemory) = max_id(m.map_mem) =#

all_id(m::Union{MemorySeg,MemPlaceHolder,MemoryStack}) = [get_id(m)]
all_id(m::Union{MemoryBlock,WorkMemory}) = vcat([get_id(m)], all_id.(get_sub_units(m))...)
all_id(::MapMemory) = []
all_id(::ParametricMapMemory) = []

struct WithMemory <: APN
    type::AbstractPCTType
    memory::AbstractMemory
    body::APN
end

with_memory(memory, body) = make_node(WithMemory, memory, body)
set_memory(wm::WithMemory, new_mem) = @set wm.memory = new_mem
set_memory(v::Var, new_memory) = @set v.memory = new_memory
get_memory(wm::WithMemory) = wm.memory
get_memory(v::Var) = isa(v.memory, Symbol) ? MemoryStack(0) : v.memory
get_memory(::APN) = MemoryStack(0)

type_size(t::ElementType) = type_size(base(t))
type_size(::Union{I,R,N}) = constant(1)
type_size(::Union{C}) = constant(2)
type_size(m::MapType) = mul(type_length.(get_bound_type(m))..., type_size(get_body_type(m)))
type_size(v::AbstractVecType) = add(type_size.(get_content_type(v))...)

function partial_inference(::Type{WithMemory}, memory, body)
    return get_type(body)
end

Base.isless(n_1::WithMemory, n_2::APN) = isless(get_body(n_1), n_2)
Base.isless(n_1::APN, n_2::WithMemory) = isless(n_1, get_body(n_2))
Base.isless(n_1::WithMemory, n_2::WithMemory) = isless(get_body(n_1), get_body(n_2))


function push_ownership!(m::MemoryManager, l::APN)
    free = get_free(l)
    pinned_id = vcat(all_id.(get_memory.(free))...)
    unique!(sort!(pinned_id))

    for id in 1:get_curr_id(m)
        if id in pinned_id || (top(m.ownerships[id]) == false)
            push!(m.ownerships[id], false)
        else
            push!(m.ownerships[id], true)
        end
    end
    m.depth = m.depth + 1
end

function lock_ownership!(m::MemoryManager)
    for id in 1:get_curr_id(m)
        push!(m.ownerships[id], false)
    end
    m.depth = m.depth + 1

end

function pop_ownership!(m::MemoryManager)
    for id in 1:get_curr_id(m)
        pop!(m.ownerships[id])
    end
    m.depth = m.depth - 1
end

function alloc_memory!(n::CBI, mm::MemoryManager)
    n_type = get_type(n)
    lock_ownership!(mm)
    new_body = alloc_memory!(get_body(n), mm)
    pop_ownership!(mm)

    body_mem = get_memory(new_body)

    push_ownership!(mm, n)
    mem = allocate_segment!(mm, type_size(n_type))
    pop_ownership!(mm)

    if isa(body_mem, WorkMemory)
        mem = register!(mm, WorkMemory(get_id(body_mem),
            get_buf_mem(body_mem), mem))
    end
    return with_memory(mem, pct_map(get_bound(n)..., new_body))
end

function alloc_memory_from_type!(n::T, mm::MemoryManager) where {T<:APN}
    if isa(get_type(n), ElementType)
        return MemoryStack(0)
    elseif cbi_applicable(get_type(n))
        return allocate_segment!(mm, type_size(get_type(n)))
    else
        error("cannot allocate memory for $(pretty(n))")
    end

end

function alloc_memory!(n::APN, mm::MemoryManager)
    new_terms = []
    for t in terms(n)
        lock_ownership!(mm)
        new_t = alloc_memory!(t, mm)
        pop_ownership!(mm)
        push!(new_terms, new_t)
    end
    isa(n, PCTVector) && return n

    buf = if sum(order, get_memory.(new_terms)) > 0
        register!(mm, MemoryBlock(next_id!(mm), get_memory.(new_terms)))
    else
        MemoryStack(0)
    end

    value_mem = alloc_memory_from_type!(n, mm)

    return if order(buf) > 0
        with_memory(register!(mm, WorkMemory(next_id!(mm), buf, value_mem)), set_terms(n, new_terms...))
    else
        with_memory(value_mem, set_terms(n, new_terms...))
    end
end

function alloc_memory!(n::TerminalNode, ::MemoryManager)
    mem = get_memory(n)
    mem = mem == :_ ? MemoryStack(0) : mem
    return with_memory(mem, n)
end

get_return_memory(m::AbstractMemory) = m

get_return_memory(m::WorkMemory) = get_return_memory(get_value_mem(m))

function alloc_memory!(lt::Let, mm::MemoryManager)
    b, b_rest... = get_bound(lt)
    a, a_rest... = args(lt)

    let_rest = pct_let(b_rest..., a_rest..., get_body(lt))

    push_ownership!(mm, let_rest)
    a_new = alloc_memory!(a, mm)
    pop_ownership!(mm)

    b_new = set_memory(b, get_return_memory(get_memory(a_new)))
    let_rest = subst(let_rest, get_body(b), get_body(b_new))
    let_rest = alloc_memory!(let_rest, mm)
    work_mem = get_memory(let_rest)

    if !isa(get_body(let_rest), Let)
        buf_mem = register!(mm, MemoryBlock(next_id!(mm)))
        if !(isa(get_memory(a_new), MapMemory) || isa(get_memory(a_new), ParametricMapMemory))
            buf_mem = pushfirst_unit(buf_mem, get_memory(a_new))
        end

        mem = register!(mm, WorkMemory(next_id!(mm), buf_mem, work_mem))
        return with_memory(mem, pct_let(b_new, a_new, let_rest))
    else
        buf_mem = get_buf_mem(work_mem)
        if !(isa(get_memory(a_new), MapMemory) || isa(get_memory(a_new), ParametricMapMemory))
            buf_mem = pushfirst_unit(buf_mem, get_memory(a_new))
        end
        mem = WorkMemory(get_id(work_mem),
            buf_mem,
            get_value_mem(work_mem))

        return with_memory(mem, pct_let(b_new, a_new, get_body(let_rest)))
    end

end

function alloc_memory!(m::Map, ::MemoryManager)
    mm = MemoryManager()
    body = alloc_memory!(get_body(m), mm)
    mem = if isa(get_memory(body), WorkMemory)
        MapMemory(m, get_memory(body))
    else
        MapMemory(m, register!(mm, WorkMemory(next_id!(mm),
            register!(mm, MemoryBlock(next_id!(mm), Vector{MemoryUnit}())), get_memory(body))))
    end
    return with_memory(mem, pct_map(get_bound(m)..., body))
end

function alloc_memory!(m::ParametricMap, mm::MemoryManager)
    new_body = alloc_memory!(get_body(m), mm)
    new_map = parametric_map(get_bound(m)..., new_body)
    mem = ParametricMapMemory(m, get_memory(new_body))
    return with_memory(mem, new_map)
end

function alloc_memory!(c::PrimitiveCall, mm::MemoryManager)
    m, ags = mapp(c), args(c)

    new_args = []
    for a in ags
        #= push_ownership!(mm, pct_vec(ags[i+1:end]..., m)) =#
        lock_ownership!(mm)
        a_new = alloc_memory!(a, mm)
        pop_ownership!(mm)
        push!(new_args, a_new)
    end

    lock_ownership!(mm)
    m = alloc_memory!(m, mm)
    pop_ownership!(mm)

    isa(get_memory(m), Union{MapMemory,ParametricMapMemory,MemoryStack,MemorySeg}) ||
        error("allocating memory for $(pretty(m)) is not supported")

    exe_mem = instantiate(get_memory(m), mm, new_args...)

    buf = if sum(order, get_memory.(new_args)) > 0
        register!(mm, MemoryBlock(next_id!(mm), get_memory.(new_args)))
    else
        MemoryStack(0)
    end

    mem = if order(buf) > 0
        register!(mm, WorkMemory(next_id!(mm), buf, exe_mem))
    else
        exe_mem
    end
    return with_memory(mem, call(m, new_args...))
end


order(m::MemorySeg) = length(string(get_id(m))) + 1
order(m::MemoryStack) = 0
function order(m::MemoryBlock)
    length(get_sub_units(m)) == 0 && return 0
    return sum(width, get_sub_units(m); init=0) # + length(get_sub_units(m)) - 1
end
function order(m::WorkMemory)
    result = width(get_buf_mem(m)) + width(get_value_mem(m)) # + (order(get_buf_mem(m)) == 0 ? 0 : 1)
    return result
end
order(m::MapMemory) = 0

width(m::AbstractMemory) = order(m)
function width(m::Union{MemoryBlock,WorkMemory})
    order(m) == 0 && return 0
    return max(length(string(get_id(m))) + 1, order(m))
end

get_sub_units(b::WorkMemory) = [get_buf_mem(b), get_value_mem(b)]
get_sub_units(::AbstractMemory) = []


collect_segs(m::MemorySeg) = [m]

collect_segs(::MemoryStack) = []

collect_segs(m::AbstractMemory) = vcat(collect_segs.(get_sub_units(m))...)

function mem_summary(m::AbstractMemory)
    segs = collect_segs(m)
    sort!(segs, by=get_id)
    unique!(get_id, segs)
    return Crayon(underline=true, background=(40, 80, 90),
        foreground=(230, 210, 40))(
        join(map(s -> "$(get_id(s)):$(pretty(get_size(s)))", segs), "⎹"))

end


function pretty(m::AbstractMemory)
    bg = Dict(
        MemorySeg => Crayon(background=(20, 100, 20)),
        MemoryBlock => Crayon(background=(120, 50, 50)),
        WorkMemory => Crayon(background=(40, 80, 220)),
    )

    function single_memory_str(m::T) where {T<:AbstractMemory}
        id = get_id(m)
        id_string = string(id)
        #= id_string = id_string[1:min(order(m), length(id_string))] =#

        padding = " "^(width(m) - length(id_string) - 1)
        id_string = id_string * padding
        return "$(bg[T](id_string))$(Crayon(reset=true)(" "))"
        #= return "$(id_string)$(padding)" =#
    end

    function single_memory_str(seg::MemorySeg)
        id_string = string(get_id(seg))
        return "$(bg[MemorySeg](id_string))$(Crayon(reset=true)(" "))"
        #= return "$(id_string)" =#
    end
    function single_memory_str(seg::MemPlaceHolder)
        return " "^order(seg)
    end

    mem_list = [Crayon() => m]
    block_string = ""
    while !isempty(mem_list) && !all(t -> isa(last(t), MemPlaceHolder), mem_list)
        block_string = block_string == "" ? block_string : block_string * "\n"
        block_string *= join(map(((color, t),) -> color(single_memory_str(t)), mem_list), "")
        new_mem_list = []

        for n in mem_list
            n = last(n)
            new_mem = if isa(n, WorkMemory)
                #= buf_units = filter(u -> order(u) > 0, get_sub_units(get_buf_mem(n)))
                append!(new_mem_list, [Crayon(foreground=(210, 10, 10)) => t for t in buf_units]) =#
                [Crayon(italics=true) => get_buf_mem(n),
                    Crayon(underline=true) => get_value_mem(n)]

            elseif isa(n, MemoryBlock)
                sub_units = filter(u -> order(u) > 0, get_sub_units(n))
                [(x -> x) => t for t in sub_units]
            elseif isa(n, MemorySeg) || isa(n, MemPlaceHolder)
                [(x -> x) => MemPlaceHolder(width(n))]
            end
            append!(new_mem_list, new_mem)
            diff = width(n) - order(n)
            if diff > 0
                append!(new_mem_list, [Crayon() => MemPlaceHolder(diff)])
            end
        end
        #= mem_list = filter(u -> order(last(u)) > 0, new_mem_list) =#
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
            return "MEM:\n$(pretty(get_proto(mem)))\n$(pretty(get_body(wm)))"
        else
            return "$(pretty(get_body(wm)))"
        end
    else
        if order(mem) > 0
            "($(pretty(get_body(wm))))@$(UNDERLINE(string(get_id(mem))))"
        else
            "($(pretty(get_body(wm))))"
        end
    end
end

