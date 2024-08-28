export annihilate, reduce_vac, vac_exp, anti_commute, VacExp

"""
The fermionic operator as a value.
"""
struct FermionicFieldAnnihilation <: FieldOperators
    type::AbstractPCTType
    body::Symbol
end

annihilate(body::Symbol) = make_node(FermionicFieldAnnihilation, body)
function pretty(f::FermionicFieldAnnihilation)
    "$(get_body(f))"
end


is_annihilation(::APN) = false
is_annihilation(p::PrimitiveCall) = isa(mapp(p), FermionicFieldAnnihilation)

is_creation(::APN) = false
is_creation(v::Conjugate) = is_annihilation(get_body(v))

is_field_op(n::APN) = is_annihilation(n) || is_creation(n)

get_op_name(f::PrimitiveCall) = get_body(mapp(f))
function get_op_name(f::Conjugate) 
    is_creation(f) || error("$(f) is no a field operator")
    get_op_name(get_body(f))
end

"""
The type of a fermionic state operator.
"""
struct FermionicState <: AbstractPCTType end

FermionicOperatorType() = MapType(VecType([FermionicState()]), FermionicState())
const FOT = FermionicOperatorType

FermionicFieldType() = MapType(N(), FOT())

partial_inference(::Type{FermionicFieldAnnihilation}, body) = MapType(VecType([N()]), FOT())
inference(n::FermionicFieldAnnihilation, _::TypeContext=TypeContext()) = set_type(n, MapType(VecType([N()]), FOT()))
# the inference for the creation is taken care of implicitly

"""
Vacuum expectation
"""

struct VacExp <: APN
    type::AbstractPCTType
    body::Composition
end


function reduce_vac(n::APN) 
    set_terms(n, map(reduce_vac, terms(n))...)
end
reduce_vac(n::TerminalNode) = n
reduce_vac(c::VacExp) = vac_exp(get_body(c))

partial_inference(::Type{VacExp}, body) = R()

function pretty(v::VacExp)
    operators = content(get_body(get_body(v)))
    return "⟨$(join(pretty.(operators), "∘"))⟩"
end

function vac_exp(c::Composition)
    terms = content(get_body(c))
    length(terms) == 0 && return constant(1)

    for i in 2:length(terms)
        left, right = terms[1:i-2], terms[i+1:end]
        t_1, t_2 = terms[i-1], terms[i]
        is_annihilation(t_1) && is_creation(t_2) || continue

        swapped = composite(left..., t_2, t_1, right...)
        remaining_ops = [left..., right...]
        commuted = mul(anti_commute(t_1, t_2), vac_exp(composite(remaining_ops...)))
        return add(commuted, mul(constant(-1), vac_exp(swapped)))
    end

    return constant(0)
end

vac_exp(::APN) = is_field_op ? constant(0) : error("vac_exp of non-operators is not supported.")

function anti_commute(a::APN, b::APN)
    #= @assert is_field_op(a) && is_field_op(b) =#
    println("matching name: ", get_op_name(a) == get_op_name(b))
    println("ordering: ", is_annihilation(a) == is_creation(b)) 
    get_op_name(a) == get_op_name(b) &&
        is_annihilation(a) == is_creation(b) || return constant(0)
    indices(t::PrimitiveCall) = content(args(t))
    indices(t::Conjugate) = indices(get_body(t))
    return delta(indices(a)..., indices(b)..., constant(1))
end

#= function anti_commute(a::PrimitiveCall, b::PrimitiveCall)
    get_body(mapp(a)) == get_body(mapp(b)) || return constant(0)
    i, j = first(content(args(a))), first(content(args(b)))
    return delta(i, j, constant(1))
end

function vac_exp(c::PrimitiveCall)
    exp_func = mapp(c)
    isa(exp_func, Var) && name(exp_func) == :vac_exp || return primitive_call(exp_func, map(vac_exp, args(c))...)

    vac_references..., op = args(c)
    new_anihilators = map(var, new_symbol(c; num=length(c), symbol=:_c), get_type.(vac_references))

    for (r, n) in zip(vac_references, new_anihilators)
        if isa(r, Conjugate)
            r = get_body(r)
            n = conjugate(n)
        end

        op = subst(op, r, n)
    end

end



function neighbor(c::Composition; settings=default_settings)
    result = NeighborList()
    terms = content(get_body(c))
    length(terms) == 1 && return result
    settings[:wick] || return result

    for i in 2:length(terms)
        left, right = terms[1:i-2], terms[i+1:end]
        t_1, t_2 = terms[i-1], terms[i]
        isa(t_2, Conjugate) && !isa(t_1, Conjugate) &&
            get_type(get_body(t_2)) == FermionicFieldType() &&
            get_type(get_body(t_1)) == FermionicFieldType() || continue


        swapped = composite(left..., t_2, t_1, right...)
        commuted = mul(anti_commute(t_1, t_2), composite(left..., right))

        push!(result, add(commuted, mul(constant(-1), swapped)); dired=true, name="Wick rewrite")
        break
    end
    append!(result, sub_neighbors(c; settings=settings))
    return result
end

function vacuum_exp_neighbor(c::PrimitiveCall; settings=default_settings)
    result = NeighborList()
    exp_func = mapp(c)
    isa(exp_func, Var) && name(exp_func) == :vac_exp || return result

    vac_references..., op = args(c)


end =#
