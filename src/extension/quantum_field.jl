export annihilate, reduce_vac, vac_exp_rewrite, anti_commute, FOT, FField
using StyledStrings

"""
The fermionic operator as a value.
"""
struct FermionicFieldAnnihilation <: FieldOperators
    type::AbstractPCTType
    body::Symbol
end

annihilate(body::Symbol) = make_node(FermionicFieldAnnihilation, body)
function pretty(f::FermionicFieldAnnihilation)
    ":$(get_body(f))"
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

contains_name(f::FermionicFieldAnnihilation, s::Symbol)::Bool = false
free_and_dummy(::FermionicFieldAnnihilation) = Set{Var}(), Set{Var}()

"""
The type of a fermionic state operator.
"""
struct FermionicState <: AbstractPCTType end

FermionicOperatorType() = MapType(VecType([FermionicState()]), FermionicState())
const FOT = FermionicOperatorType
FField() = MapType(VecType([N()]), FOT())

type_based(::FermionicState, ::ElementType) = false

FermionicFieldType() = MapType(N(), FOT())

partial_inference(::Type{FermionicFieldAnnihilation}, body) = MapType(VecType([N()]), FOT())
inference(n::FermionicFieldAnnihilation, _::TypeContext=TypeContext()) = set_type(n, MapType(VecType([N()]), FOT()))
# the inference for the creation is taken care of implicitly

function subst_type(n::FermionicState, ::S, ::R, replace_dummy=false) where {S <: APN, R <: APN}
    return n
end

"""
Vacuum expectation
"""


function reduce_vac(n::APN) 
    set_terms(n, map(reduce_vac, terms(n))...)
end
reduce_vac(n::TerminalNode) = n
reduce_vac(c::VacExp) = vac_exp_rewrite(get_body(c))

partial_inference(::Type{VacExp}, body) = R()

function pretty(v::VacExp)
    #= operators = content(get_body(get_body(v)))
    return "⟨$(join(pretty.(operators), "∘"))⟩" =#
    "⟨$(pretty(get_body(v)))⟩" 
end

function vac_exp_rewrite(c::Composition)
    terms = content(get_body(c))
    length(terms) == 0 && return constant(1)

    for i in 2:length(terms)
        left, right = terms[1:i-2], terms[i+1:end]
        t_1, t_2 = terms[i-1], terms[i]
        is_annihilation(t_1) && is_creation(t_2) || continue

        swapped = composite(left..., t_2, t_1, right...)
        remaining_ops = [left..., right...]
        commuted = mul(anti_commute(t_1, t_2), vac_exp_rewrite(composite(remaining_ops...)))
        return add(commuted, mul(constant(-1), vac_exp_rewrite(swapped)))
    end

    return constant(0)
end

vac_exp_rewrite(::APN) = is_field_op ? constant(0) : error("vac_exp of non-operators is not supported.")

function anti_commute(a::APN, b::APN)
    #= @assert is_field_op(a) && is_field_op(b) =#
    get_op_name(a) == get_op_name(b) &&
        is_annihilation(a) == is_creation(b) || return constant(0)
    indices(t::PrimitiveCall) = content(args(t))
    indices(t::Conjugate) = indices(get_body(t))
    return delta(indices(a)..., indices(b)..., constant(1))
end


#= comp_expansion(t::TerminalNode) = t
function comp_expansion(t::APN) 
    return set_terms(t, map(comp_expansion, terms(t))...)
end


function comp_expansion(c::Composition)
    terms = content(get_body(c))

    for i in 1:length(terms)
        left, right = terms[1:i-1], terms[i+1:end]
        t = terms[i]
        isa(t, Add) || continue
        return add(map(a->comp_expansion(composite(left..., a, right...)), get_body(t))...)
    end
    return c
end
 =#
function trunc_hash(n::FermionicFieldAnnihilation, h::UInt, ::Int)
    return hash(get_body(n), h) + FermionicFieldAnnihilation.hash
end
