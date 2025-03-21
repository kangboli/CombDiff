using Combinatorics
export annihilate, reduce_vac, vac_exp_rewrite, anti_commute, FOT, FField, FermionicFieldAnnihilation, FermiScalar, fermi_scalar

"""
The fermionic operator as a value.
"""
struct FermionicFieldAnnihilation <: FieldOperators
    type::AbstractPCTType
    body::Symbol
end

annihilate(body::Symbol) = make_node(FermionicFieldAnnihilation, body)


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


partial_inference(::Type{FermiScalar}, body) = FOT()
inference(s::FermiScalar, _::TypeContext=TypeContext()) = set_type(s, FOT())

# the inference for the creation is taken care of implicitly

function subst_type(n::FermionicState, ::S, ::R, replace_dummy=false) where {S<:APN,R<:APN}
    return n
end


function subst(n::FermionicFieldAnnihilation, ::S, ::R, replace_dummy=false) where {S<:APN,R<:APN}
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


function vac_exp_rewrite(c::Composition)
    terms = content(get_body(c))

    length(terms) == 0 && return constant(1)
    is_annihilation(last(terms)) && return constant(0)
    is_creation(first(terms)) && return constant(0)

    for i in 2:length(terms)
        left, right = terms[1:i-2], terms[i+1:end]
        t_1, t_2 = terms[i-1], terms[i]
        is_annihilation(t_1) && is_creation(t_2) || continue

        swapped = composite(left..., t_2, t_1, right...)
        remaining_ops = [left..., right...]
        commuted = mul(anti_commute(t_1, t_2), vac_exp_rewrite(composite(remaining_ops...)))
        return subtract(commuted, vac_exp_rewrite(swapped))
    end

    return constant(0)
end

vac_exp_rewrite(n::APN) = is_field_op(n) ? constant(0) : error("vac_exp of non-operators is not supported.")
get_indices(t::PrimitiveCall) = content(args(t))
get_indices(t::Conjugate) = get_indices(get_body(t))

function anti_commute(a::APN, b::APN)
    #= @assert is_field_op(a) && is_field_op(b) =#
    get_op_name(a) == get_op_name(b) &&
        is_annihilation(a) == is_creation(b) || return constant(0)
    return delta(get_indices(a)..., get_indices(b)..., constant(1))
end

const Pairing = Vector{Pair{Int,Int}}

"""
    enumerate_pairings(as, adags)

Recursively enumerate all Wick contraction pairings.

- Return an empty vector iff there is no nonzero pairing.
- Base case is one creation and one annihilations.

`annihilations` and `creations` are get_indices. 
Both of them are in ascending order.
"""
function enumerate_pairings(as::Vector{Int}, adags::Vector{Int})
    length(as) == length(adags) || return Vector{Pairing}()
    @assert !isempty(as)
    (first(adags) < first(as) || last(adags) < last(as)) &&
        return Vector{Pairing}()

    length(as) == 1 && return [Pairing([first(as) => first(adags)])]
    a, rest_as... = as

    function sub_pairings(i)
        c, rest_adags = adags[i], adags[1:end.!=i]
        rest_pairings = enumerate_pairings(rest_as, rest_adags)
        isempty(rest_pairings) && return Vector{Pairing}()
        return map(p -> Pairing([a => c, p...]), rest_pairings)
    end

    return vcat(map(sub_pairings, 1:length(adags))...)
end

"""
    wick_sign(pairing)

Determine the sign of a Wick pairing.
(-1)^(#crossing)
"""
wick_sign(pairing::Vector{Pair{Int,Int}}) =
    prod([(a < c < b < d || c < a < d < b) ? -1 : 1
          for ((a, b), (c, d)) in combinations(pairing, 2)])

function merge_pairing(pairing_set_1, pairing_set_2)
    [Pairing(vcat(p, q)) for p in pairing_set_1 for q in pairing_set_2]
end

function wick_rewrite(c::Composition)
    terms = content(get_body(c))
    d = Dict()
    for (i, t) in enumerate(terms)
        n = get_op_name(t)
        haskey(d, n) || (d[n] = Vector{Int}() => Vector{Int}())
        is_annihilation(t) && push!(first(d[n]), i)
        is_creation(t) && push!(last(d[n]), i)
    end

    pairing_sets = Vector{Vector{Pairing}}()
    for k in keys(d)
        push!(pairing_sets, enumerate_pairings(first(d[k]), last(d[k])))
    end

    pairings = foldr(merge_pairing, pairing_sets)
    #= pairings = isempty(pairing_sets) ? Vector{Pairing}() : foldr(merge_pairing, pairing_sets) =#
    labels = get_indices.(terms)
    contract(p) = foldr(
        ((a, adag), inner) -> delta(labels[a]..., labels[adag]..., inner),
        p; init=constant(wick_sign(p)))

    return add(map(contract, pairings)...)
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

function contains_field(n::APN)
    any(contains_field, terms(n))
end

contains_field(n::TerminalNode) = false
contains_field(n::FermionicFieldAnnihilation) = true
