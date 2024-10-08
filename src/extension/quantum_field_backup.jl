
export FermiVacuum, f_annihilation, f_creation, vacuum_exp, normal_form, anti_commutator

base(t::ProductType) = t.base
power(t::ProductType) = t.power


#= hilbert_space() = MapType(VecType([R(), R(), R()]), C(), Dict(:name => :Hilbert)) =#

function f_creation(field::Symbol)
    return make_node(FermionicFieldCreation, field)
end


function f_annihilation(field::Symbol)
    return make_node(FermionicFieldAnnihilation, field)
end

function is_creation(c::PrimitiveCall)
    return isa(mapp(c), FermionicFieldCreation)
end

function anti_commutator(a::PrimitiveCall, b::PrimitiveCall)
    get_body(mapp(a)) == get_body(mapp(b)) || return constant(0)
    i, j = first(content(args(a))), first(content(args(b)))
    if get_type(i) == get_type(j)
        return delta(i, j, constant(1))
    else
        error("commutator of fields defined on different domains is not yet implemented")
    end

end

function vacuum_exp(n::APN)
    return set_content(n, map(c->vacuum_exp(c), content(n))...) 
end

vacuum_exp(n::TerminalNode) = n
vacuum_exp(n::Composition) = vacuum_exp(content(get_body(n)))

function vacuum_exp(operator_string::Vector)
    isempty(operator_string) && return constant(1)
    is_creation(first(operator_string)) && return constant(0)
    is_creation(last(operator_string)) || return constant(0)

    i = findfirst(is_creation, operator_string)
    swapped_string = copy(operator_string)

    tmp = swapped_string[i]
    swapped_string[i] = swapped_string[i-1]
    swapped_string[i-1] = tmp

    reduced_string = []
    for (j, s) in enumerate(reduced_string)
        j == i - 1 && continue
        j == i && continue
        push!(reduced_string, s)
    end

    commutated = anti_commutator(swapped_string[i-1], swapped_string[i])

    delta_term = mul(commutated, vacuum_exp(reduced_string))

    return add(delta_term, mul(constant(-1), vacuum_exp(swapped_string)))
end

#=
function deserialize(operator_string::Vector)
    length(operator_string) == 1 && return first(operator_string)
    return call(first(operator_string), deserialize(operator_string[2:end]))
end

function deserialize_vac(operator_string::Vector)
    return deserialize([conjugate(FermiVacuum()), operator_string..., FermiVacuum()])
end

function normal_form(n::PrimitiveCall)
    operator_string = serialize(n)
    if first(operator_string) == conjugate(FermiVacuum()) &&
       last(operator_string) == FermiVacuum()
        return vacuum_exp(operator_string[1:end-1])
    end
    return normal_form(operator_string)
end =#
