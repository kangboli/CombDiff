using LaTeXStrings
export pretty, indent, verbose, latex

function indent(s::AbstractString)
    contains(s, "\n") || return " "^4 * s
    join(indent.(split(s, "\n")), "\n")
end

function latex_indent(s::AbstractString)
    contains(s, "\\\\") || return "\\quad " * s
    join(latex_indent.(split(s, "\\\\")), "\\\\")
end

verbose(t::MapType) = "[$(verbose(get_bound_type(t)))->$(verbose(get_body_type(t)))]"

verbose(v::VecType) = "$(join(verbose.(get_content_type(v)), "×"))"

verbose(::UndeterminedPCTType) = "?"

verbose(::T) where {T<:ElementType} = string(T)

function verbose(d::Domain)
    name = haskey(meta(d), :name) ? name : ""
    "$(name)[$(pretty(lower(d))), $(pretty(upper(d)))]"
end

function pretty(m::Map)
    #= range_str(range::PCTVector) = isempty(range) ? "" : " ∈ ($(pretty(range)))" =#
    params = map(v -> "$(pretty(v))", content(get_bound(m)))
    "($(join(params, ", "))) -> \n$(indent(pretty(get_body(m))))"
end

function latex(m::Map)
    #= range_str(range::PCTVector) = isempty(range) ? "" : " ∈ \\left($(latex(range))\\right)" =#
    params = map(v -> "$(latex(v))", content(get_bound(m)))
    params = length(get_bound(m)) == 1 ? first(params) : "\\left($(join(params, ", "))\\right)"
    if isa(get_body(m), PCTVector)
        return "$(params) \\to $(latex(get_body(m), true))"
    else
        return "$(params) \\to $(latex(get_body(m)))"
    end
end

function verbose(m::Map)
    #= range_str(range::PCTVector) = isempty(range) ? "" : " ∈ ($(pretty(range)))" =#
    params = map(v -> "$(verbose(v)))", content(get_bound(m)))
    "($(join(params, ", "))->\n" *
    "$(indent(verbose(get_body(m)))))\n" *
    "::$(verbose(get_type(m)))"
end

function pretty(v::Var)
    "$(name(v))"
end

function latex(v::Var)
    if startswith(string(name(v)), "__")
        return "\\mathrm{$(string(name(v))[3:end])}"
    elseif startswith(string(name(v)), "_")
        components = split(string(name(v))[2:end], "_")
        if length(components) > 1
            rest = "_{$(join(components[2:end]))}"
        else
            rest = ""
        end
        return "\\mathbb{$(components[1])}$(rest)"
    else
        return "$(name(v))"
    end
end

verbose(v::Var) = "$(name(v))::$(verbose(get_type(v)))"

pretty(c::Call) = "($(pretty(mapp(c))))($(pretty(args(c))))"

latex(c::Call) = "\\left($(latex(mapp(c)))\\right)\\left($(latex(args(c)))\\right)"

verbose(c::Call) = "($(verbose(mapp(c))))($(verbose(args(c))))::$(verbose(get_type(c)))"

function pretty(c::Conjugate) 

    conj_symbol(t::MapType) = get_body_type(t) == C() ? "⁺" : "ᵀ" 
    conj_symbol(::ElementType) = "'"
    interior = pretty(get_body(c))
    if isa(c, Map)
        interior = "($(interior))"
    end

    return "$(interior)$(conj_symbol(get_type(get_body(c))))"
end


function latex(c::Conjugate)
    conj_symbol(t::MapType) = get_body_type(t) == C() ? "\\dagger" : "T"
    conj_symbol(::ElementType) = "*"
    interior = latex(get_body(c))
    if isa(get_body(c), Map)
        interior = "\\left($(interior)\\right)"
    end

    return "$(interior)^{$(conj_symbol(get_type(get_body(c))))}"
end

verbose(c::Conjugate) = "$(verbose(get_body(c)))'"

pretty(p::Pullback) = "𝒫($(pretty(get_body(p))))"

latex(p::Pullback) = "\\mathcal{P}\\left($(latex(get_body(p)))\\right)"

verbose(p::Pullback) = "Pullback($(verbose(get_body(p))))::$(verbose(get_type(p)))"

pretty(p::PrimitivePullback) = "𝒫($(pretty(get_body(p))))"

latex(p::PrimitivePullback) = "\\mathcal{P}\\left($(latex(get_body(p)))\\right)"

verbose(p::PrimitivePullback) = "PrimitivePullback($(verbose(get_body(p))))::$(verbose(get_type(p)))"

pretty(s::Sum) = "∑(($(pretty(get_bound(s)))), $(pretty(get_body(s))))"

function latex(s::Sum, paren=false)
    indices = []
    while isa(s, Sum)
        append!(indices, content(get_bound(s)))
        s = get_body(s)
    end
    sum_str = all(i->type_based(get_type(i), R()), indices) ? "\\int" : "\\sum"
    result = "$(sum_str)_{$(join(latex.(indices),","))}$(latex(s))"
    return paren ? "\\left($(result)\\right)" : result
end

function verbose(s::Sum)
    "∑(($(verbose(get_bound(s)))),\n" *
    indent("$(verbose(get_body(s)))") *
    "\n)::$(verbose(get_type(s)))"
end

pretty(i::Integral) = "∫ $(pretty(get_body(i))) d$(pretty(get_bound(i)))"

function latex(i::Integral)
    indices = []
    while isa(i, Integral)
        push!(indices, get_bound(i))
        i = get_body(i)
    end
    "\\int $(latex(i)) $(join((x->"\\mathrm{d}"*latex(x)).(indices), " "))"
end

function verbose(i::Integral)
    "∫(($(verbose(get_bound(i)))),\n" *
    indent("$(verbose(get_body(i)))") *
    "\n)::$(verbose(get_type(i)))"
end

pretty(s::Prod) = "∏(($(pretty(get_bound(s)))), $(pretty(get_body(s))))"

latex(s::Prod) = "\\prod_{$(latex(get_bound(s)))} $(latex(get_body(s))))"

verbose(s::Prod) = invoke(verbose, Sum, s)

delta_symbol(::Type{Delta}, latex=false) = latex ? "\\delta" : "δ"
delta_symbol(::Type{DeltaNot}, latex=false) = latex ? "\\top" : "δ̸"

function pretty(d::T) where {T<:AbstractDelta}
    "$(delta_symbol(T))($(pretty(upper(d))), $(pretty(lower(d))), $(pretty(last(content(d)))))"
end

function latex(d::T) where {T<:AbstractDelta}
    "$(delta_symbol(T, true))_{$(latex(lower(d)))}^{$(latex(upper(d)))}$(latex(last(content(d))))"
end


function verbose(d::T) where {T<:AbstractDelta}
    "$(delta_symbol(T))($(verbose(upper(d))), $(verbose(lower(d))),\n" *
    indent("$(verbose(last(content(d)))))::$(verbose(get_type(d)))")
end

pretty(m::Mul) = "$(join(pretty.(sort(content(get_body(m)),by=is_negative,rev=true)), "⋅"))"

function latex(m::Mul)
    negative_first = sort(content(get_body(m)), by=is_negative, rev=true)
    latex_str(m::APN) = latex(m)
    latex_str(m::Sum) = latex(m, true)

    d = group(t -> isa(t, Monomial) && power(t) == constant(-1), negative_first)
    nominators = get(d, false, [constant(1)])
    denominators = map(base, get(d, true, []))

    if isempty(denominators)
        return "$(join(latex_str.(negative_first), "\\cdot "))"
    else
        return "\\frac{$(join(latex_str.(nominators), "\\cdot "))}
        {$(join(latex_str.(denominators), "\\cdot "))}"
    end
end

function verbose(m::Mul)
    "(*\n" *
    indent("$(join(verbose.(content(get_body(m))), ",\n"))") *
    "\n)::$(verbose(get_type(m)))"
end


function pretty(m::Add)
    signed = map(t -> is_negative(t) ? pretty(t) : "+$(pretty(t))", content(get_body(m)))
    return "($(strip(join(signed, ""), '+')))"
end

function latex(m::Add)
    signed = map(t -> is_negative(t) ? latex(t) : "+$(latex(t))", content(get_body(m)))
    return "\\left($(strip(join(signed, ""), '+'))\\right)"
end

function verbose(a::Add)
    "(+\n" *
    indent("$(join(verbose.(content(get_body(a))), ",\n"))") *
    "\n)::$(verbose(get_type(a)))"
end

pretty(p::PrimitiveCall) = "$(pretty(mapp(p)))($(pretty(args(p))))"

function latex(p::PrimitiveCall)
    if isa(mapp(p), AbstractPullback) && last(args(p)) == constant(1)
        return "\\nabla \\left($(latex(get_body(mapp(p))))\\right)\\left($(latex(args(p)[1:end-1]))\\right)"
    end

    bound_types = get_content_type(get_bound_type(get_type(mapp(p))))
    map_str = latex(mapp(p))
    #= if isa(mapp(p), Conjugate)
        map_str = "\\left($(map_str)\\right)"
    end =#

    if all(a -> a == N(), bound_types) && length(bound_types) > 0
        return "$(map_str)_{$(latex(args(p)))}"
    else
        return "$(map_str)\\left($(latex(args(p)))\\right)"
    end
end

verbose(p::PrimitiveCall) = "$(verbose(mapp(p)))($(verbose(args(p))))::$(verbose(get_type(p)))"


pretty(c::Constant) = "$(get_body(c))"

latex(c::Constant) = "$(get_body(c))"

verbose(c::Constant) = "$(get_body(c))::$(verbose(get_type(c)))"

function pretty(v::PCTVector, paren=false)
    terms = (t -> isa(t, PCTVector) ? pretty(t, true) : pretty(t)).(content(v))
    result = join(terms, ", ")
    return paren ? "𝕧($(result))" : "$(result)"
end

function latex(v::PCTVector, paren=false)
    terms = (t -> isa(t, PCTVector) ? latex(t, true) : latex(t)).(content(v))
    # if any(t->length(t) > 50, terms) && length(terms) > 1
    #     return "\\begin{bmatrix} $(join(terms, "\\\\")) \\end{bmatrix}"
    # else
    # end
    result = join(terms, ", ")
    return paren ? "\\left($(result)\\right)" : result
end

function verbose(v::PCTVector, paren=false)
    terms = (t -> isa(t, PCTVector) ? verbose(t, true) : verbose(t)).(content(v))
    result = join(terms, ", ")
    return "𝕧($(result))"
end

function Base.show(io::IO, ::MIME"text/latex", m::APN)
    print(io, latexstring(latex(m)))
end

function Base.show(io::IO, ::MIME"text/plain", m::APN)
    print(io, pretty(m))
end

pretty(n::Negate) = "-$(pretty(get_body(n)))"

pretty(m::Monomial) = "($(pretty(base(m))))^($(pretty(power(m))))"
verbose(m::Monomial) = "($(verbose(base(m)))^$(verbose(power(m))))::$(get_type(m))"
function latex(m::Monomial)
    "\\left($(latex(base(m)))\\right)^{$(latex(power(m)))}"
end

pretty(l::Let) = "let \n$(join(map((f, a) -> indent("$(pretty(f)) = $(pretty(a))"), get_bound(l), args(l)), "\n"))\n$(indent(pretty(get_body(l))))\nend"
function verbose(l::Let)
    "let $(join(map((f, a) -> indent("$(verbose(f)) = $(verbose(a))"), get_bound(l), args(l)), "\n"))\n$(indent(verbose(get_body(l))))\nend"
end
latex(l::Let) = "\\mathrm{let}\\\\ $(join(map((f, a) -> latex_indent("$(latex(f)) = $(latex(a))"), get_bound(l), args(l)), "\\\\"))\\\\$(latex_indent(latex(get_body(l))))\\\\ \\mathrm{end}"

function pretty(c::Composition)
    join(map(f -> pretty(f), content(get_body(c))), "∘")
end

function latex(c::Composition)
    join(map(f -> latex(f), content(get_body(c))), "∘")
end

# This function is only for the purpose of displaying the negative sign.
is_negative(n::APN) = false
is_negative(n::Mul) = any(t -> is_negative(t), get_body(n))
is_negative(n::Constant) = get_body(n) < 0
is_negative(n::ScalarTensorProduct) = is_negative(n.scalar)

function pretty(c::FermionicFieldAnnihilation)
    return "$(get_body(c))̂"
end

function pretty(c::FermionicFieldCreation)
    return "$(get_body(c))̂'"
end

verbose(c::FermionicField) = pretty(c)

function latex(c::FermionicFieldAnnihilation)
    "\\hat{$(get_body(c))}"
end

function latex(c::FermionicFieldCreation)
    "\\hat{$(get_body(c))}^{\\dagger}"
end

function pretty(n::Exp)
    "exp($(pretty(get_body(n))))"
end

function latex(n::Exp)
    "\\exp\\left($(latex(get_body(n)))\\right)"
end

function verbose(n::Exp)
    "exp($(verbose(get_body(n))))::$(get_type(n))"
end

function pretty(n::Log)
    "log($(pretty(get_body(n))))"
end

function latex(n::Log)
    "\\log\\left($(latex(get_body(n)))\\right)"
end

function verbose(n::Log)
    "log($(verbose(get_body(n))))::$(get_type(n))"
end

