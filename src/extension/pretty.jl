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
verbose(t::APN) = pretty(t)

function verbose(d::Domain)
    name = haskey(meta(d), :name) ? meta(d)[:name] : ""
    "$(name)[$(pretty(lower(d))), $(pretty(upper(d)))]"
end

function pretty(m::Map, typed=false)
    #= range_str(range::PCTVector) = isempty(range) ? "" : " ∈ ($(pretty(range)))" =#
    params = typed ? map(v -> "$(pretty(v))::$(pretty(get_type(v)))", content(get_bound(m))) :
             map(v -> "$(pretty(v))", content(get_bound(m)))
    "($(join(params, ", "))) -> $(pretty(get_body(m)))"
end

function latex(m::Map)
    #= range_str(range::PCTVector) = isempty(range) ? "" : " ∈ \\left($(latex(range))\\right)" =#
    params = map(v -> "$(latex(v))", content(get_bound(m)))
    params = length(get_bound(m)) == 1 ? first(params) : "($(join(params, ", ")))"
    if isa(get_body(m), PCTVector)
        return "$(params) \\mapsto $(latex(get_body(m), true))"
    else
        return "$(params) \\mapsto $(latex(get_body(m)))"
    end
end

function verbose(m::Map)
    #= range_str(range::PCTVector) = isempty(range) ? "" : " ∈ ($(pretty(range)))" =#
    params = map(v -> "$(verbose(v)))", content(get_bound(m)))
    "($(join(params, ", ")))->\n" *
    "$(indent(verbose(get_body(m))))\n" *
    "::$(verbose(get_type(m)))"
end

function pretty(v::Var)
    replace("$(name(v))", "__dot__" => ".")
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
        return "\\mathtt{$(components[1])}$(rest)"
    elseif name(v) == :∞
        return "\\infty"
    elseif occursin("_", string(name(v)))
        start, rest... = split(string(name(v)), "_")
        return "$(start)_{$(join(rest, ","))}"
    else
        return "$(name(v))"
    end
end

verbose(v::Var) = "$(pretty(v))::$(verbose(get_type(v)))"

pretty(c::Call) = "($(pretty(mapp(c))))($(pretty(args(c), false)))"

latex(c::Call) = "($(latex(mapp(c))))($(latex(args(c))))"

verbose(c::Call) = "($(pretty(mapp(c))))($(pretty(args(c))))::$(pretty(get_type(c)))"

function pretty(c::Conjugate)

    function conj_symbol(t::MapType)
        t == FOT() && return "⁺"
        get_body_type(t) == C() && return "⁺"
        return "ᵀ"
    end
    conj_symbol(::ElementType) = "'"
    interior = pretty(get_body(c))
    if isa(get_body(c), Map) || isa(get_body(c), Composition)
        interior = "($(interior))"
    end

    return "$(interior)$(conj_symbol(get_type(get_body(c))))"
end


function latex(c::Conjugate)
    get_body(c) == nabla() &&
        return "∇⋅"

    function conj_symbol(t::MapType)
        t == FOT() && return "\\dagger"
        get_body_type(t) == C() && return "\\dagger"
        return "T"
    end
    conj_symbol(::ElementType) = "*"
    interior = latex(get_body(c))
    if isa(get_body(c), Map) || isa(get_body(c), Composition)
        interior = "($(interior))"
    end

    return "$(interior)^{$(conj_symbol(get_type(get_body(c))))}"
end

verbose(c::Conjugate) = "$(pretty(get_body(c)))'::$(pretty(get_type(c)))"

pretty(p::T) where {T<:AbstractPullback} = "𝒫($(pretty(get_body(p))))"

latex(p::AbstractPullback) = "\\mathcal{P}($(latex(get_body(p))))"

verbose(p::T) where {T<:AbstractPullback} = "$(T)($(pretty(get_body(p))))::$(pretty(get_type(p)))"


function pretty(s::Sum)
    bound_string = join(map(verbose, content(get_bound(s))), ",")
    "∑(($(bound_string)), $(pretty(get_body(s))))"
end

function latex(s::Sum, paren=false)
    indices = []
    while isa(s, Sum)
        append!(indices, content(get_bound(s)))
        s = get_body(s)
    end
    differential(v::APN) = "\\mathrm{d} $(latex(v))"
    if all(i -> type_based(get_type(i), R()), indices)
        sum_str = "\\int"
        d_str = join(differential.(indices), " ")
    else
        sum_str = "\\sum"
        d_str = ""
    end
    all_sums = join(map(i -> "$(sum_str)_{$(latex(i)) = $(latex(lower(get_type(i))))}^{$(latex(upper(get_type(i))))}", indices), "")
    result = "$(all_sums) $(latex(s)) $(d_str)"
    #= result = "$(sum_str)_{$(join(latex.(indices),","))}$(latex(s))" =#
    return paren ? "($(result))" : result
end

function verbose(s::Sum)
    "∑(($(verbose(get_bound(s)))),\n" *
    indent("$(pretty(get_body(s)))") *
    "\n)::$(pretty(get_type(s)))"
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
    indent("$(pretty(get_body(i)))") *
    "\n)::$(pretty(get_type(i)))"
end

pretty(s::Prod) = "∏(($(pretty(get_bound(s)))), $(pretty(get_body(s))))"

latex(s::Prod) = "\\prod_{$(latex(get_bound(s)))} $(latex(get_body(s))))"

verbose(s::Prod) = invoke(verbose, Sum, s)

delta_symbol(::Type{Delta}, latex=false) = latex ? "\\delta" : "δ"
delta_symbol(::Type{DeltaNot}, latex=false) = latex ? "\\top" : "δ̸"
delta_symbol(::Type{Indicator}, latex=false) = latex ? "\\mathbb{I}" : "𝕀"

function pretty(d::T) where {T<:AbstractDelta}
    "$(delta_symbol(T))($(pretty(lower(d))), $(pretty(upper(d))), $(pretty(last(content(d)))))"
end

function latex(d::T) where {T<:AbstractDelta}
    "$(delta_symbol(T, true))_{$(latex(lower(d)))}^{$(latex(upper(d)))}($(latex(last(content(d)))))"
end


function verbose(d::T) where {T<:AbstractDelta}
    "$(delta_symbol(T))($(pretty(lower(d))), $(pretty(upper(d))),\n" *
    indent("$(pretty(last(content(d)))))::$(pretty(get_type(d)))")
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
        return "$(join(latex_str.(nominators), "\\cdot ")) / 
        $(join(latex_str.(denominators), "\\cdot "))"
    end
end

function verbose(m::Mul)
    "(*\n" *
    indent("$(join(pretty.(content(get_body(m))), ",\n"))") *
    "\n)::$(pretty(get_type(m)))"
end


function pretty(m::Add)
    return "($(join(map(t->pretty(t), content(get_body(m))), "+")))"
    #= signed = map(t -> is_negative(t) ? pretty(t) : "+$(pretty(t))", content(get_body(m)))
    return "($(strip(join(signed, ""), '+')))" =#
end

function latex(m::Add)
    return "($(join(map(t->latex(t), content(get_body(m))), "+")))"
    #= signed = map(t -> is_negative(t) ? latex(t) : "+$(latex(t))", content(get_body(m)))
    return "($(strip(join(signed, ""), '+')))" =#
end

function verbose(a::Add)
    "(+\n" *
    indent("$(join(pretty.(content(get_body(a))), ",\n"))") *
    "\n)::$(pretty(get_type(a)))"
end

pretty(p::PrimitiveCall) = "($(pretty(mapp(p))))($(pretty(args(p), false)))"

function latex(p::PrimitiveCall)
    if isa(mapp(p), AbstractPullback) && last(args(p)) == constant(1)
        return "\\nabla ($(latex(get_body(mapp(p)))))($(latex(args(p)[1:end-1])))"
    end

    bound_types = get_content_type(get_bound_type(get_type(mapp(p))))
    map_str = latex(mapp(p))
    #= if isa(mapp(p), Conjugate)
        map_str = "\\left($(map_str)\\right)"
    end =#

    if all(a -> isa(a, ElementType) && base(a) == N(), bound_types) && length(bound_types) > 0
        map_strs = split(map_str, "_")
        if length(map_strs) == 1
            return "$(map_strs[1])_{$(latex(args(p)))}"
        else
            return "$(map_strs[1])_{$(map_strs[2]), $(latex(args(p)))}"
        end
    else
        return "$(map_str)\\left($(latex(args(p)))\\right)"
    end
end

verbose(p::PrimitiveCall) = "$(pretty(mapp(p)))($(pretty(args(p))))::$(pretty(get_type(p)))"


pretty(c::Constant) = is_negative(c) ? "($(get_body(c)))" : "$(get_body(c))"
latex(c::Constant) = pretty(c)

verbose(c::Constant) = "$(get_body(c))::$(pretty(get_type(c)))"

function pretty(v::PCTVector, paren=true)
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
    print(io, latexstring("\\begin{array}{l} $(latex(m)) \\end{array}"))
end

function Base.show(io::IO, ::MIME"text/plain", m::APN)
    print(io, pretty(m))
end

function Base.show(io::IO, ::MIME"text/plain", m::AbstractPCTType)
    print(io, pretty(m))
end

pretty(n::Negate) = "-$(pretty(get_body(n)))"

pretty(m::Monomial) = "($(pretty(base(m))))^($(pretty(power(m))))"
verbose(m::Monomial) = "($(pretty(base(m)))^$(pretty(power(m))))::$(pretty(get_type(m)))"
function latex(m::Monomial)
    "\\left($(latex(base(m)))\\right)^{$(latex(power(m)))}"
end

pretty(l::Let) = "let \n$(join(map((f, a) -> indent("$(pretty(f)) = $(pretty(a))"), get_bound(l), args(l)), "\n"))\n$(indent(pretty(get_body(l))))\nend"
pretty(l::Mutate) = "mut \n$(join(map((f, a) -> indent("$(pretty(f)) = $(pretty(a))"), get_bound(l), args(l)), "\n"))\n$(indent(pretty(get_body(l))))\nend"
#= pretty(l::Let) = "let \n$(join(map((f, a) -> indent("$(pretty(f)) = $(pretty(a))"), get_bound(l), args(l)), "\n"))\n$(indent(pretty(get_body(l))))\nend" =#

function verbose(l::Let)
    "let $(join(map((f, a) -> indent("$(verbose(f)) = $(pretty(a))"), get_bound(l), args(l)), "\n"))\n$(indent(pretty(get_body(l))))\nend"
end
function latex(l::Let, paren=true)
    inner_str = if isa(get_body(l), Let)
        latex(get_body(l), false)
    else
        latex_indent(latex(get_body(l)))
    end

    bound_str = join(map((f, a) -> latex_indent("$(latex(f)) = $(latex(a))"), get_bound(l), args(l)), "\\\\")

    if paren
        "\\mathrm{let}\\\\$(bound_str)\\\\$(inner_str)\\\\\\mathrm{end}"
    else
        return "$(bound_str)\\\\$(inner_str)"
    end
end


function pretty(c::Composition)
    isempty(content(get_body(c))) && return ":I"
    join(map(f -> pretty(f), content(get_body(c))), "∘")
end

function pretty(c::RevComposition)
    join(map(f -> pretty(f), reverse(content(get_body(c)))), " ▷\n")
end

function latex(c::Composition)
    join(map(f -> latex(f), content(get_body(c))), " \\circ ")
end

function latex(c::RevComposition)
    join(map(f -> latex(f), reverse(content(get_body(c)))), "\\triangleright \\\\")
end

function pretty(c::Copy)
    "%$(pretty(get_body(c)))"
end

function latex(c::Copy)
    "\\%$(latex(get_body(c)))"
end


# This function is only for the purpose of displaying the negative sign.
is_negative(n::APN) = false
is_negative(n::Mul) = any(t -> is_negative(t), get_body(n))
is_negative(n::Constant) = get_body(n) < 0
is_negative(n::ScalarTensorProduct) = is_negative(n.scalar)

function pretty(n::Exp)
    "exp($(pretty(get_body(n))))"
end

function latex(n::Exp)
    "\\exp\\left($(latex(get_body(n)))\\right)"
end

function verbose(n::Exp)
    "exp($(pretty(get_body(n))))::$(pretty(get_type(n)))"
end

function pretty(n::Log)
    "log($(pretty(get_body(n))))"
end

function latex(n::Log)
    "\\log\\left($(latex(get_body(n)))\\right)"
end

function verbose(n::Log)
    "log($(pretty(get_body(n))))::$(pretty(get_type(n)))"
end

function pretty(d::ParametricDomain)
    "{$(join(pretty.(get_params(d)), ", "))} ->> $(pretty(get_param_body(d)))"
end

function pretty(d::Domain)
    "$(pretty(base(d))):[$(pretty(lower(d))), $(pretty(upper(d)))]"
end

function pretty(d::ParametricMapType)
    "{$(join(pretty.(get_params(d)), ", "))} ->> $(pretty(get_param_body(d)))"
end

function pretty(m::MapType)
    "[$(pretty(get_bound_type(m)))->$(pretty(get_body_type(m)))]"
end

function pretty(v::VecType)
    "$(join(pretty.(get_content_type(v)), "×"))"
end

pretty(::T) where {T<:ElementType} = string(T)

pretty(f::FermiScalar) = ":I($(pretty(get_body(f))))"
latex(f::FermiScalar) = "\\mathbf{I}($(latex(get_body(f))))"

function pretty(v::VacExp)
    "⟨$(pretty(get_body(v)))⟩"
end

function latex(v::VacExp)
    "\\langle $(latex(get_body(v))) \\rangle"
end


function pretty(f::FieldOperators)
    ":$(get_body(f))"
end

function latex(f::FieldOperators)
    "\\mathbf{$(get_body(f))}"
end

function latex(i::Indicator)
    "\\mathbb{I}_{$(latex(lower(i))) \\leq $(latex(upper(i)))} $(latex(get_body(i)))"
end

pretty(s::Union{Symbol,Number}) = string(s)

pretty(d::IntDiv) = "div($(pretty(get_nom(d))), $(pretty(get_denom(d))))"
latex(d::IntDiv) = "div($(latex(get_nom(d))),$(latex(get_denom(d))))"
pretty(f::Fold) = "∧($(pretty(get_bound(f))), $(pretty(get_body(f))))"
verbose(f::Fold) = "∧($(verbose(get_bound(f))), $(pretty(get_body(f))))"


pretty(f::Splat) = "$(pretty(get_body(f)))..."


function pretty(p::ParametricMap)
    "{$(join(pretty.(get_bound(p)), ", "))}$(pretty(get_body(p), true))"
end

function verbose(p::ParametricMapType)
    "{$(join(pretty.(get_params(p))))}$(pretty(get_param_body(p)))"
end
