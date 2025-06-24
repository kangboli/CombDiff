using LaTeXStrings, Crayons.Box, Crayons
export pretty, indent, verbose, latex, custom_print_settings!

print_settings = Dict(
    :color => true,
    :unicode => false
)

print_colors_defaults = Dict(
    :map => CYAN_FG,
    :product_type => MAGENTA_FG,
    :primitivecall => GREEN_FG,
    :hidden => Crayon(underline=true),
    :constructor => Crayon(foreground=(10, 190, 170))
)

print_color = print_colors_defaults

function custom_print_settings!(custom...)
    for (s, b) in custom
        s in keys(print_settings) || error("$(s) is not an option")
        print_settings[s] == b || @info "updating $(s) to $(b)"
        print_settings[s] = b
    end

    if print_settings[:color]
        CombDiff.print_color = print_colors_defaults
    else
        CombDiff.print_color = Dict(k => identity for (k, _) in print_colors_defaults)
    end
    return nothing
end


function indent(s::Any)
    contains(s, "\n") || return "    $(s)"
    join(indent.(split(s, "\n")), "\n")
end

function latex_indent(s::Any)
    contains(s, "\\\\") || return "\\quad " * s
    join(latex_indent.(split(s, "\\\\")), "\\\\")
end

Base.contains(s::Crayons.CrayonWrapper, n::String) = any(t -> contains(t, n), s.v)

verbose(t::MapType) = "[$(verbose(get_bound_type(t)))->$(verbose(get_body_type(t)))]"

verbose(v::VecType) = "$(join(verbose.(get_content_type(v)), "×"))"

verbose(::UndeterminedPCTType) = "?"

verbose(::T) where {T<:ElementType} = string(T)
verbose(t::APN) = pretty(t)

function verbose(d::Domain)
    name = haskey(meta(d), :name) ? meta(d)[:name] : ""
    "$(name)[$(verbose(lower(d))), $(verbose(upper(d)))]"
end

function pretty(m::AbstractMap, typed=false)
    #= range_str(range::PCTVector) = isempty(range) ? "" : " ∈ ($(pretty(range)))" =#
    params = typed ? map(v -> "$(pretty(v))::$(pretty(get_type(v)))", content(get_bound(m))) :
             map(v -> "$(pretty(v))", content(get_bound(m)))
    result = "($(join(params, ", "))) -> $(pretty(get_body(m)))"
    return cbi_applicable(get_type(m)) ? "[$(result)]" : result
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
    var_str = replace("$(name(v))", "__dot__" => ".")

    v_type = get_type(v)
    if startswith(string(name(v)), "__")
        if isa(v_type, ProductType)
            return "(;$(join(map((n, t) -> "$(string(n))" ,get_names(v_type), get_content_type(v_type)), ", ")))"
        else
            return print_color[:hidden](lstrip(var_str, '_'))
        end
    end

    if isa(v_type, MapType)
        return print_color[:map](var_str)
    elseif isa(v_type, ProductType)
        return print_color[:product_type](var_str)
    else
        return var_str
    end
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

#= pretty(c::Call) = "($(pretty(mapp(c))))($(pretty(args(c), false)))" =#

latex(c::Call) = "($(latex(mapp(c))))($(latex(args(c))))"

verbose(c::Call) = "($(pretty(mapp(c))))($(verbose(args(c))))::$(pretty(get_type(c)))"

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
pretty(p::PrimitivePullback) = "P($(pretty(get_body(p))))"

latex(p::AbstractPullback) = "\\mathcal{P}($(latex(get_body(p))))"

verbose(p::T) where {T<:AbstractPullback} = "$(T)($(pretty(get_body(p))))::$(pretty(get_type(p)))"


function pretty(s::Sum)
    bound_string = join(map(pretty, content(get_bound(s))), ", ")
    "sum(($(bound_string)) -> $(pretty(get_body(s))))"
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
    indent("$(verbose(get_body(s)))") *
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

pretty(m::Mul) = "$(join(pretty.(sort(content(get_body(m)),by=is_negative,rev=true)), "*"))"

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

function pretty(p::ParametricVar)
    return "$(pretty(mapp(p))){$(pretty(args(p), false))}"
end

function pretty(p::AbstractCall)

    mapp_str = (isa(mapp(p), Var) || isa(mapp(p), AbstractPullback)) ? pretty(mapp(p)) : "($(pretty(mapp(p))))"
    "$(mapp_str)($(pretty(args(p), false)))"
end

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

verbose(p::PrimitiveCall) = "$(print_color[:constructor](pretty(mapp(p))))($(verbose(args(p), false)))::$(pretty(get_type(p)))"

function pretty(p::PrimitiveCall)
    #= if isa(mapp(p), AbstractPullback) && last(args(p)) == constant(1)
        return "grad($(pretty(get_body(mapp(p)))))($(pretty(args(p)[1:end-1], false)))"
    end =#
    if isa(get_type(p), ProductType) && isa(mapp(p), Constructor) && get_typename(get_type(p)) == :__anonymous
        return "(;$(pretty(args(p), false)))"
    end

    if isa(get_type(mapp(p)), ProductType)
        @assert length(args(p)) == 1
        @assert isa(first(args(p)), Constant)
        prod_type = get_type(mapp(p))

        startswith(string(get_typename(get_type(mapp(p)))), "__") &&
            return print_color[:product_type](string(get_names(prod_type)[get_body(first(args(p)))]))
        return "$(pretty(mapp(p))).$(get_names(prod_type)[get_body(first(args(p)))])"
    end

    return "$(print_color[:primitivecall](pretty(mapp(p))))($(pretty(args(p), false)))"
end


pretty(c::Constant) = is_negative(c) ? "($(get_body(c)))" : "$(get_body(c))"
latex(c::Constant) = pretty(c)

verbose(c::Constant) = "$(get_body(c))::$(pretty(get_type(c)))"

function pretty(v::PCTVector, paren=true)
    terms = (t -> isa(t, PCTVector) ? pretty(t, true) : pretty(t)).(content(v))
    result = join(terms, ", ")
    return paren ? "tuple($(result))" : "$(result)"
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

function pretty(l::Let)
    "let \n$(join(map((f, a) -> indent("$(pretty(f)) $(isa(f, Copy) ? "=" : ":=") $(pretty(a))"), get_bound(l), args(l)), "\n"))\n$(indent(pretty(get_body(l))))\nend"
end
pretty(l::Mutate) = "mut \n$(join(map((f, a) -> indent("$(pretty(f)) = $(pretty(a))"), get_bound(l), args(l)), "\n"))\n$(indent(pretty(get_body(l))))\nend"
#= pretty(l::Let) = "let \n$(join(map((f, a) -> indent("$(pretty(f)) = $(pretty(a))"), get_bound(l), args(l)), "\n"))\n$(indent(pretty(get_body(l))))\nend" =#

function verbose(l::Let)
    "let \n$(join(map((f, a) -> indent("$(verbose(f)) $(isa(f, Copy) ? "=" : ":=") $(verbose(a))"), get_bound(l), args(l)), "\n"))\n$(indent(verbose(get_body(l))))\nend"
end
function latex(l::Let, paren=true)
    inner_str = if isa(get_body(l), Let)
        latex(get_body(l), false)
    else
        latex_indent(latex(get_body(l)))
    end

    bound_str = join(map((f, a) -> latex_indent("$(latex(f)) $(isa(f, Copy) ? "=" : ":=") $(latex(a))"), get_bound(l), args(l)), "\\\\")

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
    "$(pretty(get_body(c)))"
end

function latex(c::Copy)
    "\\$(latex(get_body(c)))"
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

function pretty(v::AbstractVecType)
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
pretty(f::Fold) = "∧(($(join(pretty.(get_bound(f)), ","))), $(pretty(get_body(f))))"
verbose(f::Fold) = "∧($(verbose(get_bound(f))), $(pretty(get_body(f))))"


pretty(f::Splat) = "$(pretty(get_body(f)))..."


function pretty(p::ParametricMap)
    "{$(join(pretty.(get_bound(p)), ", "))}$(pretty(get_body(p)))"
end

function verbose(p::ParametricMap)
    "{$(join(verbose.(get_bound(p)), ", "))}$(verbose(get_body(p)))"
end

function verbose(p::ParametricMapType)
    "{$(join(pretty.(get_params(p)), ","))}$(pretty(get_param_body(p)))"
end

function verbose(t::MultiType)
    "multi"
end

function pretty(s::FermionicState)
    "ℋ"
end

function pretty(d::Dot)
    return "$(pretty(get_body(d))).$(get_field(d))"
end

function pretty(p::ProductType)
    typename_str = startswith(string(get_typename(p)), "__") ? "_" : string(get_typename(p))
    "$(typename_str)($(join(["$(pretty(n))::$(pretty(t))" for (n, t) in zip(get_names(p), get_content_type(p))], " * ")))"
end

function verbose(p::ProductType)
    typename_str = startswith(string(get_typename(p)), "__") ? "_" : string(get_typename(p))
    "$(typename_str)($(join(["$(pretty(n))::$(verbose(t))" for (n, t) in zip(get_names(p), get_content_type(p))], " * ")))"
end

function pretty(c::Constructor)
    print_color[:constructor]("$(get_body(c))")
end

function pretty(p::ParametricProductType)

    "{$(join(pretty.(get_params(p)), ","))}$(pretty(get_param_body(p)))"
end

function pretty(g::Grad)
    "grad($(pretty(get_body(g))))"
end

function pretty(f::FixedPoint)
    "fixed($(pretty(get_body(f))))"
end

#= function pretty(f::Jacobian)
    "jacobian($(pretty(get_body(f))))"
end =#

function pretty(p::Pushforward)
    "pushforward($(pretty(get_body(p))))"
end
