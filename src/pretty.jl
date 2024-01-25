using LaTeXStrings
export pretty, indent, verbose, latex

function indent(s::AbstractString)
    contains(s, "\n") || return " "^4 * s
    join(indent.(split(s, "\n")), "\n")
end

verbose(t::MapType) = "[$(verbose(from(t)))->$(verbose(content(t)))]"

verbose(v::VecType) = "$(join(verbose.(content(v)), "×"))"

verbose(::UndeterminedPCTType) = "?"

verbose(::T) where T <: ElementType = string(T)

verbose(d::Domain) = "$(meta(d)[:name])"

pretty(m::Map) = "($(pretty(ff(m)))) -> \n$(indent(pretty(fc(m))))"

function latex(m::Map) 
    params = latex(ff(m))
    params = length(ff(m)) == 1 ? params : "\\left($(params)\\right)"
    return "$(params) \\to $(latex(fc(m)))"
end

function verbose(m::Map)
    "($(join(verbose(ff(m))))->\n"*
    "$(indent(verbose(fc(m)))))\n"*
    "::$(verbose(get_type(m)))"
end

pretty(v::Var) = "$(name(v))"

latex(v::Var) = startswith(string(name(v)), "_") ? "\\mathbb{$(string(name(v))[2:end])}" : "$(name(v))"

verbose(v::Var) = "$(name(v))::$(verbose(get_type(v)))"

pretty(c::Call) = "($(pretty(mapp(c))))($(pretty(args(c))))"

latex(c::Call) = "\\left($(latex(mapp(c)))\\right)\\left($(latex(args(c)))\\right)"

verbose(c::Call) = "($(verbose(mapp(c))))($(verbose(args(c))))::$(verbose(get_type(c)))"

pretty(c::Conjugate) = "$(pretty(fc(c)))'"

conj_symbol(::MapType) = "\\dagger"
conj_symbol(::ElementType) = "*"

latex(c::Conjugate) = "$(latex(fc(c)))^{$(conj_symbol(get_type(fc(c))))}"

verbose(c::Conjugate) = "$(verbose(fc(c)))'"    

pretty(p::Pullback) = "𝒫($(pretty(fc(p))))"

latex(p::Pullback) = "\\mathcal{P}\\left($(latex(fc(p)))\\right)"

verbose(p::Pullback) = "Pullback($(verbose(fc(p))))::$(verbose(get_type(p)))"

pretty(p::PrimitivePullback) = "𝒫($(pretty(fc(p))))"

latex(p::PrimitivePullback) = "\\mathcal{P}\\left($(latex(fc(p)))\\right)"

verbose(p::PrimitivePullback) = "PrimitivePullback($(verbose(fc(p))))::$(verbose(get_type(p)))"

pretty(s::Sum) = "∑(($(pretty(ff(s)))), $(pretty(fc(s))))"

function latex(s::Sum) 
    indices = []
    while isa(s, Sum) 
        push!(indices, ff(s))
        s = fc(s)
    end
    "\\sum_{$(join(latex.(indices),","))}\\left($(latex(s))\\right)"
end

function verbose(s::Sum)
    "∑(($(verbose(ff(s)))),\n" *
    indent("$(verbose(fc(s)))") * 
    "\n)::$(verbose(get_type(s)))"
end

pretty(i::Integral) = "∫ $(pretty(fc(i))) d$(pretty(ff(i)))"

function latex(i::Integral)
    indices = []
    while isa(i, Integral) 
        push!(indices, ff(i))
        i = fc(i)
    end
    "\\int $(latex(i)) $(join((x->"\\mathrm{d}"*latex(x)).(indices), " "))"
end

function verbose(i::Integral)
    "∫(($(verbose(ff(i)))),\n" * 
    indent("$(verbose(fc(i)))") * 
    "\n)::$(verbose(get_type(i)))"
end

pretty(s::Prod) = "∏(($(pretty(ff(s)))), $(pretty(fc(s))))"

latex(s::Prod) = "\\prod_{$(latex(ff(s)))} $(latex(fc(s))))"

verbose(s::Prod) = invoke(verbose, Sum, s)

delta_symbol(::Type{Delta}, latex=false) = latex ? "\\delta" : "δ"
delta_symbol(::Type{DeltaNot}, latex=false) = latex ? "\\top" : "δ̸"

function pretty(d::T) where T <: AbstractDelta
    "$(delta_symbol(T))($(pretty(upper(d))), $(pretty(lower(d))), $(pretty(last(content(d)))))"
end

function latex(d::T) where T <: AbstractDelta
    "$(delta_symbol(T, true))_{$(latex(lower(d)))}^{$(latex(upper(d)))}$(latex(last(content(d))))"
end


function verbose(d::T) where T <: AbstractDelta
    "$(delta_symbol(T))($(verbose(upper(d))), $(verbose(lower(d))),\n"*
    indent("$(verbose(last(content(d)))))::$(verbose(get_type(d)))")
end

pretty(m::Mul) = "($(join(pretty.(content(fc(m))), "⋅")))"

function latex(m::Mul) 
    "$(join(latex.(sort(content(fc(m)), by=is_negative, rev=true)), "\\cdot "))"
end

function verbose(m::Mul)
    "(*\n"*
    indent("$(join(verbose.(content(fc(m))), ",\n"))") * 
    "\n)::$(verbose(get_type(m)))"
end


pretty(a::Add) = "($(join(pretty.(content(fc(a))), "+")))"

function latex(m::Add) 
    signed = map(t->is_negative(t) ? latex(t) : "+$(latex(t))", content(fc(m)))
    return "\\left($(strip(join(signed, ""), '+'))\\right)"
end

function verbose(a::Add)
    "(+\n"*
    indent("$(join(verbose.(content(fc(a))), ",\n"))") * 
    "\n)::$(verbose(get_type(a)))"
end

pretty(p::PrimitiveCall) = "$(pretty(mapp(p)))($(pretty(args(p))))"

function latex(p::PrimitiveCall) 
    if isa(mapp(p), AbstractPullback) && last(args(p)) == constant(1)
        return "\\nabla \\left($(latex(fc(mapp(p))))\\right)\\left($(latex(args(p)[1:end-1]))\\right)"
    end


    if all(a->a==I(), content(from(get_type(mapp(p)))))
        return "$(latex(mapp(p)))_{$(latex(args(p)))}"
    else
        return "$(latex(mapp(p)))\\left($(latex(args(p)))\\right)"
    end
end

verbose(p::PrimitiveCall) = "$(verbose(mapp(p)))($(verbose(args(p))))::$(verbose(get_type(p)))"


pretty(c::Constant) = "$(fc(c))"

latex(c::Constant) = "$(fc(c))"

verbose(c::Constant) = "$(fc(c))::$(verbose(get_type(c)))"

pretty(v::PCTVector) = join(pretty.(content(v)), ", ")

function latex(v::PCTVector) 
    terms = latex.(content(v))
    if any(t->length(t) > 30, terms)
        return "\\begin{bmatrix} $(join(terms, "\\\\")) \\end{bmatrix}"
    else
        return join(terms, ", ")
    end
end

verbose(v::PCTVector) = join(verbose.(content(v)), ", ") 

function Base.show(io::IO, ::MIME"text/latex", m::APN) 
    print(io, latexstring(latex(m)))
end

function Base.show(io::IO, ::MIME"text/plain", m::APN) 
    print(io, pretty(m))
end

pretty(n::Negate) = "-$(pretty(fc(n)))"

pretty(m::Monomial) = "$(pretty(base(m)))^($(pretty(power(m))))"
verbose(m::Monomial) = "($(verbose(base(m)))^$(verbose(power(m))))::$(get_type(m))"
latex(m::Monomial) = "$(latex(base(m)))^{$(latex(power(m)))}"

pretty(l::Let) = "let $(join(map((f, a) -> "$(pretty(f)) = $(pretty(a))", ff(l), args(l)), "\n"))\n$(pretty(fc(l)))\nend"
function verbose(l::Let)
    "let $(join(map((f, a) -> "$(verbose(f)) = $(verbose(a))", ff(l), args(l)), "\n"))\n$(verbose(fc(l)))\nend"
end
latex(l::Let) = "\\mathrm{let} \\; $(join(map((f, a) -> "$(latex(f)) = $(latex(a))", ff(l), args(l)), "\\\\"))\\\\$(latex(fc(l)))\\\\\\mathrm{end}"

# This function is only for the purpose of displaying the negative sign.
is_negative(n::APN) = false
is_negative(n::Mul) = any(t->is_negative(t), fc(n))
is_negative(n::Constant) = fc(n) < 0

