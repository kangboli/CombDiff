using LaTeXStrings
export pretty, indent, verbose, latex

function indent(s::AbstractString)
    contains(s, "\n") || return " "^4 * s
    join(indent.(split(s, "\n")), "\n")
end

verbose(t::MapType) = "[$(verbose(from(t)))->$(verbose(to(t)))]"

verbose(v::VecType) = "$(join(verbose.(content(v)), "×"))"

verbose(::UndeterminedPCTType) = "?"

verbose(::T) where T <: ElementType = string(T)

verbose(d::Domain) = "$(meta(d)[:name])"

# pretty(d::Domain) = "$(meta(d)[:name])"
#= function verbose(d::Domain)
    "$(pretty(d))::$(verbose(d.base))($(pretty(d.lower)), $(pretty(d.upper)))"
end =#


pretty(m::Map) = "($(pretty(ff(m)))) -> \n$(indent(pretty(fc(m))))"

function latex(m::Map) 
    params = latex(ff(m))
    params = length(ff(m)) == 1 ? params :
    "\\left($(params)\\right)"
    "$(params) \\to $(latex(fc(m)))"
end

function verbose(m::Map)
    "($(join(verbose(ff(m))))->\n"*
    "$(indent(verbose(fc(m))))\n"*
    "::$(verbose(get_type(m)))"
end

pretty(v::Var) = "$(name(v))"

latex(v::Var) = "$(name(v))"

verbose(v::Var) = "$(name(v))::$(verbose(get_type(v)))"

pretty(c::Call) = "($(pretty(mapp(c))))($(pretty(args(c))))"

latex(c::Call) = "\\left($(latex(mapp(c)))\\right)\\left($(latex(args(c)))\\right)"

verbose(c::Call) = "($(verbose(mapp(c))))($(verbose(args(c))))::$(verbose(get_type(c)))"

pretty(c::Conjugate) = "$(pretty(fc(c)))'"

latex(c::Conjugate) = "$(latex(fc(c)))^*"

verbose(c::Conjugate) = "$(verbose(fc(c)))'"    

pretty(p::Pullback) = "𝒫($(pretty(fc(p))))"

latex(p::Pullback) = "\\mathcal{P}\\left($(latex(fc(p)))\\right)"

verbose(p::Pullback) = "Pullback($(verbose(fc(p))))::$(verbose(get_type(p)))"

pretty(s::Sum) = "∑(($(pretty(ff(s)))), $(pretty(fc(s))))"

latex(s::Sum) = "\\sum_{$(latex(ff(s)))}\\left($(latex(fc(s)))\\right)"

function verbose(s::Sum)
    "∑(($(verbose(ff(s)))),\n" *
    indent("$(verbose(fc(s)))") * 
    "\n)::$(verbose(get_type(s)))"
end


pretty(s::Prod) = invoke(pretty, Sum, s)

latex(s::Prod) = invoke(latex, Sum, s)

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

pretty(m::Mul) = "$(join(pretty.(content(fc(m))), "*"))"

latex(m::Mul) = join(latex.(content(fc(m))), "\\cdot ")

function verbose(m::Mul)
    "(*\n"*
    indent("$(join(verbose.(content(fc(m))), ",\n"))") * 
    "\n)::$(verbose(get_type(m)))"
end


pretty(a::Add) = "($(join(pretty.(content(fc(a))), "+")))"

latex(m::Add) = "($(join(latex.(content(fc(m))), "+")))"

function verbose(a::Add)
    "(+\n"*
    indent("$(join(verbose.(content(fc(a))), ",\n"))") * 
    "\n)::$(verbose(get_type(a)))"
end

pretty(p::PrimitiveCall) = "$(pretty(mapp(p)))($(pretty(args(p))))"

function latex(p::PrimitiveCall) 
    if all(a->a==I(), content(from(get_type(mapp(p)))))
        "$(latex(mapp(p)))_{$(latex(args(p)))}"
    else
        "$(latex(mapp(p)))($(latex(args(p))))"
    end
end

verbose(p::PrimitiveCall) = "$(verbose(mapp(p)))($(verbose(args(p))))::$(verbose(get_type(p)))"


pretty(c::Constant) = "$(fc(c))"

latex(c::Constant) = "$(fc(c))"

verbose(c::Constant) = "$(fc(c))::$(verbose(get_type(c)))"

pretty(v::PCTVector) = join(pretty.(content(v)), ", ")

latex(v::PCTVector) = join(latex.(content(v)), ", ")

verbose(v::PCTVector) = join(verbose.(content(v)), ", ") 

function Base.show(io::IO, ::MIME"text/latex", m::APN) 
    print(io, latexstring(latex(m)))
end

function Base.show(io::IO, ::MIME"text/plain", m::APN) 
    print(io, pretty(m))
end

pretty(n::Negate) = "-$(pretty(fc(n)))"

