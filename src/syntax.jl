export parse_node, purge_line_numbers, @pct

macro pct(expr)
    #= space_nodes = filter(a->a.head == :macrocall, expr.args)
    spaces = map(parse_node, space_nodes) =#
    expr = purge_line_numbers(expr)
    top_level_nodes = map(parse_node, expr.args)
    return esc(:(
        begin
            $(top_level_nodes...)
        end
    ))
end

purge_line_numbers(e::Any) = e
function purge_line_numbers(expr::Expr)
    expr.args = filter(a -> !isa(a, LineNumberNode), expr.args)
    expr.args = map(purge_line_numbers, expr.args)
    return expr
end

function parse_node(::LineNumberNode)
    return nothing
end

function parse_node(n::Expr)
    n = purge_line_numbers(n)
    n.head == :macrocall && return parse_node(MapType, n)
    n.head == Symbol("->") && return parse_node(Map, n)
    if n.head == :call 
        func = n.args[1]
        (func == :ctr || func == :sum) && return parse_node(Sum, n)
        func == :delta && return parse_node(Delta, n)
        func == :+ && return parse_node(Add, n)
        func == :* && return parse_node(Mul, n)
        func == :pullback && return parse_node(Pullback, n)
        return parse_node(AbstractCall, n)
    end
    n.head == :block && return parse_node(n.args[1])
    n.head == :let && return parse_node(Let, n)
    n.head == Symbol("'") && return parse_node(Conjugate, n)
    n.head == Symbol(:quote) && return n.args[1]
    return :()
    #= n.head == :tuple && return parse_tuple_node(n) =#
end

function parse_node(::Type{MapType}, s::Expr)
    s = purge_line_numbers(s)
    @assert s.args[1] == Symbol("@space")
    block = s.args[2]

    parse_pair(::Val{:name}, n::Symbol) = n
    parse_pair(::Val{:symmetries}, t::Expr) = t
    function parse_pair(::Val{:type}, t::Expr)
        params = :(VecType([$([:($(a)()) for a in t.args[1].args]...)]))
        return_type = :($(first(t.args[2].args))())
        return (params, return_type)
    end


    pairs = Dict(a.args[1] => parse_pair(Val(a.args[1]), a.args[2]) for a in block.args)
    return :(
        $(pairs[:name]) = MapType(
            #= $(QuoteNode(pairs[:name])), =#
            $(pairs[:type]...),
            $(
                if haskey(pairs, :symmetries)
                    :(Dict(:symmetries => $(pairs[:symmetries])))
                else
                    :(Dict())
                end
            ),
        )
    )
end

struct Param <: APN end
function parse_node(::Type{Map}, f::Expr)
    f = purge_line_numbers(f)
    @assert f.head == Symbol("->")

    params = f.args[1].head == :tuple ? f.args[1].args : Vector{Expr}([f.args[1]])
    body = f.args[2]

    return :(make_node!(Map, make_node!(PCTVector, $(map(p -> parse_node(Param, p), params)...)), $(parse_node(body))))

end


function parse_node(::Type{Param}, p::Union{Expr,Symbol})
    if isa(p, Symbol)
        return :(make_node!(Var, $(QuoteNode(p))))
    end

    if p.head == Symbol("::")
        name, type = p.args
        type in [:I, :R, :C] && (type = :($(type)()))
        isa(name, Symbol) && return :(make_node!(Var, $(QuoteNode(name)), type=$(type)))
        return :(make_node!(
            PrimitiveCall,
            make_node!(Var, $(QuoteNode(name.args[1])), type=$(type)),
            make_node!(PCTVector, $(parse_node(name.args[2]))),
        ))
    end
    if p.head == :call
        return :(make_node!(
            PrimitiveCall,
            $(parse_node(p.args[1])),
            make_node!(PCTVector, $(parse_node.(p.args[2:end])...)),
        ))
    end

end

parse_node(p::Symbol) = :(make_node!(Var, $(QuoteNode(p))))
#= function parse_node(::Type{Var}, p::Symbol)
    make_node(Var, p)
end =#
parse_node(i::Number) = :(Constant($(i), $(pct_type(Constant, i))()))

function parse_node(::Type{AbstractCall}, c::Expr)
    @assert c.head == :call
    func = c.args[1]

    isa(func, Expr) &&
        func.head == Symbol("->") &&
        return :(make_node!(
            Call,
            $(parse_node(func)),
            make_node!(PCTVector, $(parse_node.(c.args[2:end])...)),
        ))

    return :(make_node!(
        PrimitiveCall,
        $(parse_node(func)),
        make_node!(PCTVector, $(parse_node.(c.args[2:end])...)),
    ))
end

function parse_node(::Type{Add}, a::Expr)
    @assert a.args[1] == :+
    return :(make_node!(Add, make_node!(PCTVector, $(parse_node.(a.args[2:end])...))))
end

function parse_node(::Type{Mul}, m::Expr)
    @assert m.args[1] == :*
    return :(make_node!(Mul, make_node!(PCTVector, $(parse_node.(m.args[2:end])...))))
end


function parse_node(::Type{Sum}, s::Expr)
    @assert s.args[1] == :sum || s.args[1] == :ctr
    #= default_type = s.args[1] == :sum ? I() : R() =#
    params = isa(s.args[2], Symbol) ? [s.args[2]] : s.args[2].args
    param_nodes = (n -> parse_node(Param, n)).(params)
    return :(make_node!(Sum, make_node!(PCTVector, $(param_nodes...)), $(parse_node(s.args[3]))))
end

function parse_node(::Type{Let}, l::Expr)
    @assert l.head == Symbol("let")

    substitutions = l.args[1].head == :block ? l.args[1].args : [l.args[1]]

    function parse_subst(a::Expr)
        @assert a.head == Symbol("=")
        return :($(parse_node(a.args[1])) => $(parse_node(a.args[2])))
    end

    content = parse_node(l.args[2])
    return :(make_node!(Let, make_node!(PCTVector, $(parse_subst.(substitutions)...)), $(content)))

end

function parse_node(::Type{Pullback}, p::Expr)
    @assert p.args[1] == :pullback
    return :(make_node!(Pullback, $(parse_node(p.args[2]))))
end


function parse_node(::Type{Delta}, d::Expr)
    @assert d.args[1] == :delta
    upper_params = isa(d.args[2], Symbol) ? [d.args[2]] : d.args[2].args
    lower_params = isa(d.args[3], Symbol) ? [d.args[3]] : d.args[3].args
    upper_nodes = (n -> parse_node(Param, n)).(upper_params)
    lower_nodes = (n -> parse_node(Param, n)).(lower_params)
    return :(make_node!(
        Delta,
        make_node!(PCTVector, $(upper_nodes...)),
        make_node!(PCTVector, $(lower_nodes...)),
        $(parse_node(d.args[4])),
    ))
end

function parse_node(::Type{Conjugate}, c::Expr)
    return :(make_node!(Conjugate, $(parse_node(c.args[1]))))
end


