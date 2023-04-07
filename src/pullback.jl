export evaluate_pullback, pullback

evaluate_pullback(n::APN) = set_terms!(n, evaluate_pullback.(terms(n))...)

evaluate_pullback(n::TerminalNode) = n

function evaluate_pullback(p::Pullback)
    mapp = fc(p)
    is_univariate(mapp) || return evaluate_pullback(p, MapType)
    pullback(fc(ff(mapp)), fc(mapp))
    # , make_node!(Var, :𝒦; type = get_type(fc(mapp)))
end

function evaluate_pullback(p::Pullback, ::Type{MapType})
    mapp = fc(p)
    length(ff(mapp)) > 1 && error("Multivariate tensor pullbacks are not supported.")

    z = fc(ff(mapp))
    k = make_node!(Var, :_K; type = get_type(fc(mapp)))
    z_types = from(get_type(z))
    z_index_symbols = new_symbol(p, z, k; num = length(z_types))
    z_vars = map((s, t) -> make_node!(Var, s; type = t), z_index_symbols, content(z_types))

    if isa(get_type(fc(mapp)), MapType)
        return multi_map(p, z, k, z_vars)
    else
        return single_map(z, k, z_vars, mapp)
    end
end

function single_map(z, k, z_vars, mapp)
    z_vars = make_node!(PCTVector, z_vars...)

    return make_node!(
        Map,
        make_node!(PCTVector, z, k),
        make_node!(
            Map,
            z_vars,
            make_node!(
                Call,
                pullback(make_node!(PrimitiveCall, z, z_vars), fc(mapp)),
                make_node!(PCTVector, make_node!(PrimitiveCall, z, z_vars), k),
            ),
        ),
    )
end



function multi_map(p, z, k, z_vars)

    result_map_type = get_type(fc(mapp))
    sum_types = content(from(result_map_type))
    sum_index_symbols = new_symbol(p, z, k, z_vars...; num = length(sum_types))

    sum_vars =
        map((s, t) -> make_node!(Var, s; type = t), sum_index_symbols, content(sum_types))

    z_vars = make_node!(PCTVector, z_vars...)
    sum_vars = make_node!(PCTVector, sum_vars...)

    return make_node!(
        Map,
        make_node!(PCTVector, z, k),
        make_node!(Map, z_vars),
        make_node!(
            Sum,
            sum_vars,
            make_node!(
                Call,
                make_node!(
                    Pullback,
                    make_node!(
                        Map,
                        make_node!(PCTVector, make_node!(PrimitiveCall, z, z_vars)),
                        make_node!(Call, fc(mapp), sum_vars),
                    ),
                ),
                make_node!(
                    PCTVector,
                    make_node!(PrimitiveCall, z, z_vars),
                    make_node!(PrimitiveCall, k, sum_vars),
                ),
            ),
        ),
    )

end


struct ElementWise end

# Univariate pullbacks

function pullback(iv::Var, ov::Var)
    k = make_node!(Var, :_K; type = get_type(ov))
    if name(iv) == name(ov)
        base(get_type(iv)) == base(get_type(ov)) ||
            error("type mismatch: $(get_type(iv)) vs $(get_type(ov))")
        return make_node!(Map, make_node!(PCTVector, iv, k), k)
    end
    return make_node!(Map, make_node!(PCTVector, iv, k), make_node!(Constant, 0))
end



function pullback(iv::Var, ov::Conjugate)
    #= k = make_node!(Var, :𝒦; type = get_type(ov)) =#
    new_map = pullback(iv, fc(ov))
    set_content!(new_map, content(new_map)...)
end


function pullback(iv::APN, ov::Add)
    k = make_node!(Var, :_K; type = get_type(ov))
    terms = map(
        c -> make_node!(Call, pullback(iv, c), make_node!(PCTVector, iv, k)),
        content(fc(ov)),
    )
    make_node!(
        Map,
        make_node!(PCTVector, iv, k),
        add(terms...),
    )
end


function pullback(iv::APN, ov::Mul)
    k = make_node!(Var, :_K; type = get_type(ov))
    terms::PCTVector = fc(ov)
    t1 = fc(terms)

    rest = length(terms) > 2 ? mul(content(terms)[2:end]...) : last(terms)

    arg_1 = mul(make_node!(Conjugate, rest), k)
    arg_2 = mul(make_node!(Conjugate, t1), k)
    term_1 = make_node!(Call, pullback(iv, t1), make_node!(PCTVector, iv, arg_1))
    term_2 = make_node!(Call, pullback(iv, rest), make_node!(PCTVector, iv, arg_2))
    make_node!(
        Map,
        make_node!(PCTVector, iv, k),
        add(term_1, term_2),
    )
end

"""

pullback(iv->(ff->fc)(y(a...))) = (iv, k) -> ∑(a, pullback(iv->a)(iv, pullback(ff->fc)(a..., k))
"""
function pullback(iv::APN, ov::Call)
    k = make_node!(Var, :_K; type = get_type(ov))
    g = mapp(ov)
    inner_pullback =
        make_node!(Call, pullback(ff(g), fc(g)), make_node!(PCTVector, args(ov)..., k))
    make_node!(
        Map,
        make_node!(PCTVector, iv, k),
        make_node!(
            Add,
            map(a -> call(pullback(iv, a), iv, inner_pullback), args(ov)),
        ),
    )
end

"""
    pullback(iv, ov)

The pullback between two primitive calls.

pullback(x(i)->x(j)) = (iv, k) -> δ(i, j, k)

pullback(x(i)->y(j)) = (iv, k) -> 0

Not working/tested.
pullback(x(i)->y(a(x))) = (iv, k) -> ∑(a, P(x->a(x))(iv, P(y)(x(j), k))
"""
function pullback(iv::PrimitiveCall, ov::PrimitiveCall)
    k = make_node!(Var, :_K; type = get_type(ov))

    if name(mapp(iv)) == name(mapp(ov))
        for (a_1, a_2) in zip(get_type.(content(args(iv))), get_type.(content(args(ov))))
            base(a_1) == base(a_2) || error("type mismatch: $(a_1) vs $(a_2)")
        end
        return make_node!(
            Map,
            make_node!(PCTVector, iv, k),
            delta(content(args(iv))..., content(args(ov))..., k),
        )
    end

    contains_name(ov, name(mapp(iv))) ||
        return make_node!(Map, make_node!(PCTVector, iv, k), make_node!(Constant, 0))

    inner_pullback = make_node!(
        PrimitiveCall,
        make_node!(PrimitivePullback, mapp(ov)),
        make_node!(PCTVector, content(args(ov))..., k),
    )

    make_node!(
        Map,
        make_node!(PCTVector, iv, k),
        map(a -> call(pullback(iv, a), iv, inner_pullback),
            args(ov),
        ),
    )
end

"""
    pullback(iv, ov)

Univariate pullback of a contraction.

pullback(iv->∑(ff, fc)) =
    (iv, k) -> ∑(ff, pullback(iv->fc)(iv, k))
"""
function pullback(iv::APN, ov::T) where {T<:Contraction}
    k = make_node!(Var, :_K; type = get_type(ov))
    make_node!(
        Map,
        make_node!(PCTVector, iv, k),
        make_node!(T, ff(ov), call(pullback(iv, fc(ov)), iv, k)),
    )
end


