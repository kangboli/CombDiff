export evaluate_pullback, pullback

evaluate_pullback(n::APN) = set_terms!(n, evaluate_pullback.(terms(n))...)

evaluate_pullback(n::TerminalNode) = n

function evaluate_pullback(p::Pullback)
    mapp = fc(p)
    is_univariate(mapp) || return evaluate_pullback(p, MapType)
    pullback(fc(ff(mapp)), fc(mapp), make_node!(Var, :𝒦; type = get_type(fc(mapp))))
end

function evaluate_pullback(p::Pullback, ::Type{MapType})
    mapp = fc(p)
    length(ff(mapp)) > 1 && error("Multivariate tensor pullbacks are not supported.")

    z = fc(ff(mapp))
    k = make_node!(Var, :𝒦; type = get_type(fc(mapp)))
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
            make_node!(Map, z_vars,
            make_node!(
                Call,
                pullback(make_node!(PrimitiveCall, z, z_vars), fc(mapp), k),
                #= make_node!(
                    Pullback,
                    make_node!(
                        Map,
                        make_node!(PCTVector, make_node!(PrimitiveCall, z, z_vars)),
                        fc(mapp),
                    ),
                ), =#
                make_node!(PCTVector, make_node!(PrimitiveCall, z, z_vars), k),
            ),
         ),
        )
end



function multi_map(p, z, k, z_vars)

        result_map_type = get_type(fc(mapp))
        sum_types = content(from(result_map_type))
        sum_index_symbols = new_symbol(p, z, k, z_vars...; num = length(sum_types))

        sum_vars = map(
            (s, t) -> make_node!(Var, s; type = t),
            sum_index_symbols,
            content(sum_types),
        )

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

function pullback(iv::Var, ov::Var, k::Var)
    if name(iv) == name(ov)
        get_type(iv) == get_type(ov) ||
            error("type mismatch: $(get_type(iv)) vs $(get_type(ov))")
        return make_node!(Map, make_node!(PCTVector, iv, k), k)
    end
    return make_node!(Map, make_node!(PCTVector, iv, k), make_node!(Constant, 0))
end



function pullback(iv::Var, ov::Conjugate, k::Var)
    new_map = pullback(iv, fc(ov), k)
    set_content!(new_map, content(new_map)...)
end


function pullback(iv::APN, ov::Add, k::Var)
    terms = map(
        c -> make_node!(Call, pullback(iv, c, k), make_node!(PCTVector, iv, k)),
        content(fc(ov)),
    )
    make_node!(
        Map,
        make_node!(PCTVector, iv, k),
        make_node!(Add, make_node!(PCTVector, terms...)),
    )
end


function pullback(iv::APN, ov::Mul, k::Var)
    terms::PCTVector = fc(ov)
    t1 = fc(terms)

    rest = length(terms) > 2 ? make_node!(Mul, terms[2:end]) : last(terms)

    arg_1 = make_node!(Mul, make_node!(PCTVector, make_node!(Conjugate, rest), k))
    arg_2 = make_node!(Mul, make_node!(PCTVector, make_node!(Conjugate, t1), k))
    term_1 = make_node!(Call, pullback(iv, t1, k), make_node!(PCTVector, iv, arg_1))
    term_2 = make_node!(Call, pullback(iv, rest, k), make_node!(PCTVector, iv, arg_2))
    make_node!(
        Map,
        make_node!(PCTVector, iv, k),
        make_node!(Add, make_node!(PCTVector, term_1, term_2)),
    )
end

function pullback(iv::APN, ov::Call, k::Var)
    g = mapp(ov)
    inner_pullback =
        make_node!(Call, pullback(ff(g), fc(g), k), make_node!(PCTVector, args(ov)..., k))
    make_node!(
        Map,
        make_node!(PCTVector, iv, k),
        map(
            a -> make_node!(
                Call,
                pullback(iv, a, k),
                make_node!(PCTVector, iv, inner_pullback),
            ),
            args(ov),
        ),
    )
end

function pullback(iv::PrimitiveCall, ov::PrimitiveCall, k::APN)
    if name(mapp(iv)) == name(mapp(ov))
        for (a_1, a_2) in zip(get_type.(content(args(iv))), get_type.(content(args(ov))))
            a_1 == a_2 || error("type mismatch: $(a_1) vs $(a_2)")
        end
        return make_node!(
            Map,
            make_node!(PCTVector, iv, k),
            make_node!(Delta, args(iv), args(ov), k),
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
        map(
            a -> make_node!(
                Call,
                pullback(iv, a, k),
                make_node!(PCTVector, iv, inner_pullback),
            ),
            args(ov),
        ),
    )
end

"""
pullback(iv->sum(ff, fc)) = 
    (iv, k) -> sum(ff, pullback(iv->fc)(iv, k))
"""
function pullback(iv::APN, ov::T, k::APN) where T <: Contraction
    make_node!(Map, make_node!(PCTVector, iv, k),
    make_node!(T, ff(ov), make_node!(Call, pullback(iv, fc(ov), k), make_node!(PCTVector, iv, k))))
end


