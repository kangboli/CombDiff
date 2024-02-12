export process_directive

function vdiff(n::APN)
    set_content(n, vcat(map(t -> vdiff(t), content(n))...)...)
end

function vdiff(p::Pullback)
    m = get_body(p)

    function vdiff_single(pcomp)
        return pcomp |> pp |> eval_all |> propagate_k |> simplify |> first
    end

    result = pct_vec(map(f -> ecall(vdiff_single(decompose(pct_map(f, get_body(m)))), f), get_bound(m))...)
    return pct_map(get_bound(m)..., v_unwrap(result))
end

function propagate_k(n::Map, k=constant(1))
    zs = get_bound(n)[1:end-1]
    return pct_map(zs..., ecall(n, get_bound(n)[1:end-1]..., k))
end

"""
Redux will be a higher level interface to simplify to reduce the complexity.
I haven't figured out how to go about this so it just calls simplify right now.
"""
redux(n::APN; settings=default_settings) = simplify(n::APN; settings=settings) |> first

#= function redux(n::Map; settings=default_settings)
    pct_map(get_bound(n)...,  redux(get_body(n); settings=settings))
end

function redux(n::T; settings=default_settings) where T
    if T == Sum
        settings = custom_settings(:gcd=>false; preset=settings)
    end
    reduced = [redux(t, settings=settings) for t in content(n)]
    simplify(set_content(n, reduced...); settings=settings) |> first
end

function redux(n::Union{Var, Constant}; _...)
    return n
end
 =#

function simplify(n::APN; settings=default_settings)
    g = last(spanning_tree!(n; settings=settings))
    min_size = minimum(pct_size, nodes(g))
    smallest = Vector{APN}()

    for n in nodes(g)
        pct_size(n) == min_size && push!(smallest, n)
    end
    return smallest
end

function simplify(n::Map; settings=default_settings)
    if settings[:blaserize]
        return invoke(simplify, Tuple{APN}, n; settings)
    else
        simplified_nodes = simplify(get_body(n); settings=settings)
        return map(t -> make_node(Map, get_bound(n), t), simplified_nodes)
    end
end

process_directive(n::APN) = set_content(n, map(process_directive, content(n))...)

const directive_list = [:__vdiff, :__sym, :__deactivate]

function process_directive(n::PrimitiveCall)
    directive = get_body(mapp(n))
    directive in directive_list || return invoke(process_directive, Tuple{APN,}, n)
    length(args(n)) > 1 && error("A directive cannot be applied to multiple arguments")
    new_arg = first(process_directive(args(n)))
    directive == :__vdiff && return vdiff(new_arg)
    directive == :__sym && return redux(new_arg; settings=symmetry_settings)
    directive == :__deactivate && pop!(current_ast_transforms())
end

process_directive(n::Union{Var,Constant}) = n
