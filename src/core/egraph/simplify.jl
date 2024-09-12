export process_directive, dropp, eval_pullback, symmetry_reduction

function vdiff(n::APN)
    set_content(n, vcat(map(t -> vdiff(t), content(n))...)...)
end

function dropp(n::APN)
    set_content(n, vcat(map(t -> dropp(t), content(n))...)...)
end


vdiff(n::TerminalNode) = n

dropp(n::TerminalNode) = n

function vdiff(p::Pullback)
    m = get_body(p)

    function vdiff_single(pcomp)
        return pcomp |> pp |> eval_all |> propagate_k |> simplify |> first
    end

    result = pct_vec(map(f -> ecall(vdiff_single(decompose(pct_map(f, get_body(m)))), f), get_bound(m))...)
    if length(result) > 1
        result = simplify(result) |> first
    end
    return pct_map(get_bound(m)..., v_unwrap(result))
end

function eval_pullback(n::APN)
    result = set_content(n, vcat(map(t -> eval_pullback(t), content(n))...)...)
    return result
end

eval_pullback(n::TerminalNode) = n

function eval_pullback(c::AbstractCall)
    return call(eval_pullback(mapp(c)), map(eval_pullback, content(args(c)))...)
end

function eval_pullback(p::Pullback)
    m = get_body(p)
    #= output_type == R() || error("Output must be a real scalar for the gradient to be defined") =#
    function vdiff_single(pcomp)
        return pcomp |> pp |> eval_all
    end

    univariate_map = f -> decompose(pct_map(f, get_body(m)))

    output_type = get_body_type(get_type(m))
    k_types = isa(output_type, VecType) ? get_content_type(output_type) : [output_type]

    ks = map(var, new_symbol(m; num=length(v_wrap(get_body(m))), symbol=:_k), k_types)
    result = pct_vec(map(f -> ecall(vdiff_single(univariate_map(f)), f, ks...), get_bound(m))...)
    result = result |> simplify |> first
    return pct_map(get_bound(m)..., ks..., v_unwrap(result))
end

function dropp(p::Pullback)
    m = get_body(p)
    return dropp(m)
end

function propagate_k(n::Map, k=constant(1))
    println(pretty(n))
    zs = get_bound(n)[1:end-1]
    return pct_map(zs..., ecall(n, get_bound(n)[1:end-1]..., k))
end

"""
Redux will be a higher level interface to simplify to reduce the complexity.
I haven't figured out how to go about this so it just calls simplify right now.
"""
function redux(n::APN; settings=default_settings)
    result = simplify(n::APN; settings=settings) |> first
    simplify(result::APN; settings=custom_settings(:clench_sum => true)) |> first
end

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

function simplify(n::APN; kwargs...)
    g = last(spanning_tree!(n; kwargs...))
    min_size = minimum(pct_size, nodes(g))
    smallest = Vector{APN}()

    for n in nodes(g)
        pct_size(n) == min_size && push!(smallest, n)
    end
    return smallest
end

function simplify(n::Map; settings=default_settings, logger=Logger())
    if settings[:blaserize]
        return invoke(simplify, Tuple{APN}, n; settings, logger)
    else
        simplified_nodes = simplify(get_body(n); settings=settings, logger=logger)
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

function absorb_single(t_set, r)
    t_rep = first(t_set)

    #= typeof(t_rep) == typeof(r) || return t_set, false =#
    #= !isa(t_rep, Sum) || length(get_bound(t_rep)) == length(get_bound(r)) || return t_set, false =#
    first(free_and_dummy(t_rep)) == first(free_and_dummy(r)) || return t_set, false

    for t in t_set
        result = simplify(add(t, r); settings=custom_settings(:logging => false, preset=symmetry_settings)) |> first
        isa(result, Add) && continue
        new_set = simplify(result; settings=custom_settings(:logging => false, preset=symmetry_settings))
        return new_set, true
    end
    return t_set, false
end

function absorb_list(t_set, list)
    remaining = Vector{APN}()
    for r in list
        t_set, absorbed = absorb_single(t_set, r)
        absorbed || push!(remaining, r)
    end
    return t_set, remaining
end


function symmetry_reduction(n::Add; settings=default_settings)
    g = simplify(n; settings=custom_settings(:expand_mul => true, :gcd => false, :symmetry => false, :logging=>false; preset=settings)) |> first
    isa(g, Add) || return g
    g = add(map(t->first(simplify(t; settings=custom_settings(:logging=>false ;preset=symmetry_settings))), content(get_body(g)))...)
    

    reducibles = content(get_body(g))
    irreducibles = Vector{APN}()

    while !isempty(reducibles)
        t, rest... = reducibles
        
        t_set = simplify(t; settings=custom_settings(:logging => false, preset=symmetry_settings))
        t_set, reducibles = absorb_list(t_set, rest)

        push!(irreducibles, first(t_set))
    end

    return add(irreducibles...)
end

function symmetry_reduction(n::APN; settings=default_settings)
    set_content(n, vcat(map(t -> symmetry_reduction(t; settings=settings), content(n))...)...)
end

function symmetry_reduction(n::TerminalNode; _=default_settings)
    return n
end
