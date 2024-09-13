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

function are_similar(t, r)
    first(free_and_dummy(t)) == first(free_and_dummy(r)) || return false
    get_bound_length(n::APN) = 0
    get_bound_length(n::Contraction) = length(get_bound(n))
    function get_bound_length(n::Mul)
        sub_terms = content(get_body(n))
        i = findfirst(t -> isa(t, Sum), sub_terms)
        i === nothing && return 0
        return length(get_bound(sub_terms[i]))
    end

    get_bound_length(t) == get_bound_length(r) || return false
    return true
end

function absorb_single(t::APN, r_set::Vector{APN})::Tuple{APN, Bool}
    r_rep = first(r_set)

    #= typeof(t_rep) == typeof(r) || return t_set, false =#
    #= !isa(t_rep, Sum) || length(get_bound(t_rep)) == length(get_bound(r)) || return t_set, false =#
    are_similar(t, r_rep) || return t, false

    for r in r_set
        #= result = simplify(add(t, r); settings=custom_settings(:logging => false)) |> first =#
        result = combine_factors(add(t, r))
        isempty(nodes(result)) && continue
        #= new_t_set = simplify(first(new_t_set); settings=custom_settings(:logging => false, preset=symmetry_settings)) =#
        return first(nodes(result)), true
    end
    return t, false
end

function absorb_list(t::APN, list::Vector{Vector{APN}})
    remaining = Vector{Vector{APN}}()
    for r_set in list
        t, absorbed = absorb_single(t, r_set)
        absorbed || push!(remaining, r_set)
        absorbed && println("absorbed:", pretty(first(r_set)))
    end
    return t, remaining
end


function symmetry_reduction(n::Add; settings=default_settings)
    g = simplify(n; settings=custom_settings(:expand_mul => true, :gcd => false, :symmetry => false, :logging => false; preset=settings)) |> first
    isa(g, Add) || return g
    t_sets = map(t -> simplify(t; settings=custom_settings(:logging => false; preset=symmetry_settings)), content(get_body(g)))
    #= g = add(first.(t_sets)...) =#

    reduced = Vector{APN}()

    while !isempty(t_sets)
        t_set, rest... = t_sets
        t = first(t_set)

        #= t_set = simplify(t; settings=custom_settings(:logging => false, preset=symmetry_settings)) =#
        t, t_sets = absorb_list(t, rest)

        push!(reduced, t)
    end

    return add(reduced...)
end

function symmetry_reduction(n::APN; settings=default_settings)
    set_content(n, vcat(map(t -> symmetry_reduction(t; settings=settings), content(n))...)...)
end

function symmetry_reduction(n::TerminalNode; _=default_settings)
    return n
end
