
function vdiff(n::APN; settings=default_settings)
    set_content(n, vcat(map(t->vdiff(t; settings=settings), content(n))...)...)
end

function vdiff(p::Pullback; settings=default_settings)
    m = get_body(p)

    function vdiff_single(pcomp)
        result = pcomp |> pp |> eval_all |> propagate_k |> simplify |> first
        #= result = simplify(result, settings=custom_settings(:clench_sum=>true)) |> first =#
        return simplify(result; settings=settings) |> first
        #= if haskey(settings, :symmetry) && settings[:symmetry]
            return simplify(result; settings=settings) |> first
        else 
            return result
        end =#
    end

    result = pct_vec(map(f-> ecall(vdiff_single(decompose(pct_map(f, get_body(m)))), f), get_bound(m))...)
    return pct_map(get_bound(m)..., result)
    
end

function propagate_k(n::Map, k=constant(1))
    zs = get_bound(n)[1:end-1]
    return pct_map(zs..., ecall(n, get_bound(n)[1:end-1]..., k))
end


function redux(n::Map; settings=default_settings)
    pct_map(get_bound(n)...,  redux(get_body(n); settings=settings))
end

function redux(n::APN; settings=default_settings)
    reduced = [redux(t, settings=settings) for t in content(n)]
    simplify(set_content(n, reduced...); settings=settings) |> first
end

function redux(n::Union{Var, Constant}; _...)
    return n
end


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
    map(t->make_node(Map, get_bound(n), t), simplify(get_body(n); settings=settings))
end
