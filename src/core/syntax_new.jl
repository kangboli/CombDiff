export @nein, @neinshow, @comb, @neintype, @neinspace, @mein, @main

macro comb(expr, f=:_, ctx=:(TypeContext()))
    expr = hasfield(typeof(expr), :head) && expr.head == :quote ? expr.args[1] : expr
    esc(:(@pct $(f) $(ctx) $(expr)))
end

function is_nested_arr_type(::Type{T}) where {T}
    T <: Number && return true
    T <: AbstractArray && return is_nested_arr_type(eltype(T))
    T <: RangedTensor && return true
end

function nein_base(expr, ctx, interior)
    return :(
        begin
            global_var_names = Symbol.(first.(first(varinfo().content).rows[2:end]))
            local_vars = Base.@locals()
            local_var_names = collect(keys(local_vars))

            global_type_names = filter(n -> isa(eval(n), AbstractPCTType), global_var_names)
            local_type_names = filter(n -> isa(local_vars[n], AbstractPCTType), local_var_names)

            let ctx = deepcopy($(ctx))
                map(n -> push_type!(ctx, n, eval(n)), global_type_names)
                map(n -> push_type!(ctx, n, local_vars[n]), local_type_names)

                content, ctx = @pit($(expr), ctx)

                global_array_names = filter(n -> CombDiff.is_nested_arr_type(typeof(eval(n))) ||
                        isa(eval(n), Function), global_var_names)
                global_array_names = filter(n -> content !== nothing && contains_name(content, n), global_array_names)
                global_array_types = map(n -> convert_pct_type(eval(n)), global_array_names)

                local_array_names = filter(n -> CombDiff.is_nested_arr_type(typeof(eval(n))) ||
                        isa(eval(n), Function), local_var_names)
                local_array_names = filter(n -> content !== nothing && contains_name(content, n), local_array_names)
                local_array_types = map(n -> convert_pct_type(local_vars[n]), local_array_names)

                global_params = map(var, global_array_names, global_array_types)
                local_params = map(var, local_array_names, local_array_types)
                $(interior)
            end
        end
    )
end

macro nein(expr, f=:_, ctx=:(TypeContext()))

    expr = purge_line_numbers(expr.args[1])
    return_node = if f == :_
        :(content)
    else
        :(continuition($(f), content))
    end

    return esc(:(
        begin
            $(nein_base(expr, ctx, :(Base.invokelatest(
                Base.invokelatest(
                    eval(codegen(inference(pct_map(global_params..., pct_map(local_params..., eval_all($(return_node))))))),
                    eval.(Symbol.(global_array_names))...),
                [local_vars[n] for n in local_array_names]...))))
        end
    ))
end


function_dict = Dict{Pair{Expr,Vector{Type}},Function}()
free_dict = Dict{Expr,Vector{Symbol}}()
expr_dict = Dict{Expr,APN}()
function clear_cache!()
    CombDiff.function_dict = Dict{Pair{Expr,Vector{Type}},Function}()
    CombDiff.free_dict = Dict{Expr,Vector{Symbol}}()
    CombDiff.expr_dict = Dict{Expr,APN}()
end



macro neintype(expr, f=:_, ctx=:(TypeContext()))
    expr = purge_line_numbers(expr.args[1])
    expr = :(@domain _tmp_domain $(expr))

    return esc(:(
        begin
            $(nein_base(expr, ctx, :(ctx[:_tmp_domain])))
        end
    ))
end


macro neinspace(expr, f=:_, ctx=:(TypeContext()))
    expr = purge_line_numbers(expr.args[1])
    expr = :(@space _tmp_space begin
        $(expr)
    end)

    return esc(:(
        begin
            $(nein_base(expr, ctx, :(ctx[:_tmp_space])))
        end
    ))
end


macro neinshow(expr, f=:_, ctx=:(TypeContext()))

    expr = purge_line_numbers(expr.args[1])
    return_node = if f == :_
        :(content)
    else
        :(continuition($(f), content))
    end

    return esc(:(
        begin
            $(nein_base(expr, ctx,
                :((inference(pct_map(global_params..., local_params..., $(return_node)))),
                    eval.(Symbol.(global_array_names)),
                    [local_vars[n] for n in local_array_names]
                ))
            )
        end
    ))
end

macro main(expr, f=:_, ctx=:(TypeContext()))
    expr = hasfield(typeof(expr), :head) && expr.head == :quote ? expr.args[1] : expr
    expr = purge_line_numbers(expr)
    node = parse_node(expr)
    if isa(node, MutatingStatement)
        node = statement_to_mut([node], lhs(node))
    end
    return_node = f == :_ ? node : :(continuition($(f), $(node)))

    return esc(:(
        begin
            _ctx = $(ctx)

            func = $(return_node)
            free = CombDiff.get_body.(CombDiff.get_free(func))
            filter!(t->!(haskey(_ctx, t) && isa(_ctx[t], ProductType)), free)

            #= context_types = typeof.([$(free...)]) =#
            local_vars = Base.@locals()
            free_vals = [haskey(local_vars, f) ? local_vars[f] : eval(f) for f in CombDiff.dedot.(free)]
            context_types = typeof.(free_vals)
            converted = CombDiff.convert_pct_type.(free_vals)
            func = pct_map(map(var, free, converted)..., func)
            reverse_inference(inference(func, _ctx)), free_vals
        end))
end

"""
"""
macro mein(expr, f=:_, ctx=:(TypeContext()))
    expr = hasfield(typeof(expr), :head) && expr.head == :quote ? expr.args[1] : expr
    expr = purge_line_numbers(expr)
    node = parse_node(expr)
    if isa(node, MutatingStatement)
        node = statement_to_mut([node], lhs(node))
    end
    return_node = f == :_ ? node : :(continuition($(f), $(node)))

    return esc(:(
        begin
            _ctx = $(ctx)

            func = get(CombDiff.expr_dict, $(QuoteNode(expr)), nothing)
            if func === nothing
                func = $(return_node)
                CombDiff.expr_dict[$(QuoteNode(expr))] = func
            end

            free = get(CombDiff.free_dict, $(QuoteNode(expr)), nothing)
            if free === nothing
                free = CombDiff.get_body.(CombDiff.get_free(func))
                filter!(t->!(haskey(_ctx, t) && isa(_ctx[t], ProductType)), free)
                CombDiff.free_dict[$(QuoteNode(expr))] = free
            end

            local_vars = Base.@locals()
            free_vals = [haskey(local_vars, f) ? local_vars[f] : eval(f) for f in CombDiff.dedot.(free)]
            context_types = typeof.(free_vals)
            compiled = get(CombDiff.function_dict, $(QuoteNode(expr)) => context_types, nothing)
            if compiled === nothing
                converted = CombDiff.convert_pct_type.(free_vals)
                func = pct_map(map(var, free, converted)..., func)
                compiled = eval(CombDiff.codegen(reverse_inference(inference(func, _ctx))))
                CombDiff.function_dict[$(QuoteNode(expr))=>context_types] = compiled
            end
            Base.invokelatest(compiled, (free_vals...))
        end))
end



#= macro nein(expr, f=:_, ctx=:(TypeContext()))

    expr = purge_line_numbers(expr.args[1])
    JitCache.function_counter::Int = 0

    JitCache.function_dict = Dict{Expr, Symbol}()

    if haskey(JitCache.function_dict, expr)
        function_name = JitCache.function_dict[expr]
        func = Expr(Symbol("."), Expr(Symbol("."), :CombDiff, QuoteNode(:JitCache)), QuoteNode(function_name))
        return :(Base.invokelatest($(func), eval.(Symbol.(global_array_names))..., [local_vars[n] for n in local_array_names]...))
    else
        function_name = Symbol("__$(JitCache.function_counter)")
        JitCache.function_dict[expr] = function_name
        JitCache.function_counter += 1
        func = Expr(Symbol("."), Expr(Symbol("."), :CombDiff, QuoteNode(:JitCache)), QuoteNode(function_name))
    end

    return_node = if f == :_ 
        :(content)
    else
        :(continuition($(f), content))
    end

    return esc(:(
        begin
            $(nein_base(expr, ctx, 
                        :(
                        begin
                        $(func) = eval(codegen(inference(pct_map(global_params..., pct_map(local_params..., eval_all($(return_node)))))))
                        Base.invokelatest(
                        $(func)
                #= eval(codegen(inference(pct_map(global_params..., pct_map(local_params..., eval_all($(return_node))))))) =#
                    , 
                eval.(Symbol.(global_array_names))..., [local_vars[n] for n in local_array_names]...)
                        end
                        )))
        end
    ))
end
 =#
