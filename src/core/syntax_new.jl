export @nein, @neinshow, @comb, @neintype, @neinspace

macro comb(expr, f=:_, ctx=:(TypeContext()))
    :(@pct $(f) $(ctx) $(expr.args[1]))
end

function nein_base(expr, ctx, interior)
    return :(
        begin
            global_var_names = Symbol.(first.(first(varinfo().content).rows[2:end]))
            local_vars = Base.@locals()
            local_var_names = collect(keys(local_vars))

            global_type_names = filter(n->isa(eval(n), AbstractPCTType), global_var_names)
            local_type_names = filter(n->isa(local_vars[n], AbstractPCTType), local_var_names)

            ctx = deepcopy($(ctx))
            map(n->push_type!(ctx, n, eval(n)), global_type_names)
            map(n->push_type!(ctx, n, local_vars[n]), local_type_names)

            content, ctx = @pit($(expr), ctx)

            global_array_names = filter(n->isa(eval(n), Number) || 
                                        (isa(eval(n), Array) && eltype(eval(n)) <: Number) ||
                                        isa(eval(n), RangedTensor), global_var_names)
            global_array_names = filter(n->content!==nothing && contains_name(content, n), global_array_names)
            global_array_types = map(n->convert_pct_type(eval(n)), global_array_names)

            local_array_names = filter(n->isa(local_vars[n], Number) ||
                                       (isa(local_vars[n], Array) && eltype(local_vars[n]) <: Number) ||
                                       isa(local_vars[n], RangedTensor), local_var_names)
            local_array_names = filter(n->content!==nothing && contains_name(content, n), local_array_names)
            local_array_types = map(n->convert_pct_type(local_vars[n]), local_array_names)

            global_params = map(var, global_array_names, global_array_types)
            local_params = map(var, local_array_names, local_array_types)
            $(interior)
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
                    eval(codegen(inference(pct_map(global_params..., pct_map(local_params..., $(return_node)))))), 
                    eval.(Symbol.(global_array_names))...),
                [local_vars[n] for n in local_array_names]...))))
        end
    ))
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
                        :((inference(pct_map(global_params..., pct_map(local_params..., $(return_node)))),
                eval.(Symbol.(global_array_names)),
                [local_vars[n] for n in local_array_names]
                         ))
              
            ))
        end
    ))
end



