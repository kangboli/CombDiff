export @nein, @neinshow, @comb

macro comb(expr, f=:_, ctx=:(TypeContext()))
    :(@pct $(f) $(ctx) $(expr.args[1]))
end

macro nein(expr, f=:_, ctx=:(TypeContext()))

    return_node = if f == :_ 
        :(content)
    else
        :(continuition($(f), content))
    end

    capture = esc(:(
        begin
            content, ctx = @pit($(expr.args[1]), $(ctx))
            local_var_names = first.(first(varinfo().content).rows[2:end])
            array_names = filter(n->isa(eval(Symbol(n)), Union{Array, Number}), local_var_names)
            array_names = filter(n->contains_name(content, Symbol(n)), array_names)
            array_types = map(n->convert_arr_type(typeof(eval(Symbol(n)))), array_names)
            params = map(var, Symbol.(array_names), array_types)
            eval(codegen(inference(pct_map(params..., $(return_node)))))(eval.(Symbol.(array_names))...)
        end
    ))
end

macro neinshow(expr, f=:_, ctx=:(TypeContext()))

    return_node = if f == :_ 
        :(content)
    else
        :(continuition($(f), content))
    end

    capture = esc(:(
        begin
            content, ctx = @pit($(expr.args[1]), $(ctx))
            local_var_names = first.(first(varinfo().content).rows[2:end])
            array_names = filter(n->isa(eval(Symbol(n)), Union{Array, Number}), local_var_names)
            array_names = filter(n->contains_name(content, Symbol(n)), array_names)
            array_types = map(n->convert_arr_type(typeof(eval(Symbol(n)))), array_names)
            params = map(var, Symbol.(array_names), array_types)
            inference(pct_map(params..., $(return_node)))
        end
    ))
end


