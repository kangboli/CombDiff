using PCT, Test
# Symmetries

ctx = @pct _ begin

    @domain begin
        name=Na
        base=I
        lower=-N
        upper=N
    end

    @space begin
        name=S
        type=(I, I)->R
        symmetries=(((2, 1), :id),)
    end

    @space begin
        name=V
        type=(I,)->R
    end

    @space begin
        name=T
        type=(I, I, I, I)->R
        symmetries=(
        ((2, 1, 3, 4), :id), 
        ((1, 2, 4, 3), :id),
        ((3, 4, 1, 2), :id),
        )
    end

    (A::S, x::V, i::I, j::I, p::I, q::I) -> _
end

f = @pct ctx A(i, j)
@test first(neighbors(fc(f))[1]) == fc(@pct ctx A(j, i))

g = @pct ctx U(i, j, p, q)
@test fc(@pct ctx U(j, i, p, q)) in nodes(neighbors(fc(g)))
@test fc(@pct ctx U(i, j, q, p)) in nodes(neighbors(fc(g)))
@test fc(@pct ctx U(p, q, i, j)) in nodes(neighbors(fc(g)))

# visualize(spanning_tree!(fc(g)))

# GCD

fn(n) = first(nodes(neighbors(n)))

two = @pct _ 2 
@test two == fn(@pct _ 1 + 1)

@test fc(@pct(ctx, i*2)) in nodes(neighbors(fn(fc(@pct ctx i + i))))

@test @pct(j*(i+q)) in nodes(neighbors(@pct i * j + j * q))

@pct(0) == fn(fn(fn(@pct i - i)))

spanning_tree!(fc(@pct(ctx, i+i)))

visualize(spanning_tree!(fc(@pct(ctx, A(i, j)+A(j, i)))))
visualize(spanning_tree!(fc(@pct(ctx, sum((k), A(i, k)+A(k, i))))))
visualize(spanning_tree!(fc(@pct(ctx, sum((k), A(i, k) * x(k)) + sum((k), x(k) * A(k, i))))))
simplify(fc(@pct(ctx, sum((k), A(i, k) * x(k)) + sum((k), x(k) * A(k, i)))))
