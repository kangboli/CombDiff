using PCT, Test

# Space, Sum and Call
f = @pct begin
    @space begin
        name=V
        type=(I,) -> R
    end

    (x::V) -> sum(i, x(i) * x(i))
end

@test name(first(content(ff(f)))) == :x
@test isa(fc(f), Sum)
@test name(ff(fc(f))) == :i

f = inference(f)

@test content(get_type(first(content(ff(f))))) == R()
@test from(get_type(first(content(ff(f))))) == VecType([I()])
@test get_type(fc(f)) == R()
 
@test (nodes(neighbors(fc(f))) |> length) == 1


# Split syntax
f = @pct begin
    @space begin
        name=V
        type=(I,) -> R
    end

    (x::V, i::I, j::I) -> _
end

g = @pct f sum(i, x(i) * x(i))

@test isa(fc(g), Sum)

# Domain
d = @pct begin
    @domain begin
        name=I1
        base=I
        lower=-N
        upper=N
    end
end

@test get_type(upper(inference(d))) == I()

# Product
g = @pct f prod(i, x(i))
@test isa(fc(g), Prod)

# Delta

g = @pct f delta(i, j, x(i) * x(j))
@test name(upper(fc(g))) == :i
@test name(lower(fc(g))) == :j


