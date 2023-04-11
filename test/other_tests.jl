
Meta.parse("
space(
    M,
    (I, I) => R,
    symmetries = [(1, 2)],
    )
")

"
(A::M, x::((I)->R)) -> let ax = (i::I) -> ctr((j::I), A(i,j) * x(j))
    ctr((i::I), x(i) * ax(i))
end
"

Meta.parse("(i)->i*2")
Meta.dump(Meta.parse("
begin
@space begin 
    name=M
    type=(I, I)->R
    symmetries=((1,2))
end

(x::V) -> pullback((x(i)::R) -> ctr((j::I), x(j) * x(j)))

(A::M, x::((I)->R)) -> let ax = (i::I) -> ctr((j::I), A(i,j) * x(j))
    ctr((i::I), x(i) * ax(i))
end
end
"))

Meta.dump(Meta.parse("
@space begin 
    name=M
    type=(I, I)->R 
    symmetries=((1,2),)
end"
), maxdepth=20)

parse_node(MapType, Meta.parse("
@space begin 
    name=M
    type=(I, I)->R 
    symmetries=((1,2),((2,3), (4,5)))
end"
))

expr = Meta.parse("
@space begin 
    name=M
    type=(I, I)->R 
    symmetries=((1,2),((2,3), (4,5)))
end"
)
expr = purge_line_numbers!( expr)

Meta.dump(Meta.parse("(x::V) -> pullback((x(i)::R) -> ctr((j::I), x(j) * x(j)))"), maxdepth=20)
Meta.dump(Meta.parse("(A::M, x::V) -> pullback((x(i)::R) -> ctr((j::I), x(j) * x(j)))"), maxdepth=20)
parse_node(Map, Meta.parse("(A::M, x::V) -> pullback((x(i)) -> ctr((j::I), x(j) * x(j)))"))
parse_node(AbstractCall, Meta.parse("(i::R->i+1)(j)"))
parse_node(Map, Meta.parse("(x::V)->(x(i))->x(j)"))
Meta.dump(Meta.parse("sum((i, ), x(i) * x(i))"))
parse_node(Sum, Meta.parse("sum((i, j), x(i) * x(i))"))
parse_node(Meta.parse("(x::V) -> sum((i, j), x(i) * x(i))"))
Meta.dump(Meta.parse("let x = y + 1,
    t = y + 1
    (z::I) -> x * z
end"))


parse_node(Let, Meta.parse("let x = y + 1,
    t = y + 1
    (z::I) -> x * z
end"))

parse_node(Meta.parse("pullback((x(i)::M)->sum((j), x(j)))"))


Meta.dump(Meta.parse("delta((i, j), (k, l), x(i) * x(i))"))
parse_node(Delta, Meta.parse("delta((i::I, j::I), (k::I, l::I), x(i) * x(i))"))
Meta.dump(Meta.parse("delta((i::I, j::I), (k::I, l::I), x(i) * x(i))"), maxdepth=20)

parse_node(Meta.parse("x'"))

@macroexpand @pct begin
@space begin
    name=M
    type=(I, I) -> R
    symmetries=((1,2),)
end

@space begin
    name=V
    type=(I,) -> R
end
(A::M) -> pullback((x::V) -> sum((i, j), x(i)' * A(i, j) * x(j)))
end


f = @pct begin
@space begin
    name=M
    type=(I, I) -> R
    symmetries=((1,2),)
end
@space begin
    name=V
    type=(I,) -> R
end
(A::M) -> pullback((x(k)::V) -> sum((i, j), x(i)' * A(i, j) * x(j)))
end

f = @pct begin
@space begin
    name=M
    type=(I, I) -> R
    symmetries=((1,2),)
end
@space begin
    name=V
    type=(I,) -> R
end
# (A::M) -> (i::I, j::I) -> ((i::R)->i * sum((j), i + j))(A(i, j))
# (A::M) -> (x::V) -> sum((i, j), x(i)' * A(i, j) * x(j))
# pullback((x::R) -> x * x + x)
# (y::V) -> (j::I) -> pullback((x(i)::V) -> x(j) * y(j))
(y::V) -> (j::I) -> ((x(i)::V) -> x(i))(y(j))
end

inferred_f = inference(f, TypeContext())
println(verbose(inferred_f))
e_f = evaluate(inferred_f)
println(verbose(e_f))
p = evaluate_pullback(inferred_f)
inferred_p = inference(p)
q = evaluate(inferred_p)
combine_add(evaluate(inferred_p))

evaluate(inferred_f)

make_node!(PCTVector, make_node!(Var, :i), make_node!(Var, :j))

