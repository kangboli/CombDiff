using CombDiff, Test

# Test Var
@testset "element: variables" begin
    # The machine-facing constructor.
    # `make_node` always takes one or more `APN`s.
    x = make_node(Var, pct_vec(), :x)

    # Each variable has a name.
    @test name(x) == :x

    # The type is by default undetermined.
    @test get_type(x) == UndeterminedPCTType()

    # One can set the type.
    x = set_type(x, I())
    @test I() == get_type(x)

    # The `terms` of a variable is its name.
    # The same goes for `content`
    @test :x == last(terms(x))
    y = set_terms(x, pct_vec(), :y)
    @test :y == name(y)
    z = set_content(x, :z)
    @test :z == first(content(z))
    @test get_type(z) == I()

    # non-generic constructor.
    @test x == var(:x, I())

    @test x == base(x)
    @test make_node(Constant, 1) == power(x)
    #= @test isempty(bound(x)) =#
end


# Test vectors
@testset "element: PCTVector" begin

    # The machine-facing constructor
    v = make_node(PCTVector, var(:x, I()), var(:y, I()), var(:z, I()))
    @test get_type(v) == VecType([I(), I(), I()])
    partial_inference(PCTVector, var(:x, I()), var(:y, I()), var(:z, I()))

    # The terms and the content of a vector are the elements.
    @test terms(v) == content(v)
    @test first(content(v)) == var(:x, I())

    # To set the elements, use either of these. 
    m = set_content(v, var(:p, I()), var(:q, I()))
    n = set_terms(v, var(:p, I()), var(:q, I()))
    @test m == n

    # mapping over a pct vector gives a pct vector back
    m2 = map(t->set_type(t, R()), m)
    @test get_type(first(content(m2))) == R()
    #
    # So is indexing
    @test m2[1:2] == m2

    # length is the number of nodes
    @test length(m2) == 2
    @test last(m2) == var(:q, R())
    @test first(m2) == var(:p, R())
    @test m2[1] == first(m2)

    # One can replace the ith entry
    v2 = set_i(v, 2, var(:q, R()))
    @test v2[2] == var(:q, R())

    # non-generic constructor
    v3 = pct_vec(var(:x, I()), var(:y, I()), var(:z, I()))
    v == v3
end

# Test maps
@testset "element: maps" begin
    m = make_node(Map, pct_vec(var(:x, I())), var(:x, I()))

    @test get_body_type(get_type(m)) == I()

    # `bound` gives the list of argument as a PCTVector.
    @test get_bound_type(get_type(m)) == VecType([I()])
    @test first(content(get_bound(m))) == var(:x, I())

    # `content` gives the output of the map.
    @test first(content((m))) == var(:x, I())

    # `terms` gives both.
    @test length(terms(m)) == 2

    # One can set the `bound`, the `content`, or both.
    m2 = set_bound(m, pct_vec(var(:y, I())))
    @test first(content(get_bound(m2))) == var(:y, I())

    m3 = set_content(m2, var(:y, I()))
    @test first(content(m3)) == var(:y, I())

    m4 = set_terms(m, pct_vec(var(:y, I())), var(:y, I()))
    @test m3 == m4

    # There is a function for testing if the function
    # is univariate, on which pullbacks will be supported.
    @test is_univariate(m)

    # non-generic contructor
    m5 = pct_map(var(:x, I()), var(:x, I()))
    @test m5 == m
end

# Test pullbacks

@testset "element: pullbacks" begin
    m = make_node(Map, pct_vec(var(:x, I())), var(:x, I()))
    m2 = set_bound(m, pct_vec(var(:y, I())))
    # Constructing a pullback is just wrapping 
    # a map in a struct called pullback.
    p = make_node(Pullback, m)
    @test get_body(p) == m
    p2 = set_content(p, m2)
    @test get_body(p2) == m2
    @test set_terms(p, m2) == p2

    # non-generic constructor
    pullback(m) == p

    # Primitive pullbacks
    p = pullback(var(:f))
    @test get_body(p) == var(:f)

    # Test calls

    c = make_node(Call, pct_map(var(:x), var(:y), var(:x)), pct_vec(var(:x), var(:y)))
    @test mapp(c) == first(content(c)) == pct_map(var(:x), var(:y), var(:x))
    @test args(c) == last(content(c)) == pct_vec(var(:x), var(:y))

    @test m == mapp(set_content(c, m, pct_vec(var(:x), var(:z))))

    # non-generic constructor
    call(m, pct_map(var(:x), var(:y), var(:x)), var(:x), var(:y))

end

# Test monomials
@testset "element: monomials" begin

    m = make_node(Monomial, var(:x), var(:y))
    @test base(m) == var(:x)
    @test power(m) == var(:y)
    first(content(m)) == base(m)
    last(content(m)) == power(m)

    m2 = set_content(m, var(:p), var(:q))
    @test first(content(m2)) == var(:p)

    # non-generic constructor
    @test monomial(var(:p), var(:q)) == m2

end

# Test Add
@testset "element: add" begin
    a = make_node(Add, pct_vec(var(:x), var(:y)))
    @test get_body(a) == pct_vec(sort([var(:x), var(:y)])...)

    a2 = set_content(a, pct_vec(var(:p), var(:q)))
    @test a2 == add(sort([var(:p), var(:q)])...)

    @test flatten_add(a) == content(get_body(a))

    # An `Add` with a single term is 
    # reduces in the e-class to the term.
    @test var(:x) == make_node(Add, pct_vec(var(:x)))

    # An `Add` of a term and zero reduces
    # in the e-class to the term.
    @test var(:x) == make_node(Add, pct_vec(var(:x), make_node(Constant, 0)))

    # An `Add` of and `Add` reduces
    # in the e-class to a flat `Add`.
    a = make_node(Add, pct_vec(var(:m), make_node(Add, pct_vec(var(:x), var(:z)))))
    @test a == make_node(Add, pct_vec(var(:m), var(:x), var(:z)))

    # non-generic constructor
    @test add(var(:m), var(:x), var(:z)) == a
end
# Test Mul

@testset "element: mul" begin
    a = make_node(Mul, pct_vec(var(:x), var(:y)))
    @test get_body(a) == pct_vec(sort([var(:x), var(:y)])...)

    a2 = set_content(a, pct_vec(var(:p), var(:q)))
    @test get_body(a2) == pct_vec(sort([var(:p), var(:q)])...)

    @test flatten_mul(a) == content(get_body(a))

    # An `Mul` with a single term is 
    # reduces in the e-class to the term.
    @test var(:x) == make_node(Mul, pct_vec(var(:x)))

    # An `Mul` of a term and zero reduces
    # in the e-class to the term.
    @test var(:x) == make_node(Mul, pct_vec(var(:x), make_node(Constant, 1)))

    @test make_node(Constant, 0) == make_node(Mul, pct_vec(var(:x), make_node(Constant, 0)))
    # An `Mul` of and `Mul` reduces
    # in the e-class to a flat `Mul`.
    a = make_node(Mul, pct_vec(var(:m), make_node(Mul, pct_vec(var(:x), var(:z)))))
    @test a == make_node(Mul, pct_vec(var(:m), var(:x), var(:z)))

    # non-generic constructor
    @test mul(var(:m), var(:x), var(:z)) == a
end

@testset "element: contraction" begin
    s = pct_sum(var(:i), call(var(:x), var(:i)))
    @test get_bound(s) == pct_vec(var(:i, N())) # There is an default inference for sum
    @test get_body(s) == call(var(:x), var(:i))

    i = pct_int(var(:x), call(var(:f), var(:x)))
    @test get_bound(i) == pct_vec(var(:x, R()))
    @test get_body(i) == call(var(:f), var(:x))

    # non-generic constructor.
    @test s == pct_sum(var(:i), call(var(:x), var(:i)))
    @test i == pct_int(var(:x), call(var(:f), var(:x)))

    # Multiple indices is OK.
    @test isa(pct_sum(var(:i), var(:j), call(var(:x), var(:i), var(:j))), Sum)
end

#= @testset "product" begin
    p = pct_product(var(:i), call(var(:x), var(:i)))
    @test get_bound(p) == pct_vec(var(:i, I()))
    @test get_body(p) == call(var(:x), var(:i))
    @test p == pct_product(var(:i), call(var(:x), var(:i)))
end =#

@testset "element: Delta" begin
    d = make_node(Delta, var(:i), var(:j), call(var(:x), var(:i), var(:j)))
    @test upper(d) == var(:i)
    @test lower(d) == var(:j)
    @test get_body(d) == call(var(:x), var(:i), var(:j))

    d2 = set_content(d, var(:p), var(:q), call(var(:x), var(:p), var(:q)))
    @test upper(d2) == var(:p)
    @test lower(d2) == var(:q)
    @test get_body(d2) == call(var(:x), var(:p), var(:q))

    d = delta(var(:i), var(:p), var(:j), var(:q), call(var(:A), var(:i), var(:j)))

    @test upper(d) == var(:p)
    @test lower(d) == var(:q)

    @test upper(get_body(d)) == var(:i)
    @test lower(get_body(d)) == var(:j)
end

@testset "element: conjugate" begin
    c = make_node(Conjugate, var(:x, C()))
    @test get_body(c) == var(:x, C())

    c2 = make_node(Conjugate, c)
    @test c2 == var(:x, C())

    c3 = make_node(Conjugate, var(:x, I()))
    @test c3 == var(:x, I())

    c4 = conjugate(var(:y, C()))

    @test isa(c4, Conjugate)
    @test get_body(c4) == var(:y, C())
end



