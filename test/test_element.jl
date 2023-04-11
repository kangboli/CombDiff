using PCT, Test

# Test Var
@testset "variables" begin
    # The machine-facing constructor.
    # `make_node` always takes one or more `APN`s.
    x = make_node(Var, :x)

    # Each variable has a name.
    @test name(x) == :x

    # The type is by default undetermined.
    @test get_type(x) == UndeterminedPCTType()

    # One can set the type.
    x = set_type(x, I())
    @test I() == get_type(x)

    # The `terms` of a variable is its name.
    # The same goes for `content`
    @test :x == first(terms(x))
    y = set_terms(x, :y)
    @test :y == name(y)
    z = set_content(x, :z)
    @test :z == first(content(z))
    @test get_type(z) == I()

    # non-generic constructor.
    @test x == var(:x, I())

    @test x == base(x)
    @test make_node(Constant, 1) == power(x)
    @test isempty(from(x))
end


# Test vectors
@testset "PCTVector" begin

    # The machine-facing constructor
    v = make_node(PCTVector, var(:x, I()), var(:y, I()), var(:z, I()))
    @test get_type(v) == VecType([I(), I(), I()])
    partial_inference(PCTVector, var(:x, I()), var(:y, I()), var(:z, I()))

    # The terms and the content of a vector are the elements.
    @test terms(v) == content(v)
    @test fc(v) == var(:x, I())

    # To set the elements, use either of these. 
    m = set_content(v, var(:p, I()), var(:q, I()))
    n = set_terms(v, var(:p, I()), var(:q, I()))
    @test m == n

    # mapping over a pct vector gives a pct vector back
    m2 = map(t->set_type(t, R()), m)
    @test get_type(fc(m2)) == R()
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
@testset "maps" begin
    m = make_node(Map, pct_vec(var(:x, I())), var(:x, I()))

    @test content(get_type(m)) == I()

    # `from` gives the list of argument as a PCTVector.
    @test from(get_type(m)) == VecType([I()])
    @test fc(ff(m)) == var(:x, I())

    # `content` gives the output of the map.
    @test fc(m) == var(:x, I())

    # `terms` gives both.
    @test length(terms(m)) == 2

    # One can set the `from`, the `content`, or both.
    m2 = set_from(m, pct_vec(var(:y, I())))
    @test fc(ff(m2)) == var(:y, I())

    m3 = set_content(m2, var(:y, I()))
    @test fc(m3) == var(:y, I())

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

@testset "pullbacks" begin
    m = make_node(Map, pct_vec(var(:x, I())), var(:x, I()))
    m2 = set_from(m, pct_vec(var(:y, I())))
    # Constructing a pullback is just wrapping 
    # a map in a struct called pullback.
    p = make_node(Pullback, m)
    @test fc(p) == m
    p2 = set_content(p, m2)
    @test fc(p2) == m2
    @test set_terms(p, m2) == p2

    # non-generic constructor
    pullback(m) == p

    # Primitive pullbacks
    p = pullback(var(:f))
    @test fc(p) == var(:f)

    # Test calls

    c = make_node(Call, pct_map(var(:x), var(:y), var(:x)), pct_vec(var(:x), var(:y)))
    @test mapp(c) == fc(c) == pct_map(var(:x), var(:y), var(:x))
    @test args(c) == last(content(c)) == pct_vec(var(:x), var(:y))

    @test m == mapp(set_content(c, m, pct_vec(var(:x), var(:z))))

    # non-generic constructor
    call(m, pct_map(var(:x), var(:y), var(:x)), var(:x), var(:y))

end

# Test monomials
@testset "monomials" begin

    m = make_node(Monomial, var(:x), var(:y))
    @test base(m) == var(:x)
    @test power(m) == var(:y)
    fc(m) == base(m)
    last(content(m)) == power(m)

    m2 = set_content(m, var(:p), var(:q))
    @test fc(m2) == var(:p)

    # non-generic constructor
    @test monomial(var(:p), var(:q)) == m2

end

# Test Add
@testset "add" begin
    a = make_node(Add, pct_vec(var(:x), var(:y)))
    @test fc(a) == pct_vec(var(:x), var(:y))

    a2 = set_content(a, pct_vec(var(:p), var(:q)))
    @test fc(a2) == pct_vec(var(:p), var(:q))

    @test flatten_add(a) == content(fc(a))

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

@testset "mul" begin
    a = make_node(Mul, pct_vec(var(:x), var(:y)))
    @test fc(a) == pct_vec(var(:x), var(:y))

    a2 = set_content(a, pct_vec(var(:p), var(:q)))
    @test fc(a2) == pct_vec(var(:p), var(:q))

    @test flatten_mul(a) == content(fc(a))

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

@testset "contraction" begin
    s = make_node(Sum, var(:i), call(var(:x), var(:i)))
    @test ff(s) == var(:i, I()) # There is an default inference for sum
    @test fc(s) == call(var(:x), var(:i))

    i = make_node(Integral, var(:x), call(var(:f), var(:x)))
    @test ff(i) == var(:x, R())
    @test fc(i) == call(var(:f), var(:x))

    # non-generic constructor.
    @test s == pct_sum(var(:i), call(var(:x), var(:i)))
    @test i == pct_int(var(:x), call(var(:f), var(:x)))

    # Multiple indices is OK.
    @test isa(pct_sum(var(:i), var(:j), call(var(:x), var(:i), var(:j))), Sum)
end

@testset "product" begin
    p = make_node(Prod, var(:i), call(var(:x), var(:i)))
    @test ff(p) == var(:i, I())
    @test fc(p) == call(var(:x), var(:i))
    @test p == pct_product(var(:i), call(var(:x), var(:i)))
end

@testset "Delta" begin
    d = make_node(Delta, var(:i), var(:j), call(var(:x), var(:i), var(:j)))
    @test upper(d) == var(:i)
    @test lower(d) == var(:j)
    @test fc(d) == call(var(:x), var(:i), var(:j))

    d2 = set_content(d, var(:p), var(:q), call(var(:x), var(:p), var(:q)))
    @test upper(d2) == var(:p)
    @test lower(d2) == var(:q)
    @test fc(d2) == call(var(:x), var(:p), var(:q))

    d = delta(var(:i), var(:p), var(:j), var(:q), call(var(:A), var(:i), var(:j)))

    @test upper(d) == var(:p)
    @test lower(d) == var(:q)

    @test upper(fc(d)) == var(:i)
    @test lower(fc(d)) == var(:j)
end

@testset "conjugate" begin
    c = make_node(Conjugate, var(:x))
    @test fc(c) == var(:x)

    c2 = make_node(Conjugate, c)
    @test c2 == var(:x)

    c3 = make_node(Conjugate, var(:x, I()))
    @test c3 == var(:x)

    c4 = conjugate(var(:y, C()))

    @test isa(c4, Conjugate)
    @test fc(c4) == var(:y, C())
end



