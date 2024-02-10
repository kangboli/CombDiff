export contraction_node,
    tensor_node,
    contraction_graph,
    graph_to_contraction,
    inner_product_node,
    vector_matrix_product_node,
    matrix_vector_product_node,
    matrix_product_node,
    transpose_node,
    rewrite_degree_two_contraction!

abstract type ContractionGraphNode <: APN end
const CGN = ContractionGraphNode

struct TensorNode <: CGN
    type::AbstractPCTType
    tensor_element::APN
end
tensor_element(t::TensorNode) = t.tensor_element
pretty(n::TensorNode) = pretty(n.tensor_element)
no_index(n::TensorNode) = pretty(mapp(n.tensor_element))
tensor_node(e::APN) = make_node(TensorNode, e)
partial_inference(::Type{TensorNode}, element::APN) = get_type(element)

struct ContractionNode <: CGN
    type::AbstractPCTType
    contraction_index::APN
end
contraction_index(c::ContractionNode) = c.contraction_index
pretty(n::ContractionNode) = pretty(n.contraction_index)
contraction_node(i::APN) = make_node(ContractionNode, i)
partial_inference(::Type{ContractionNode}, index) = get_type(index)

struct ContractionGraph <: APN
    type::AbstractPCTType
    tensor_nodes::Vector{CGN}
    contraction_nodes::Dict{Symbol,ContractionNode}
    edges::Dict{Symbol,Vector{CGN}}
end
function partial_inference(::Type{ContractionGraph}, terms::Vararg)
    tensor_nodes = first(terms)
    return escalate(get_type.(tensor_nodes)...)
end

function pretty(c::ContractionGraph)
    tensor_str = join(map(pretty, c.tensor_nodes))
    if isempty(c.contraction_nodes)
        return tensor_str
    else
        return "∑(($(join(map(n->pretty(n), values(c.contraction_nodes)), ","))), $(tensor_str))"
    end
end

function indices(g::ContractionGraph)
    result = vcat(map(indices, g.tensor_nodes)...)
    contraction_indices = contraction_index.(values(g.contraction_nodes))
    filter!(t -> !(t in contraction_indices), result)
    return result
end
get_tensor_nodes(g::ContractionGraph) = g.tensor_nodes
get_contraction_nodes(g::ContractionGraph) = g.contraction_nodes
get_edges(g::ContractionGraph) = g.edges

function contraction_graph(m::Map)
    inner_graph = contraction_graph(get_body(m))
    return set_content(m, inner_graph)
end

function contraction_graph(s::Sum)
    summand = get_body(s)
    contraction_nodes = Dict(get_body(i) => contraction_node(i) for i in content(get_bound(s)))
    if isa(summand, Mul)
        tensor_nodes = map(tensor_node, content(get_body(summand)))
    else
        tensor_nodes = [tensor_node(summand)]
    end
    return contraction_graph(tensor_nodes, contraction_nodes)
end

function contraction_graph(p::APN)
    contraction_nodes = Dict{Symbol, ContractionNode}()
    tensor_nodes = [tensor_node(p)]
    return contraction_graph(tensor_nodes, contraction_nodes)
end

function contraction_graph(tensor_nodes, contraction_nodes)

    edges = Dict{Symbol,Vector{TensorNode}}()
    for t_node in tensor_nodes
        free, _ = free_and_dummy(tensor_element(t_node))
        filter!(f -> tensorize(get_type(f)), free)
        for f in free
            get_body(f) in keys(contraction_nodes) || continue
            #= push!(get(edges, get_body(f), []), t_node) =#
            edges[get_body(f)] = push!(get(edges, get_body(f), []), t_node)
        end
    end

    return make_node(ContractionGraph, tensor_nodes, contraction_nodes, edges)
end

function graph_to_contraction(g::ContractionGraph)
    pct_sum(contraction_index.(get_contraction_nodes(g))..., mul(tensor_element.(get_tensor_nodes(g))...))
end

is_vector(t::MapType) = length(get_bound_type(t)) == 1
is_matrix(t::MapType) = length(get_bound_type(t)) == 2

is_vector(t::AbstractPCTType) = false
is_matrix(t::AbstractPCTType) = false
#= is_vector(t::TensorNode) = false
is_matrix(t::TensorNode) = false =#

indices(n::TensorNode) = filter(t -> tensorize(get_type(t)), content(args(n.tensor_element)))
is_vector(n::TensorNode) = length(indices(n)) == 1
is_matrix(n::TensorNode) = length(indices(n)) == 2

struct InnerProductNode <: CGN
    type::AbstractPCTType
    l_node::CGN
    r_node::CGN
    contraction_node::ContractionNode
end
indices(::InnerProductNode) = []
pretty(p::InnerProductNode) = "⟨$(no_index(p.l_node)), $(no_index(p.r_node))⟩"
no_index(p::InnerProductNode) = pretty(p)
is_vector(n::InnerProductNode) = false
is_matrix(n::InnerProductNode) = false
inner_product_node(l_node, r_node, contraction_node) = make_node(InnerProductNode,
    l_node, r_node, contraction_node)
function partial_inference(::Type{InnerProductNode}, l_node, r_node, contraction_node)
    escalate(get_type(l_node), get_type(r_node))
end

struct VectorMatrixProductNode <: CGN
    type::AbstractPCTType
    matrix::CGN
    vector::CGN
    contraction_node::ContractionNode
end
pretty(n::VectorMatrixProductNode) = "($(no_index(n)))($(map(pretty, indices(n))...))"
no_index(n::VectorMatrixProductNode) = "($(no_index(n.vector))ᵀ⋅$(no_index(n.matrix)))"
indices(n::VectorMatrixProductNode) = [last(indices(n.matrix))]
is_vector(n::VectorMatrixProductNode) = true
is_matrix(n::VectorMatrixProductNode) = false
function vector_matrix_product_node(matrix, vector, contraction_node)
    make_node(VectorMatrixProductNode, matrix, vector, contraction_node)
end
function partial_inference(::Type{VectorMatrixProductNode}, matrix, vector, contraction_node)
    return get_type(matrix)
end

struct MatrixVectorProductNode <: CGN
    type::AbstractPCTType
    matrix::CGN
    vector::CGN
    contraction_node::ContractionNode
end
indices(n::MatrixVectorProductNode) = [first(indices(n.matrix))]
pretty(n::MatrixVectorProductNode) = "($(no_index(n)))($(map(pretty, indices(n))...))"
no_index(n::MatrixVectorProductNode) = "($(no_index(n.matrix))⋅$(no_index(n.vector)))"
is_vector(n::MatrixVectorProductNode) = true
is_matrix(n::MatrixVectorProductNode) = false
function matrix_vector_product_node(matrix, vector, contraction_node)
    make_node(MatrixVectorProductNode, matrix, vector, contraction_node)
end
function partial_inference(::Type{MatrixVectorProductNode}, terms::Vararg)
    return get_type(first(terms))
end

struct NoIndexNode <: CGN
    type::AbstractPCTType
    node::CGN
end
pretty(n::NoIndexNode) = no_index(n.node)
no_index_node(n) = make_node(NoIndexNode, n)
function partial_inference(::Type{NoIndexNode}, node)
    return get_type(node)
end

struct TransposeNode <: CGN
    type::AbstractPCTType
    matrix::CGN
end
indices(n::TransposeNode) = reverse(indices(n.matrix))
pretty(t::TransposeNode) = "$(no_index(t.matrix))($(map(pretty, indices(t))...))"
no_index(t::TransposeNode) = "$(no_index(t.matrix))ᵀ"
is_vector(n::TransposeNode) = false
is_matrix(n::TransposeNode) = true
transpose_node(matrix) = make_node(TransposeNode, matrix)
function partial_inference(::Type{TransposeNode}, matrix)
    return get_type(matrix)
end

struct MatrixProductNode <: CGN
    type::AbstractPCTType
    l_node::CGN
    r_node::CGN
    contraction_node::ContractionNode
end
indices(n::MatrixProductNode) = [first(indices(n.l_node)), last(indices(n.r_node))]
no_index(n::MatrixProductNode) = "$(no_index(n.l_node))⋅$(no_index(n.r_node))"
pretty(n::MatrixProductNode) = "$(no_index(n))($(map(pretty, indices(n))...))"
is_matrix(n::MatrixProductNode) = true
is_vector(n::MatrixProductNode) = false
function matrix_product_node(l_node, r_node, contraction_node)
    make_node(MatrixProductNode, l_node, r_node, contraction_node)
end
function partial_inference(::Type{MatrixProductNode}, l_node, r_node, contraction_node)
    return get_type(l_node)
end

function rewrite_degree_two_contraction!(m::Map)
    g = get_body(m)
    rewrite_degree_two_contraction!(g)
    length(get_tensor_nodes(g)) == 1 || return set_content(m, g)
    inner_node = get_tensor_nodes(g) |> first
    indices(inner_node) == content(get_bound(m)) && return no_index_node(inner_node)
    if length(inner_node) == 2 && indices(inner_node) == reverse(content(get_bound(m)))
        return no_index_node(transpose_node(inner_node))
    end
end

function rewrite_degree_two_contraction!(g::ContractionGraph)

    contraction_nodes = g.contraction_nodes
    edges = g.edges
    degree_two_contractions = filter(s -> length(edges[s]) == 2, keys(edges))
    while !isempty(degree_two_contractions)
        s = pop!(degree_two_contractions)
        x, y = sort(edges[s], by=is_matrix)
        if is_vector(x) && is_vector(y)
            new_node = inner_product_node(x, y, contraction_nodes[s])
            update_graph!(g, s, x, y, new_node)
            continue
        end
        if is_vector(x) && is_matrix(y)
            if s == get_body(first(indices(y)))
                new_node = vector_matrix_product_node(y, x, contraction_nodes[s])
            else
                new_node = matrix_vector_product_node(y, x, contraction_nodes[s])
            end
            update_graph!(g, s, x, y, new_node)
            continue
        end
        if is_matrix(x) && is_matrix(y)
            i = findfirst(t -> get_body(t) == s, indices(x))
            j = findfirst(t -> get_body(t) == s, indices(y))
            if i == 2 && j == 1
                new_node = matrix_product_node(x, y, contraction_nodes[s])
            elseif i == 1 && j == 2
                new_node = matrix_product_node(y, x, contraction_nodes[s])
            elseif i == 1 && j == 1
                new_node = matrix_product_node(transpose_node(x), y, contraction_nodes[s])
            else
                new_node = matrix_product_node(transpose_node(y), x, contraction_nodes[s])
            end
            update_graph!(g, s, x, y, new_node)
            continue
        end
    end
end

function update_graph!(g::ContractionGraph, s, x, y, new_node)
    (; tensor_nodes, contraction_nodes, edges) = g
    delete!(contraction_nodes, s)
    delete!(edges, s)
    filter!(t -> t != x && t != y, tensor_nodes)
    push!(tensor_nodes, new_node)
    for t_nodes in values(edges)
        replace!(t_nodes, x => new_node)
        replace!(t_nodes, y => new_node)
    end
end

