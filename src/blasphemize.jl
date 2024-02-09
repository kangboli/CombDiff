abstract type ContractionGraphNode end
const CGN = ContractionGraphNode

struct TensorNode <: CGN
    tensor_element::APN
end
tensor_element(t::TensorNode) = t.tensor_element

struct ContractionNode <: CGN
    contraction_index::APN
end
contraction_index(c::ContractionNode) = c.contraction_index

struct ContractionGraph <: APN
    tensor_nodes::Vector
    contraction_nodes::Vector{ContractionNode}
    edges::Dict{Symbol,Vector}
end

get_tensor_nodes(g::ContractionGraph) = g.tensor_nodes
get_contraction_nodes(g::ContractionGraph) = g.contraction_nodes
get_edges(g::ContractionGraph) = g.edges

function make_contraction_graph(s::Sum)
    summand = get_body(s)
    contraction_nodes = Dict(get_body(i) => ContractionNode(i) for i in content(get_bound(s)))
    tensor_nodes = map(TensorNode, content(get_body(summand)))

    edges = Dict{Symbol,Vector{TensorNode}}
    for t_node in tensor_nodes
        free, _ = free_and_dummy(tensor_element(t_node))
        filter!(tensorize, free)
        for f in free
            f in keys(contraction_nodes) || continue
            edges[get_body(f)] = push(get(edges, get_body(f), []), t_node)
        end
    end

    return ContractionGraph(contraction_nodes, tensor_nodes, edges)
end

function graph_to_contraction(g::ContractionGraph)
    pct_sum(contraction_index.(get_contraction_nodes(g))..., mul(tensor_element.(get_tensor_nodes(g))...))
end

is_vector(t::MapType) = length(get_bound_type(t)) == 1
is_matrix(t::MapType) = length(get_bound_type(t)) == 2

is_vector(t::AbstractPCTType) = false
is_matrix(t::AbstractPCTType) = false

indices(n::TensorNode) = content(args(n.tensor_element))
struct InnerProduct <: CGN
    l_node::CGN
    r_node::CGN
    contraction_node::ContractionNode
end
indices(::InnerProduct) = []

struct VectorMatrixProductNode <: CGN
    matrix::CGN
    vector::CGN
    contraction_node::ContractionNode
end

indices(n::VectorMatrixProductNode) = last(indices(n.matrix))

struct MatrixVectorProductNode <: CGN
    matrix::CGN
    vector::CGN
    contraction_node::ContractionNode
end
indices(n::MatrixVectorProductNode) = first(indices(n.matrix))

struct TransposeNode <: CGN
    matrix::CGN
end
indices(n::TransposeNode) = reverse(indices(n.matrix))

struct MatrixProductNode <: CGN
    l_node::CGN
    r_node::CGN
    contraction_node::ContractionNode
end
indices(n::MatrixProductNode) = [first(indices(n.l_node)), last(indices(n.r_node))]

function rewrite_degree_two_contraction!(g::ContractionGraph)
    (; _, contraction_nodes, edges) = g

    degree_two_contractions = filter(s -> length(edges[s]) == 2, keys(edges))
    while !isempty(degree_two_contractions)
        s = pop!(degree_two_contractions)
        x, y = sort(edges[s], by=is_vector)
        if is_vector(x) && is_vector(y)
            new_node = InnerProduct(x, y, contraction_nodes[s])
            update_graph!(g, s, x, y, new_node)
        end
        if is_vector(x) && is_matrix(y)
            if s == get_body(first(indices(y)))
                new_node = VectorMatrixProductNode(y, x, contraction_nodes[s])
            else
                new_node = MatrixVectorProductNode(y, x, contraction_nodes[s])
            end
            update_graph!(g, s, x, y, new_node)
        end
        if is_matrix(x) && is_matrix(y)
            i = findfirst(t -> get_body(t) == s, indices(x))
            j = findfirst(t -> get_body(t) == s, indices(y))
            if i == 2 && j == 1
                new_node = MatrixProductNode(x, y, contraction_nodes[s])
            elseif i == 1 && j == 2
                new_node = MatrixProductNode(y, x, contraction_nodes[s])
            elseif i == 1 && j == 1
                new_node = MatrixProductNode(TransposeNode(x), y, contraction_nodes[s])
            else
                new_node = MatrixProductNode(TransposeNode(y), x, contraction_nodes[s])
            end
            update_graph!(g, s, x, y, new_node)
        end
    end
end

function update_graph!(g::ContractionNode, s, x, y, new_node)
    (; tensor_nodes, contraction_nodes, edges) = g
    delete!(contraction_nodes, s)
    delete!(edges, s)
    filter!(t->t != x && t != y, tensor_nodes)
    push!(new_node)
    for t_nodes in values(edges)
        replace!(t_nodes, x, new_node)
        replace!(t_nodes, y, new_node)
    end
end

