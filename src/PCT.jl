module PCT

using Accessors
using Graphs
using GraphPlot

include("type.jl")
include("element.jl")
include("e_class.jl")
include("hash.jl")
include("index_signature.jl")
include("evaluation.jl")
#= include("reduction.jl") =#
include("pullback.jl")
include("pbev.jl")
include("inference.jl")
include("pretty.jl")
include("syntax.jl")
include("neighbors.jl")
include("graph.jl")

end
