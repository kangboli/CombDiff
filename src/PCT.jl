module PCT

using Accessors
using Graphs
using GraphPlot

include("type.jl")
include("element.jl")
include("index_signature.jl")
include("hash.jl")
include("evaluation.jl")
#= include("reduction.jl") =#
include("pullback.jl")
include("inference.jl")
include("pretty.jl")
include("syntax.jl")
include("equivalent_set.jl")
include("graph.jl")

end
