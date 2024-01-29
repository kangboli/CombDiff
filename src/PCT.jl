module PCT

using Accessors
using Graphs
using GraphPlot
using SplitApplyCombine

include("type.jl")
include("nodes.jl")
include("element.jl")
include("e_class.jl")
include("index_signature.jl")
include("hash.jl")
include("evaluation.jl")
include("partialchain_fibration.jl")
include("inference.jl")
include("pretty.jl")
include("syntax.jl")
include("equivalent_set.jl")
include("graph.jl")
include("simplify.jl")
include("codegen.jl")

end
