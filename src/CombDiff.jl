module CombDiff

include("core/misc.jl")
include("core/type/type.jl")
include("core/type/parametric_type.jl")
include("core/type/nodes.jl")
include("core/type/element.jl")
include("core/type/let.jl")
include("core/type/inference.jl")
include("core/bound.jl")
include("core/egraph/e_class.jl")
include("core/egraph/equivalent_set.jl")
include("core/egraph/graph.jl")
include("core/egraph/simplify.jl")
include("core/egraph/index_signature.jl")
include("core/egraph/hash.jl")
include("core/egraph/linear.jl")
include("core/evaluation.jl")
include("core/type/type_match.jl")
include("core/combinatory_diff.jl")
include("core/syntax.jl")
include("core/syntax_new.jl")

# The core does not and will not depend on the extensions.

include("extension/quantum_field.jl")
include("extension/blaserize.jl")
include("extension/pretty.jl")
include("extension/codegen.jl")
include("extension/call_by_indexing.jl")
include("extension/memory.jl")

end
