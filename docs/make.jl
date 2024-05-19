using Documenter

makedocs(sitename="CombDiff",
    pages=[
        "Introduction" => "index.md",
        "Tensor Calculus" => "tensor.md",
        "Calculus of Variations" => "calculus.md",
        "Analytic Backpropagation" => "backprop.md",
         "API (to be written)" => "api.md",
        #= "Language" => "api.md" =#
    ],
    format=Documenter.HTML(; mathengine=
    Documenter.KaTeX(
        Dict(:delimiters => [
                Dict(:left => raw"$", :right => raw"$", display => false),
                Dict(:left => raw"$$", :right => raw"$$", display => true),
                Dict(:left => raw"\[", :right => raw"\]", display => true),
            ],
            :macros => Dict("\\RR" => "\\mathbb{R}",
                raw"\Xi" => raw"X_{i}",
                raw"\Ru" => raw"R_{\mathrm{univ.}}",
                raw"\Pstd" => raw"P_{\mathrm{std}}",
                raw"\Tstd" => raw"T_{\mathrm{std}}",
            ),
        )
    )
    )
)


