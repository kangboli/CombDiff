using CombDiff

f, _ = @pct begin
    (M::N) -> (x::N{M}) -> x
end

pretty.(all_bounds(get_body(get_body(f)), Upper()))
