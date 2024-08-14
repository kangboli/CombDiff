using CombDiff

_, ctx = @pct begin
    @domain I1{n} begin
        base = I
        lower = -n
        upper = n
    end

    @space M{m} begin
        type = (I1{m}, ) -> R
    end
end

@macroexpand @pct begin
    @domain I1{n} begin
        base = I
        lower = -n
        upper = n
    end

    @space M{m} begin
        type = (I1{m}, ) -> R
    end
end
