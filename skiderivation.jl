abstract type Combinator end

abstract type S <: Combinator end
abstract type K <: Combinator end
abstract type Apply{A, B} <: Combinator where {A <: Combinator, B <: Combinator} end

Base.show(io::IO, ::Type{S}) = print(io, "S")
Base.show(io::IO, ::Type{Apply{A, B}}) where {A <: Combinator, B <: Combinator} = print(io, "($A ∘ $B)")

(∘)(::Type{A}, ::Type{B}) where {A <: Combinator, B <: Combinator} = Apply{A, B}

rewrite(::Type{S}) = S
rewrite(::Type{K}) = K
rewrite(::Type{Apply{Apply{Apply{S, F}, G}, Z}}) where {F <: Combinator, G <: Combinator, Z <: Combinator} = (F ∘ Z) ∘ (G ∘ Z)
rewrite(::Type{Apply{Apply{K, X}, Y}}) where {X <: Combinator, Y <: Combinator} = X
rewrite(::Type{Apply{A, B}}) where {A <: Combinator, B <: Combinator} = Apply{rewrite(A), rewrite(B)}

rewrite(::Type{C}, n::Int) where {C <: Combinator} = n == 0 ? C : rewrite(rewrite(C), n-1)

import Base.rand
rand(::Type{Combinator}; ρ = 0.4, 𝒞  = (S, K)) = rand() < ρ ? Apply{rand(Combinator; ρ = ρ, 𝒞 = 𝒞), rand(Combinator; ρ = ρ, 𝒞 = 𝒞)} : rand(𝒞)

abstract type X <: Combinator end
abstract type Y <: Combinator end
abstract type Z <: Combinator end
rewrite(::Type{X}) = X
rewrite(::Type{Y}) = Y
rewrite(::Type{Z}) = Z

abstract type ι <: Combinator end
rewrite(::Type{ι}) = ι
rewrite(::Type{Apply{ι, A}}) where {A <: Combinator} = Apply{Apply{A, S}, K}

#for _ ∈ 1:1000
#    c = rand(Combinator; 𝒞 = (ι, ))
#
#    if rewrite(c, 500) == S
#        println(c)
#    end
#end
#
function findformula(𝒞, vars, out)
    applyformula(e, vars) = length(vars) == 0 ? e : applyformula(Apply{e, vars[begin]}, vars[begin+1, end])

    for _ ∈ 1:1000
        c = rand(Combinator; 𝒞 = 𝒞)

        if rewrite(c, 200) == out
            println(c)
        end
    end
end
