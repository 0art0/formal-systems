abstract type Prop end

abstract type ⊤ <: Prop end
abstract type ⊥ <: Prop end

abstract type →{A, B} <: Prop where {A <: Prop, B <: Prop} end

abstract type 𝒫 <: Prop end

𝕃 = []

macro variable(A) :(abstract type $A <: 𝒫 end; push!(𝕃, $A)) end

@variable P; @variable Q; @variable R;

→(::Type{A}, ::Type{B}) where {A <: Prop, B <: Prop} = →{A, B}
¬(::Type{A}) where {A <: Prop} = A → ⊥

Base.show(io::IO, ::Type{→{A, B}}) where {A <: Prop, B <: Prop} = print(io, "($A → $B)")

function Base.rand(::Type{Prop}; ρ::Float64 = 0.6)
    if rand() ≤ ρ
        rand(Bool) ? →{rand(Prop), rand(Prop)} : ¬(rand(Prop))
    else
        rand(𝕃)
    end
end

fst(::Type{→{A, B}}) where {A <: Prop, B <: Prop} = A
snd(::Type{→{A, B}}) where {A <: Prop, B <: Prop} = B