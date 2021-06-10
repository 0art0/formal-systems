abstract type Prop end

abstract type ¬{A} <: Prop end
abstract type ∨{A, B} <: Prop end
abstract type ∧{A, B} <: Prop end
abstract type →{A, B} <: Prop end
abstract type ↔{A, B} <: Prop end

abstract type ⊤ <: Prop end
abstract type ⊥ <: Prop end

abstract type 𝒫 <: Prop end

macro variable(A) :(abstract type $A <: 𝒫 end) end

@variable P; @variable Q; @variable R

¬(::Type{A}) where {A <: Prop} = ¬{A}
∨(::Type{A}, ::Type{B}) where {A <: Prop, B <: Prop} = ∨{A, B}
∧(::Type{A}, ::Type{B}) where {A <: Prop, B <: Prop} = ∧{A, B}
→(::Type{A}, ::Type{B}) where {A <: Prop, B <: Prop} = →{A, B}
↔(::Type{A}, ::Type{B}) where {A <: Prop, B <: Prop} = →{A, B}

Base.show(io::IO, ::Type{¬{A}}) where {A <: Prop} = print(io, "¬$A")
Base.show(io::IO, ::Type{∨{A, B}}) where {A <: Prop, B <: Prop} = print(io, "($A ∨ $B)")
Base.show(io::IO, ::Type{∧{A, B}}) where {A <: Prop, B <: Prop} = print(io, "($A ∧ $B)")
Base.show(io::IO, ::Type{→{A, B}}) where {A <: Prop, B <: Prop} = print(io, "($A → $B)")
Base.show(io::IO, ::Type{↔{A, B}}) where {A <: Prop, B <: Prop} = print(io, "($A ↔ $B)")

rewrite(::Type{¬{A}}) where {A <: Prop} = rewrite(A → ⊥)
rewrite(::Type{∨{A, B}}) where {A <: Prop, B <: Prop} = rewrite(¬A → B)
rewrite(::Type{∧{A, B}}) where {A <: Prop, B <: Prop} = rewrite(¬(A → ¬B))
#rewrite(::Type{↔{A, B}}) where {A <: Prop, B <: Prop} = rewrite(((A → B) ∧ (B → A)))

rewrite(::Type{→{A, ⊤}}) where {A <: Prop} = ⊤
rewrite(::Type{→{⊥, A}}) where {A <: Prop} = ⊤
rewrite(::Type{→{⊤, ⊥}}) = ⊥


rewrite(::Type{→{A, B}}) where {A <: Prop, B <: Prop} = →{rewrite(A), rewrite(B)}

rewrite(::Type{⊤}) = ⊤
rewrite(::Type{⊥}) = ⊥
rewrite(::Type{A}) where {A <: 𝒫} = A

macro assign(A, b) :(rewrite(::Type{$A}) = $b) end
