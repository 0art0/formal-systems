using Base: rewrap_unionall
abstract type Expression end
abstract type Variable <: Expression end

abstract type α <: Variable end
abstract type β <: Variable end
abstract type γ <: Variable end

abstract type f <: Variable end
abstract type g <: Variable end
abstract type h <: Variable end

abstract type x <: Variable end
abstract type y <: Variable end
abstract type z <: Variable end

abstract type Function <: Expression end
abstract type Head{X} <: Function where {X <: Variable} end
abstract type Abstraction{H, B} <: Function where {H <: Head, B <: Expression} end
abstract type Application{A, B} <: Function where {A <: Expression, B <: Expression} end

Base.show(io::IO, ::Type{Head{X}}) where {X <: Variable} = print(io, "λ$X")
Base.show(io::IO, ::Type{Abstraction{H, B}}) where {H <: Head, B <: Expression} = print(io, "$H. $B")
Base.show(io::IO, ::Type{Application{A, B}}) where {A <: Expression, B <: Expression} = print(io, "($A)($B)")

λ(::Type{X}) where {X <: Variable} = Head{X}
⋅(::Type{H}, ::Type{B}) where {H <: Head, B <: Expression} = Abstraction{H, B}
(::Type{M})(::Type{E}) where {M <: Expression, E <: Expression} = Application{M, E}

#β-reduction
reduce(::Type{V}) where {V <: Variable} = V
reduce(::Type{Abstraction{H, B}}) where {H <: Head, B <: Expression} = Abstraction{H, reduce(B)}
reduce(::Type{Application{A, B}}) where {A <: Expression, B <: Expression} = Application{reduce(A), reduce(B)}

function reduce(::Type{Application{Abstraction{Head{X}, ℬ}, E}}) where {X <: Variable, ℬ <: Expression, E <: Expression}
    rewrite(::Type{V}) where {V <: Variable} = V == X ? E : V
    rewrite(::Type{Abstraction{H, B}}) where {H <: Head, B <: Expression} = Abstraction{H, rewrite(B)}
    rewrite(::Type{Application{A, B}}) where {A <: Expression, B <: Expression} = Application{rewrite(A), rewrite(B)}

    rewrite(ℬ)
end