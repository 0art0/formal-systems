abstract type AbstractType end

struct →{A, B} <: AbstractType where {A <: AbstractType, B <: AbstractType}
    name::Union{Symbol, Expr}
end

→(::Type{A}, ::Type{B}) where {A <: AbstractType, B <: AbstractType} = →{A, B}

Base.show(io::IO, ::Type{→{A, B}}) where {A <: AbstractType, B <: AbstractType} = print(io, "$A → $B")
Base.show(io::IO, x::AbstractType) = print(io, "$(x.name) : $(typeof(x))")

dom(::Type{→{A, B}}) where {A <: AbstractType, B <: AbstractType} = A
cod(::Type{→{A, B}}) where {A <: AbstractType, B <: AbstractType} = B

var(x::Symbol, ::Type{T}) where {T <: AbstractType} = Expr(:(=), x, T(x)) |> eval
macro var(x, T) var(x, eval(T)) end

macro type(T)
    :(struct $T <: AbstractType
        name::Union{Symbol, Expr}
    end)
end

(f::(→{A, B}))(a::A) where {A, B <: AbstractType} = B(:($(f.name)($(a.name))))
