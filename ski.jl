const S = f -> g -> z -> f(z)(g(z));
const K = x -> y -> x;
const I = x -> x;

for f in (:S, :K, :I)
    @eval Base.show(io::IO, ::typeof($f)) = print(io, $(string(f)))
    @eval Base.show(io::IO, ::MIME"text/plain", ::typeof($f)) = show(io, $f)
end

#Base.show(io::IO, s::typeof(S(I)).name.primary) = print(io, "S(", s.f, ')')
#Base.show(io::IO, s::typeof(S(I)(I)).name.primary) = print(io, "S(", s.f, ')', '(', s.g, ')')
#Base.show(io::IO, k::typeof(K(I)).name) = print(io, "K(", k.x, ')')
#Base.show(io::IO, ::MIME"text/plain", f::Union{
#    typeof(S(I)).name,
#    typeof(S(I)(I)).name,
#    typeof(K(I)).name
#}) = show(io, f)