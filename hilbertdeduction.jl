### A Pluto.jl notebook ###
# v0.14.5

using Markdown
using InteractiveUtils

# ╔═╡ 40dd03fa-bb9a-11eb-3a08-a30e7215415b
abstract type Prop end

# ╔═╡ 814f0f17-d918-4a5b-8504-4ad0f9ea25b1
begin
	abstract type ⊤ <: Prop end
	abstract type ⊥ <: Prop end
end

# ╔═╡ 90cecfc3-753b-4a4e-85aa-6bf8b6face58
begin
	abstract type →{ϕ, ψ} <: Prop where {ϕ <: Prop, ψ <: Prop} end
	→(::Type{ϕ}, ::Type{ψ}) where {ϕ <: Prop, ψ <: Prop} = →{ϕ, ψ}
end

# ╔═╡ 035c180e-631f-4dc3-9c5e-d5fe4f0d865c
begin
	abstract type ¬{ϕ} <: Prop where {ϕ <: Prop} end
	¬(::Type{ϕ}) where {ϕ <: Prop} = ¬{ϕ} #ϕ → ⊥
end

# ╔═╡ 3fded8e1-e95f-4023-b7e3-071b4d1bffd8
begin
	Base.show(io::IO, ::Type{→{ϕ, ψ}}) where {ϕ <: Prop, ψ <: Prop} = print(io, "($ϕ → $ψ)")
	Base.show(io::IO, ::Type{¬{ϕ}}) where {ϕ <: Prop} = print(io, "¬$ϕ")
end

# ╔═╡ a1522fde-bfc6-4419-ab54-dd475dfc3a90
begin
	abstract type 𝒫 <: Prop end
	
	abstract type P <: 𝒫 end
	abstract type Q <: 𝒫 end
end

# ╔═╡ 79fce3ea-49e0-4d2b-8db4-a7911d4fb442
abstract type Sequentce end

# ╔═╡ 36605cc1-6aca-49fc-9618-ad6b003fdeab
begin
	struct Proof{ϕ} <: Prop where {ϕ <: Prop}
		proof
	end
	
	struct MP <: Sequentce
		A::Proof
		B::Proof
	end
	
	(A::Proof{→{ϕ, ψ}})(B::Proof{ϕ}) where {ϕ <: Prop, ψ <: Prop} = Proof{ψ}(MP(A, B))
	
	abstract type P1{ϕ} <: Sequentce where {ϕ <: Prop} end
	P1(::Type{ϕ}) where {ϕ <: Prop} = Proof{ϕ → ϕ}(P1{ϕ})
	
	abstract type P2{ϕ, ψ} <: Sequentce where {ϕ <: Prop, ψ <: Prop} end
	P2(::Type{ϕ}, ::Type{ψ}) where {ϕ <: Prop, ψ <: Prop} = Proof{ϕ → (ψ → ϕ)}(P2{ϕ, ψ})
	
	abstract type P3{ϕ, ψ, ζ} <: Sequentce where {ϕ <: Prop, ψ <: Prop, ζ <: Prop} end
	P3(::Type{ϕ}, ::Type{ψ}, ::Type{ζ}) where {ϕ <: Prop, ψ <: Prop, ζ <: Prop} = Proof{(ϕ → (ψ → ζ)) → ((ϕ → ψ) → (ψ → ζ))}(P3{ϕ, ψ, ζ})
	
	abstract type P4{ϕ, ψ} <: Sequentce where {ϕ <: Prop, ψ <: Prop} end
	P4(::Type{ϕ}, ::Type{ψ}) where {ϕ <: Prop, ψ <: Prop} = Proof{(¬ϕ → ¬ψ) → (ψ → ϕ)}(P4{ϕ, ψ})
end

Base.show(io::IO, p::Proof{ϕ}) where {ϕ <: Prop} = print(io, "Proof : $ϕ")


# ╔═╡ 5ef40058-5ad1-4c1d-8a37-29a80ba42c08
𝕃 = (P, Q)

# ╔═╡ 1abb3647-2834-4352-a136-b34a55e43862
begin
	function Base.rand(::Type{Prop}; ρ::Float64 = 0.6)
		if rand() ≤ ρ
			rand(Bool) ? →{rand(Prop), rand(Prop)} : ¬{rand(Prop)}
		else
			rand(𝕃)
		end
	end
	
	Base.rand(::Type{P1}) = P1(rand(Prop))
	Base.rand(::Type{P2}) = P2(rand(Prop), rand(Prop))
	Base.rand(::Type{P3}) = P3(rand(Prop), rand(Prop), rand(Prop))
	Base.rand(::Type{P4}) = P4(rand(Prop), rand(Prop))
	
	Base.rand(::Type{Sequentce}) = rand(rand([P1, P2, P3, P4]))
end

# ╔═╡ 4c7cbbeb-7a2b-4256-b9d8-91e2af65ba39
τ = Dict{DataType, Vector{Proof}}()
theoremcount = 0

# ╔═╡ 823bb686-8d3e-4d51-b517-6932fe7143ba
function addtheorem!(A::Proof{→{ϕ, ψ}}; threshold = 1000) where {ϕ <: Prop, ψ <: Prop}
        if theoremcount ≤ threshold
                haskey(τ, ϕ) ? nothing : τ[ϕ] = Proof[]	
	        A ∈ τ[ϕ] ? nothing : push!(τ[ϕ], A)
                global theoremcount
                theoremcount += 1
	
        	if haskey(τ, →{ϕ, ψ})
	        	for p ∈ τ[→{ϕ, ψ}]; addtheorem!(p(A); threshold = threshold); end
	        end
        end
end

# ╔═╡ f02bd8cd-f549-43b1-b5da-8f5d77d5ecb7
function generatetheorems(N = 1000; 𝕃 = (P, ))
        global theoremcount
	while theoremcount ≤ N
		addtheorem!(rand(Sequentce); threshold = N)
	end
end

function findtheorem(::Type{→{ϕ, ψ}}) where {ϕ <: Prop, ψ  <: Prop}
    if haskey(τ, ϕ)
        for p ∈ τ[ϕ]
            if typeof(p) == Proof{→{ϕ, ψ}}
                return p
            end
        end
    end
end


#
# ╔═╡ Cell order:
# ╠═40dd03fa-bb9a-11eb-3a08-a30e7215415b
# ╠═814f0f17-d918-4a5b-8504-4ad0f9ea25b1
# ╠═90cecfc3-753b-4a4e-85aa-6bf8b6face58
# ╠═035c180e-631f-4dc3-9c5e-d5fe4f0d865c
# ╠═3fded8e1-e95f-4023-b7e3-071b4d1bffd8
# ╠═a1522fde-bfc6-4419-ab54-dd475dfc3a90
# ╠═79fce3ea-49e0-4d2b-8db4-a7911d4fb442
# ╠═36605cc1-6aca-49fc-9618-ad6b003fdeab
# ╠═5ef40058-5ad1-4c1d-8a37-29a80ba42c08
# ╠═1abb3647-2834-4352-a136-b34a55e43862
# ╠═4c7cbbeb-7a2b-4256-b9d8-91e2af65ba39
# ╠═823bb686-8d3e-4d51-b517-6932fe7143ba
# ╠═f02bd8cd-f549-43b1-b5da-8f5d77d5ecb7
