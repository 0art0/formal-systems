#### The meta-language

#Negation
(¬)(p::Bool)::Bool = !p
#Disjunction
∨(p::Bool, q::Bool)::Bool =  p || q
#Conjunction
∧(p::Bool, q::Bool)::Bool = ¬(¬p ∨ ¬q)
#Implication
⟹(p::Bool, q::Bool)::Bool = ¬p ∨ q
#Biconditional
⟺(p::Bool, q::Bool)::Bool = (p ⟹ q) ∧ (q ⟹ p)

#The data-type for well-formed formulae
WFF = Union{Symbol, Expr}

#The language
𝕃 = (:p, :q, :r)

"""
Generates all well-formed formulae of size `n`.

S𝕃(n) = S𝕃(n-1) ∪ {(¬s), (s ∨ t) | s, t ∈ S𝕃(n-1)}
"""
function S𝕃(n::Int = 0)
    n == 0 ?
    [𝕃...] :
    [
    S𝕃(n-1);
    [:(¬$s) for s ∈ S𝕃(n-1)];
    [:($s∨$t) for s ∈ S𝕃(n-1) for t ∈ S𝕃(n-1)]
    ]
end

SL = S𝕃(3)

rand(SL)

"""
Rewrites a formula, replacing a given symbol with a boolean value (true / false).
"""
function rewrite!(formula::WFF, s::Symbol, v::Bool)
    for (i, e) in enumerate(formula.args)
        if e == s
            formula.args[i] = v
        elseif typeof(e) == Expr
            rewrite!(e, s, v)
        end
    end
end

#A demonstration of the `rewrite!` function
f = :((¬p ∨ (q ∧ ¬r)) ∨ (p ⟹ ¬p))
rewrite!(f, :p, true)
f

"""
Applies a given valuation to a formula `φ`.
"""
function evaluate(φ::WFF, v::Tuple{Vararg{Bool}})::Bool
    formula = deepcopy(φ)  #copying to preserve the input formula
    
    if typeof(φ) == Symbol
        formula = Expr(:call, :(x -> x), formula) #handling symbols
    end        

    for (val, s) ∈ zip(v, 𝕃)
        rewrite!(formula, s, val)
    end

    eval(formula)
end

#A demonstration of the `evaluate` function
ϕ = :((¬r ⟹ (q ∧ p)) ⟺ (((r ∨ ¬p) ∧ (p ⟹ q)) ∨ p))
evaluate(ϕ, (true, false, true))

"""
Checks if a valuation v satisfies a given set of formulae.
"""
evaluate(formulae::Vector{Any}, v::Tuple{Vararg{Bool}})::Bool = reduce(∧, [evaluate(formula, v) for formula ∈ formulae])

"""
Gives the list of all valuations that satisfy the given formula.
"""
function ν(formula::Union{WFF, Vector{Expr}})::Vector{Tuple{Vararg{Bool}}}
    #the set of all possible valuations for the symbols in 𝕃
    vs = Iterators.product(ntuple(i -> (false, true), length(𝕃))...) |> collect |> vec

    [v for v ∈ vs if evaluate(formula, v)]
end

"""
Checks if a proposition `t` is a logical consequence of a given set of propositions `S`.

In other words, this function checks if `S ⊨ t`.
"""
⊩(S::Vector{Any}, t::WFF)::Bool = ν(S) ⊆ ν(t)

#A demonstration of the `⊩` function
[:(p ∧ p), :(p ⟹ r)] ⊩ :(r ∨ r)

"""
Checks if two propositional formulae `s` and `t` are logically equivalent (`s ≡ t`).
"""
≌(s::WFF, t::WFF)::Bool = (ν(s) ⊆ ν(t)) ∧ (ν(t) ⊆ ν(s))

#A demonstration of the `≌` function
:(p ∨ ¬(p ⟹ q)) ≌ :(p ∧ p)



#### Hilbert-style deductive calculus

#The Logical Axioms

LA₁(s::WFF, t::WFF)::WFF = :( $s ⟹ ($t ⟹ $s) )

LA₂(s::WFF, t::WFF, u::WFF)::WFF = :( ($s ⟹ ($t ⟹ $u)) ⟹ (($s ⟹ $t) ⟹ ($s ⟹ $u)) )

LA₃(s::WFF)::WFF = :( ¬¬$s ⟹ $s )

LA₄(s::WFF, t::WFF)::WFF = :( (¬$s ⟹ ¬$t) ⟹ ($t ⟹ $s) )

#Modus Ponens
MP(s::WFF, t::WFF)::WFF = s.args[begin] == :⟹ && (s.args[begin+1] == t) ? s.args[end] : :missing

#Non-Logical Axioms
NLA(S   , n::Int)::WFF = S[n]

"""
A data structure defining sequents.

It contains the set of non-logical axioms `S`,
a propositional formula `t`,
a rule (logical axiom, rule of inference, or non-logical axiom) used to derive the proposition,
a list of arguments passed to the rule function.

`S ⊢ t`
"""
struct Sequent
    S::Vector{WFF}
    t::WFF
    rule::Function
    args::Vector{Any}

    #checks if the sequent rule gives the required formula
    Sequent(S, t, rule, args) = rule != MP && rule(args...) != t ?
        error("Inconsistent sequent") :
        new(S, t, rule, args)
end

#The data-type for formal proofs
FormalProof = Vector{Sequent}  #a FormalProof here is implemented as a list of Sequents

"""
A function that takes in a FormalProof (a list of sequents),
and verifies if the steps are correct.

If the formal proof is correct, the last propositional formula is returned.
"""
function verify(FP::FormalProof)
    for (i, Seq) ∈ enumerate(FP)
        if Seq.rule == MP
            #The indices here are relative positions
            m, n = Seq.args[begin]
            MP(FP[i - m].t, FP[i - n].t) == Seq.t ?
            println("Step $i involving MP is correct.") :
            error("Error in step $i in the formal proof.")
        end
    end

    println("\n The formal proof is correct!")

    return FP[end].t
end

#A demonstration of formal proof verification for the propositional formula `p ⟹ r`.
let S = [:(p ⟹ q), :(q ⟹ r)]
    proof::FormalProof = [
    Sequent(S, :(q ⟹ r), NLA, [S, 2]),
    Sequent(S, :(p ⟹ q), NLA, [S, 1]),
    Sequent(S, :((q ⟹ r) ⟹ (p ⟹ (q ⟹ r))), LA₁, [:(q ⟹ r), :(p)]),
    Sequent(S, :((p ⟹ (q ⟹ r))), MP, [(1, 3)]),
    Sequent(S, :( (p ⟹ (q ⟹ r)) ⟹ ((p ⟹ q) ⟹ (p ⟹ r)) ), LA₂, [:p, :q, :r]),
    Sequent(S, :((p ⟹ q) ⟹ (p ⟹ r)), MP, [(1, 2)]),
    Sequent(S, :(p ⟹ r), MP, [(1, 5)])
    ]

    verify(proof)
end

#Verification of the proof of :((s ⟹ ¬¬s))
let S = Expr[]
    proof::FormalProof = [
    Sequent(S, :(¬(¬(¬s)) ⟹ ¬s), LA₃, [:(¬s)]),
    Sequent(S, :( (¬(¬(¬s)) ⟹ ¬s) ⟹ (s ⟹ ¬(¬s))), LA₄, [:(¬(¬s)), :(s)]),
    Sequent(S, :(s ⟹ ¬(¬s)), MP, [(1, 2)])
    ]

    verify(proof)
end

"""
Recurses through the expression `expr`, searching for an occurrence of the expression `pf` on the right of an implication sign.
The output is a vector of terms that were on the left side of an implication sign.
"""
function nested(expr::WFF, pf::WFF)
    if expr == pf
        return [pf]
    end

    if typeof(expr) != Symbol && expr.args[begin] == :⟹
        a, b = expr.args[end-1:end]

        return [a; nested(b, pf)]
    end
    return expr
end

"""
Returns a set of tautologies obtained by plugging the elements of the input set `S` into to the logical axioms.
A dictionary is used to store information regarding which logical axiom and inputs were used to produce a particular expression.
"""
function τ(S::Vector{Any})
    T, D = Expr[], Dict{Expr, Tuple{Function, Vector{Any}}}()

    for a ∈ S
        push!(T, LA₃(a)); push!(D, LA₃(a)=>(LA₃, [a]))
        for b ∈ S
            push!(T, LA₁(a, b)); push!(D, LA₁(a, b)=>(LA₁, [a, b]))
            push!(T, LA₄(a, b)); push!(D, LA₄(a, b)=>(LA₄, [a, b]))
            for c ∈ S
                push!(T, LA₂(a, b, c)); push!(D, LA₂(a, b, c)=>(LA₂, [a, b, c]))
            end
        end
    end

    (T, D)
end

"""
Produces new propositional formulae from the given set `S` by recursively joining existing propositions with `¬` and `⟹`.
"""
function R𝕃(S, n::Int)
    n == 0 ?
    S :
    [
    R𝕃(S, n-1);
    [:(¬$s) for s ∈ R𝕃(S, n-1)];
    [:($s⟹$t) for s ∈ R𝕃(S, n-1) for t ∈ R𝕃(S, n-1)]
    ] |> Set |> collect
end

𝕃 = (:s,)

"""
Returns a formal proof (list of sequents) of a propositional formula `prop`, using tautologies specified in the list `T`.

The output is an empty list is no proof can be produced using the tautologies in `T`.
"""
function proof_of(prop::WFF, T, D; avoid = [])
    formalproof = Sequent[]

    function explore()
        ℒ = [(nested(t, prop), t) for t ∈ T]
        filter!(V -> V[1][end] == prop, ℒ)

        for l ∈ ℒ
            push!(formalproof, Sequent(Expr[], l[end], D[l[end]]...))
            seqprove(l...)

            length(formalproof) == 0 ? continue : break
        end

        return formalproof
    end

    function seqprove(props, expr)
        if length(props) == 1
            return
        end

        if (props[begin] ∈ avoid) || length(ν(props[begin])) < 2^length(𝕃)
            formalproof = Sequent[]
            return
        end

        pr = proof_of(props[begin], T, D; avoid = [[props[end]]; avoid])

        if length(pr) == 0
            formalproof = Sequent[]
            return
        end

        append!(formalproof, pr)
        push!(formalproof, Sequent(Expr[], expr.args[end], MP, [(1, 1+length(pr))]))
        seqprove(props[begin+1:end], expr.args[end])
    end

    explore()
end

proof_of(prop::WFF, (S, n)) = proof_of(prop, τ(R𝕃(S, n))...)


#Examples of proofs
proof_of(:(s ⟹ ¬¬s), ([:s], 2))

proof_of(:(s ⟹ s), ([:s], 1))

proof_of(:((s ⟹ ¬s) ⟹ ¬s), ([:s], 1))  #this has no proofs involving the given tautologies