# NK-0 Typing Rules (Normative)

Judgment forms:
- Γ ⊢ e : T
- Γ ⊢ s ok   (statement well-typed)
- Γ ⊢ f ok   (function well-typed)
- Γ ⊢ M ok   (module well-typed)

## Base types
T ∈ {Real, Bool, State, Field}

## Variables
If x:T ∈ Γ, then Γ ⊢ x : T.

## Literals
Γ ⊢ n : Real
Γ ⊢ true : Bool
Γ ⊢ false : Bool
Γ ⊢ "..." : Field   (NK-0 treats strings as Field atoms only if declared; otherwise disallow in strict mode)

## Binary ops (core)
If Γ ⊢ a:Real and Γ ⊢ b:Real then:
- Γ ⊢ a+b : Real, a-b : Real, a*b : Real, a/b : Real

If Γ ⊢ a:T and Γ ⊢ b:T then:
- Γ ⊢ a==b : Bool

If Γ ⊢ a:Real and Γ ⊢ b:Real then:
- Γ ⊢ a<=b : Bool, a>=b : Bool

## Calls
Functions are declared with (T1..Tn) -> Tout.
If Γ ⊢ ei:Ti for all i, then Γ ⊢ f(e1..en) : Tout.

## Statements
let x = e; is ok iff Γ ⊢ e:T and Γ,x:T ⊢ subsequent stmts ok.
return e; is ok iff Γ ⊢ e : Tout (declared return type)
assert p; is ok iff Γ ⊢ p : Bool

## Module
A module is ok iff:
1) all imported module names resolve (link-time)
2) invariants are Bool expressions under module scope Γ_M
3) all functions are well-typed
4) budget is a Real ≥ 0 literal in NK-0 strict mode
