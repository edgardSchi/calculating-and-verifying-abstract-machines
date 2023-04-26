--------------------------------------------------------------------------------
-
- Defining substitution of contexts
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Substitution where

open import AbstractMachines.Language.Types hiding (ex1; ex2; ex3; ex4)
open import AbstractMachines.Language.Weakening

open import Relation.Binary.PropositionalEquality as EQ hiding ([_])
open EQ using (_≡_; refl; sym; cong)
open EQ.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
\end{code}

\begin{code}
private variable
  Γ Δ Ε   : Context
  T T₁ T₂ : Type
\end{code}

\begin{code}
infixl 5 _⊆-↷_
infixr 5 _↷-⊆_
\end{code}

--------------------------------------------------------------------------------

𝗦𝘂𝗯𝘀𝘁𝗶𝘁𝘂𝘁𝗶𝗼𝗻 𝗥𝗲𝗹𝗮𝘁𝗶𝗼𝗻
Instead of using a function T ∈ Γ → Δ ⊢ T that translate a variable from
context Γ to a term with context Δ, we use a substitution relation.
Γ ↷ Δ says that context Δ can be substituted by context Γ.
This allows doing proofs about substitutions.
<Sub-Relation>
\begin{code}
data _↷_ (Γ : Context) : Context → Set where
  ∅    : Γ ↷ ∅
  _,_  : Γ ↷ Δ → (Γ ⊢ T) → Γ ↷ (Δ , T)
\end{code}

If Γ is a subset of Ε and we can replace Δ by Γ, then we can also replace
Δ by Ε
<Subset-Substitute>
\begin{code}
_⊆-↷_ : Γ ⊆ Ε → Γ ↷ Δ → Ε ↷ Δ
_⊆-↷_ Γ⊆Ε ∅        = ∅
_⊆-↷_ Γ⊆Ε (σ , x)  = Γ⊆Ε ⊆-↷ σ , weaken Γ⊆Ε x
\end{code}

If Δ can be replace by Γ and Ε is a subset of Δ, then we can also replace
Ε by Γ
<Substitute-Subset>
\begin{code}
_↷-⊆_ : Γ ↷ Δ → Ε ⊆ Δ → Γ ↷ Ε
σ       ↷-⊆ ∅         = σ
(σ , T) ↷-⊆ drop Ε⊆Δ  = σ ↷-⊆ Ε⊆Δ
(σ , T) ↷-⊆ copy Ε⊆Δ  = (σ ↷-⊆ Ε⊆Δ) , T
\end{code}

Substituting Γ ⊆ Γ for some Γ and σ always yields σ again
\begin{code}
id-↷-⊆ : (σ : Γ ↷ Δ) → ⊆-id ⊆-↷ σ ≡ σ
id-↷-⊆ ∅                                        = refl
id-↷-⊆ (σ , x) rewrite id-↷-⊆ σ | wk-id≡refl x  = refl
\end{code}

Substituting Γ ⊆ Γ for some Γ and σ always yields σ again
\begin{code}
⊆-↷-id : (σ : Γ ↷ Δ) → σ ↷-⊆ ⊆-id ≡ σ
⊆-↷-id ∅                         = refl
⊆-↷-id (σ , _) rewrite ⊆-↷-id σ  = refl
\end{code}

If we can replace Δ by Γ, then we add a type T to both
contexts and the substitution relation holds with
(Γ , T) ↷ (Δ , T), extending the substitution
<Extend>
\begin{code}
extend : Γ ↷ Δ → (Γ , T) ↷ (Δ , T)
extend σ = ⊆-wk ⊆-↷ σ , (′ Z)
\end{code}

The substitution relation is reflexive
<Substitution-Relation-Reflexive>
\begin{code}
↷-refl : Γ ↷ Γ
↷-refl {∅}      = ∅
↷-refl {Γ , x}  = extend ↷-refl
\end{code}

\begin{code}
Γ↷Γ = ↷-refl
\end{code}

𝗩𝗮𝗿𝗶𝗮𝗯𝗹𝗲 𝗦𝘂𝗯𝘀𝘁𝗶𝘁𝘂𝘁𝗶𝗼𝗻
Substitute a variable of type T in context Δ with context
Γ to get a term of type T with context Γ
<Variable-Substitution>
\begin{code}
substituteⱽ : Γ ↷ Δ → T ∈ Δ → Γ ⊢ T
substituteⱽ (σ , x) Z      = x
substituteⱽ (σ , x) (S y)  = substituteⱽ σ y
\end{code}

𝗦𝘂𝗯𝘀𝘁𝗶𝘁𝘂𝘁𝗶𝗼𝗻
Given a substitution relation σ : Γ ↷ Δ and a term of type T with
context Δ, we substitute Δ for Γ and get a term of type T with
context Γ.
For terms that are not variables or introduce new variables, we
recursively substitute the substerms. For let- and λ-terms we
substitute the subterms and extend σ by the type of the variable.
The base case is substituting a variable, which is handled by the
substituteⱽ function.
<Substitution>
\begin{code}
substitute : Γ ↷ Δ → Δ ⊢ T → Γ ⊢ T
substitute σ true              = true
substitute σ false             = false
substitute σ (if t₁ then t₂ else t₃)
  = if substitute σ t₁ then substitute σ t₂ else substitute σ t₃
substitute σ (x N)             = x N
substitute σ (l ⟨ ⊕ ⟩ᵃ r)      = substitute σ l ⟨ ⊕ ⟩ᵃ substitute σ r
substitute σ (l ⟨ ⊙ ⟩ᶜ r)      = substitute σ l ⟨ ⊙ ⟩ᶜ substitute σ r
substitute σ (let' t₁ in' t₂)  = let' substitute σ t₁ in' substitute (extend σ) t₂
substitute σ (′ x)             = substituteⱽ σ x
substitute σ (ƛ t)             = ƛ substitute (extend σ) t
substitute σ (t₁ · t₂)         = substitute σ t₁ · substitute σ t₂
\end{code}

𝗦𝗶𝗻𝗴𝗹𝗲 𝗦𝘂𝗯𝘀𝘁𝗶𝘁𝘂𝘁𝗶𝗼𝗻
Performing single substitution with a term of type Γ ⊢ T₂ and one of type
(Γ , T₂) ⊢ T₁ to elimate a variable
<Single-Substitution>
\begin{code}
[_]_ : Γ ⊢ T₂ → (Γ , T₂) ⊢ T₁ → Γ ⊢ T₁
[_]_ t₂ t₁ = substitute (Γ↷Γ , t₂) t₁
\end{code}

The substitution relation is transivitve by using substitution
<Substitute-Relation-Transitive>
\begin{code}
_↷↷_ : Γ ↷ Ε → Ε ↷ Δ → Γ ↷ Δ
σ ↷↷ ∅ = ∅
σ ↷↷ (ρ , x) = σ ↷↷ ρ , substitute σ x
\end{code}

𝗩𝗮𝗿𝗶𝗮𝗯𝗹𝗲 𝗥𝗲𝗻𝗮𝗺𝗶𝗻𝗴
Given a variable of type T in context Γ, we can change the
context to Δ if Γ ⊆ Δ holds
<Variable-Renaming>
\begin{code}
renameⱽ : Γ ⊆ Δ → T ∈ Γ → T ∈ Δ
renameⱽ (drop Γ⊆Δ) x      = S renameⱽ Γ⊆Δ x
renameⱽ (copy Γ⊆Δ) Z      = Z
renameⱽ (copy Γ⊆Δ) (S x)  = S renameⱽ Γ⊆Δ x
\end{code}

𝗥𝗲𝗻𝗮𝗺𝗶𝗻𝗴
Given a term of type T with context Γ, we can change the
context to Δ if Γ ⊆ Δ holds.
It has the same structure as the substitution function defined
above. The base case is handled by the renameⱽ function.
\begin{code}
rename : Γ ⊆ Δ → Γ ⊢ T → Δ ⊢ T
rename Γ⊆Δ true             = true
rename Γ⊆Δ false            = false
rename Γ⊆Δ (if t₁ then t₂ else t₃)
  = if rename Γ⊆Δ t₁ then rename Γ⊆Δ t₂ else rename Γ⊆Δ t₃
rename Γ⊆Δ (n N)             = n N
rename Γ⊆Δ (l ⟨ ⊕ ⟩ᵃ r)      = rename Γ⊆Δ l ⟨ ⊕ ⟩ᵃ rename Γ⊆Δ r
rename Γ⊆Δ (l ⟨ ⊗ ⟩ᶜ r)      = rename Γ⊆Δ l ⟨ ⊗ ⟩ᶜ rename Γ⊆Δ r
rename Γ⊆Δ (let' t₁ in' t₂)  = let' rename Γ⊆Δ t₁ in' rename (copy Γ⊆Δ) t₂
rename Γ⊆Δ (′ x)             = ′ renameⱽ Γ⊆Δ x
rename Γ⊆Δ (ƛ t)             = ƛ rename (copy Γ⊆Δ) t
rename Γ⊆Δ (t₁ · t₂)         = rename Γ⊆Δ t₁ · rename Γ⊆Δ t₂
\end{code}

--------------------------------------------------------------------------------
-- Examples 
--------------------------------------------------------------------------------

\begin{code}
private module Sub-Examples where
\end{code}

<Examples>
\begin{code}
    ex1 : substitute {Γ = ∅ , Nat} (∅ , (42 N)) ((# 0) ⟨ + ⟩ᵃ (1 N))
        ≡
        (42 N) ⟨ + ⟩ᵃ (1 N)
    ex1 = refl

    ex2 : substitute {Γ = ∅} ∅ true ≡ true
    ex2 = refl

    ex3 : substitute
            {Γ = ∅ , Nat , Nat}
            (∅ , 42 N , 4711 N)
            (let' 10 N in' ((# 0) ⟨ + ⟩ᵃ ((# 1) ⟨ + ⟩ᵃ (# 2))))
          ≡
          let' 10 N in' ((# 0) ⟨ + ⟩ᵃ ((4711 N) ⟨ + ⟩ᵃ (42 N)))
    ex3 = refl
\end{code}

\begin{code}
private module Single-Sub-Examples where
\end{code}

<Single-Sub-Examples>
\begin{code}
  t₁ : ∅ ⊢ Bool
  t₁ = true
  ex1 : [ t₁ ] (# 0) ≡ t₁
  ex1 = refl

  t₂ : ∅ , Nat , Bool ⇒ Nat ⇒ Nat , Nat ⊢ Nat
  t₂ = (1 N) ⟨ + ⟩ᵃ (2 N)
  t₃ : ∅ , Nat , Bool ⇒ Nat ⇒ Nat , Nat , Nat ⊢ Nat
  t₃ = (# 0) ⟨ + ⟩ᵃ (3 N)
  ex2 : [ t₂ ] t₃
        ≡
        ((1 N) ⟨ + ⟩ᵃ (2 N)) ⟨ + ⟩ᵃ (3 N)
  ex2 = refl

  t₄ : ∅ , Nat ⇒ Nat , Nat ⊢ Nat
  t₄ = (# 1) · (# 0)
  t₅ : ∅ , Nat ⇒ Nat , Nat , Nat ⊢ Nat
  t₅ = # 1
  ex3 : [ t₄ ] t₅ ≡ (# 0)
  ex3 = refl
\end{code}
