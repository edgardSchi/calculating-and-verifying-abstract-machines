--------------------------------------------------------------------------------
-
- Types and Terms of the Language
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Types where

open import Data.Nat using (ℕ; suc; zero; _≤?_)
open import Data.Bool renaming (Bool to 𝔹) hiding (if_then_else_; T; _≤?_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (∃; ∃-syntax; _×_; proj₁; proj₂)
\end{code}

\begin{code}
infixr 7 _⇒_
infix 4 _⊢_
\end{code}

--------------------------------------------------------------------------------

𝗧𝘆𝗽𝗲𝘀
The types the language has
<Type>
\begin{code}
data Type : Set where
  _⇒_   : Type → Type → Type
  Nat   : Type
  Bool  : Type
\end{code}

\begin{code}
open import AbstractMachines.Language.BinaryOperation public
open import AbstractMachines.Context Type public
\end{code}

\begin{code}
private variable
  Γ Δ      : Context
  T T₁ T₂  : Type
\end{code}

𝗧𝗲𝗿𝗺𝘀
Intrisically typed terms using DeBruijn indices.
Based on the PLFA chapter "DeBruijn"
<Typing-Judgment>
\begin{code}
data _⊢_ : Context → Type → Set where
  true           : Γ ⊢ Bool

  false          : Γ ⊢ Bool

  if_then_else_  : Γ ⊢ Bool
                 → Γ ⊢ T
                 → Γ ⊢ T
                 --------
                 → Γ ⊢ T

  _N             : ∀ (n : ℕ)
                 ---------
                 → Γ ⊢ Nat

  _⟨_⟩ᵃ_         : Γ ⊢ Nat
                 → ArithmeticOp
                 → Γ ⊢ Nat
                 ---------
                 → Γ ⊢ Nat 

  _⟨_⟩ᶜ_         : Γ ⊢ Nat
                 → CompareOp
                 → Γ ⊢ Nat
                 ----------
                 → Γ ⊢ Bool

  let'_in'_      : Γ ⊢ T₁
                 → (Γ , T₁) ⊢ T₂
                 ----------------
                 → Γ ⊢ T₂

  ′_             : T ∈ Γ
                 --------
                 → Γ ⊢ T

  ƛ_             : (Γ , T₁) ⊢ T₂
                 ----------------
                 → Γ ⊢ (T₁ ⇒ T₂)

  _·_            : Γ ⊢ (T₁ ⇒ T₂)
                 → Γ ⊢ T₁
                 ----------------
                 → Γ ⊢ T₂
\end{code}

Helper function for declaring DeBruijn indices based
on the provided natural number
<DeBruijn-Helper>
\begin{code}
#_ : ∀ {Γ} → (n : ℕ) → {n∈Γ : True (suc n ≤? length Γ)}
   → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = ′ count (toWitness n∈Γ)
\end{code}

𝗩𝗮𝗹𝘂𝗲𝘀
The values of the language
Note: the constructor ƛⱽ_ has the superscript to avoid name clashes with the term
constructor. However, it is kinda ugly
<Value>
\begin{code}
data Value : Γ ⊢ T → Set where
  true   : Value (true {Γ})
  false  : Value (false {Γ})
  _N     : ∀ n → Value (_N {Γ} n)
  ƛⱽ_    : ∀ (t : Γ , T₁ ⊢ T₂) → Value (ƛ_ {Γ} t)
\end{code}

Function to lift a natural number from the language into Agda
<NatVal-To-Natural>
\begin{code}
N↑ : ∀ {n : Γ ⊢ Nat} → Value n → ℕ
N↑ (n N) = n
\end{code}

Function to transform a boolean from Agda into the language
<Bool-To-BoolVal>
\begin{code}
𝔹↓ : 𝔹 → Γ ⊢ Bool
𝔹↓ false  = false
𝔹↓ true   = true
\end{code}

Every reification yields a value
\begin{code}
𝔹↓ⱽ : ∀ {b : 𝔹} {Γ} → Value {Γ} (𝔹↓ b)
𝔹↓ⱽ {false} = false
𝔹↓ⱽ {true} = true
\end{code}

Helper function for turning a comparison into a value
\begin{code}
⟦⟧ᶜ-val : ∀ {Γ ⊕} → (a : ℕ) (b : ℕ) → Value {Γ = Γ} (𝔹↓ (⟦ ⊕ ⟧ᶜ a b))
⟦⟧ᶜ-val {_} {⊕} a b with ⟦ ⊕ ⟧ᶜ a b
... | false = false
... | true = true
\end{code}

--------------------------------------------------------------------------------
- Examples
--------------------------------------------------------------------------------

<Examples>
\begin{code}
ex1 : ∅ ⊢ Nat
ex1 = if ((2 N) ⟨ + ⟩ᵃ (4 N)) ⟨ < ⟩ᶜ (3 N) then (1 N) else (0 N)

ex2 : ∅ , Nat ⊢ Bool
ex2 = let' (42 N) in' (((# 1) ⟨ * ⟩ᵃ (# 0)) ⟨ ≈ ⟩ᶜ (100 N))

ex3 : ∅ ⊢ Nat ⇒ Bool
ex3 = ƛ ((0 N) ⟨ ≈ ⟩ᶜ (# 0))

ex4 : ∅ ⊢ Bool
ex4 = ex3 · (4711 N)
\end{code}
