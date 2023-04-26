------------------------------------------------------------------------
--
-- Public module for everything related to contexts
--
------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Context (Type : Set) where

open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n) renaming (_<_ to _≺_; _≤?_ to _≼?_; _+_ to _N+_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; _≢_; cong)
\end{code}

\begin{code}
infixl 5 _,_
\end{code}

--------------------------------------------------------------------------------

<Context>
\begin{code}
data Context : Set where
  ∅    : Context
  _,_  : Context → Type → Context
\end{code}

\begin{code}
private variable
  Γ Δ     : Context
  T T₁ T₂ : Type
\end{code}

<Context-Membership>
\begin{code}
data _∈_ : Type → Context → Set where
  Z   : T ∈ (Γ , T)
  S_  : T₁ ∈ Γ → T₁ ∈ (Γ , T₂)
\end{code}

<Context-Length>
\begin{code}
length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ )
\end{code}

<Context-Lookup>
\begin{code}
lookup : {Γ : Context} → {n : ℕ} → (p : n ≺ (length Γ)) → Type
lookup {Γ , A} {zero} (s≤s z≤n) = A
lookup {Γ , A} {suc n} (s≤s p) = lookup p
\end{code}

<Context-Count>
\begin{code}
count : ∀ {Γ} → {n : ℕ} → (p : n ≺ length Γ) → lookup p ∈ Γ
count {Γ , A} {zero} (s≤s z≤n) = Z
count {Γ , A} {suc n} (s≤s p) = S (count p)
\end{code}

<Context-Extension>
\begin{code}
ext : (∀ {t₁} → t₁ ∈ Γ → t₁ ∈ Δ ) → (∀ {t₁ t₂} → t₁ ∈ (Γ , t₂) → t₁ ∈ (Δ , t₂))
ext ρ Z = Z
ext ρ (S x) = S (ρ x)
\end{code}

Defining an order-preserving embedding (OPE)
<Context-Order>
\begin{code}
data _⊆_ : Context → Context → Set where
  ∅     : ∅ ⊆ ∅
  drop  : Γ ⊆ Δ →       Γ ⊆ (Δ , T)
  copy  : Γ ⊆ Δ → (Γ , T) ⊆ (Δ , T)
\end{code}

Composition of OPEs
\begin{code}
_∘_ : ∀ {Γ Δ Ε} → (τ : Δ ⊆ Γ) → (τ' : Ε ⊆ Δ) → Ε ⊆ Γ
∅      ∘ τ'       = τ'
drop τ ∘ τ'       = drop (τ ∘ τ')
copy τ ∘ drop τ'  = drop (τ ∘ τ')
copy τ ∘ copy τ'  = copy (τ ∘ τ')
\end{code}

\begin{code}
∅⊆Γ : ∀ {Γ} → ∅ ⊆ Γ
∅⊆Γ {∅} = ∅
∅⊆Γ {Γ , _} = drop ∅⊆Γ
\end{code}

<OPE-Id>
\begin{code}
⊆-id : Γ ⊆ Γ
⊆-id {∅} = ∅
⊆-id {Γ , _} = copy ⊆-id
\end{code}

<OPE-Weakening>
\begin{code}
⊆-wk : Γ ⊆ (Γ , T)
⊆-wk = drop ⊆-id
\end{code}

\begin{code}
⊆-refl : ∀ {Γ Δ Ε} → Γ ⊆ Ε → Ε ⊆ Δ → Γ ⊆ Δ
⊆-refl Γ⊆Ε ∅ = Γ⊆Ε
⊆-refl Γ⊆Ε (drop Ε⊆Δ) = drop (⊆-refl Γ⊆Ε Ε⊆Δ)
⊆-refl (drop Γ⊆Ε) (copy Ε⊆Δ) = drop (⊆-refl Γ⊆Ε Ε⊆Δ)
⊆-refl (copy Γ⊆Ε) (copy Ε⊆Δ) = copy (⊆-refl Γ⊆Ε Ε⊆Δ)
\end{code}

\begin{code}
⊆-refl-idₗ : ∀ {Γ Δ} → (Γ⊆Δ : Γ ⊆ Δ) → ⊆-refl Γ⊆Δ ⊆-id ≡ Γ⊆Δ
⊆-refl-idₗ ∅ = refl
⊆-refl-idₗ (drop Γ⊆Δ) rewrite ⊆-refl-idₗ Γ⊆Δ = refl
⊆-refl-idₗ (copy Γ⊆Δ) rewrite ⊆-refl-idₗ Γ⊆Δ = refl
\end{code}

\begin{code}
⊆-refl-idᵣ : ∀ {Γ Δ} → (Γ⊆Δ : Γ ⊆ Δ) → ⊆-refl ⊆-id Γ⊆Δ ≡ Γ⊆Δ
⊆-refl-idᵣ ∅ = refl
⊆-refl-idᵣ (drop Γ⊆Δ) rewrite ⊆-refl-idᵣ Γ⊆Δ = refl
⊆-refl-idᵣ (copy Γ⊆Δ) rewrite ⊆-refl-idᵣ Γ⊆Δ = refl
\end{code}
