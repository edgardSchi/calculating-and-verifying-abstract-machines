--------------------------------------------------------------------------------
-
- Big-Step Structural Operational Semantics
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Big-Step where

open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import AbstractMachines.Language.Types
open import AbstractMachines.Language.BinaryOperation
open import AbstractMachines.Language.Substitution

open import AbstractMachines.Language.Reduction
open import AbstractMachines.Language.Normalization
\end{code}

--------------------------------------------------------------------------------

\begin{code}
private variable
  Γ : Context
  T T₁ T₂ : Type
  n : ℕ
  ⊕ : ArithmeticOp
  ⊙ : CompareOp
\end{code}

--------------------------------------------------------------------------------

\begin{code}
mutual
\end{code}

In big-step, a closure is used as a value to capture a term and environment.
Values are not longer a special type of term, but indexed with their type
<Value-Definition>
\begin{code}
    data Valueᴮ : Type → Set where
        closure  : ∀ (t : Γ , T₁ ⊢ T₂)
                   → Environmentᴮ Γ
                   ----------------
                   → Valueᴮ (T₁ ⇒ T₂)
        true     : Valueᴮ Bool
        false    : Valueᴮ Bool
        _N       : ∀ (n : ℕ) → Valueᴮ Nat
\end{code}

𝗘𝗻𝘃𝗶𝗿𝗼𝗻𝗺𝗲𝗻𝘁
The environment is simply a list of values, indexed by a context to retrieve
values with from variables T ∈ Γ
<Env-Definition>
\begin{code}
    data Environmentᴮ : Context → Set where
        ∅     : Environmentᴮ ∅
        _,ᴮ_  : Environmentᴮ Γ
              → Valueᴮ T
              --------------------
              → Environmentᴮ (Γ , T)
\end{code}

Lookup function for environments
<Lookup>
\begin{code}
lookupᴮ : Environmentᴮ Γ → T ∈ Γ → Valueᴮ T
lookupᴮ (γ ,ᴮ x) Z = x
lookupᴮ (γ ,ᴮ x) (S y) = lookupᴮ γ y
\end{code}

--------------------------------------------------------------------------------

\begin{code}
private variable
    Δ : Context
    γ : Environmentᴮ Γ
    δ : Environmentᴮ Δ

N↑ᴮ : Valueᴮ Nat → ℕ
N↑ᴮ (n N) = n

𝔹↓ᴮ : 𝔹 → Valueᴮ Bool
𝔹↓ᴮ false = false
𝔹↓ᴮ true = true
\end{code}

--------------------------------------------------------------------------------
- Big-Step Evaluation
--------------------------------------------------------------------------------

𝗕𝗶𝗴-𝗦𝘁𝗲𝗽 𝗘𝘃𝗮𝗹𝘂𝗮𝘁𝗶𝗼𝗻 𝗥𝗲𝗹𝗮𝘁𝗶𝗼𝗻
Big-Step relates an environment, term and value.
<Big-Step-Rules>
\begin{code}
data _⊢_⇓_ : Environmentᴮ Γ → Γ ⊢ T → Valueᴮ T → Set where
    True      : γ ⊢ true ⇓ true
    False     : γ ⊢ false ⇓ false
    Num       : γ ⊢ (n N) ⇓ (n N)
    Var       : ∀ {x : T ∈ Γ} → {v : Valueᴮ T}
                → {l : lookupᴮ γ x ≡ v}
                --------------
                → γ ⊢ ′ x  ⇓ v
    App       : ∀ {t₁ : Γ ⊢ T₁ ⇒ T₂} {t₂ : Γ ⊢ T₁} {t : Δ , T₁ ⊢ T₂}
                → {v : Valueᴮ T₂} {v₂ : Valueᴮ T₁}
                → γ ⊢ t₁ ⇓ closure t δ
                → γ ⊢ t₂ ⇓ v₂
                → (δ ,ᴮ v₂) ⊢ t ⇓ v
                -------------------
                → γ ⊢ t₁ · t₂ ⇓ v
    Lambda    : ∀ {t : Γ , T₁ ⊢ T₂}
                → γ ⊢ (ƛ t) ⇓ closure t γ
    Let       : ∀ {t₁ : Γ ⊢ T₁} {t₂ : Γ , T₁ ⊢ T₂}
                → {v₁ : Valueᴮ T₁} {v : Valueᴮ T₂}
                → γ ⊢ t₁ ⇓ v₁
                → (γ ,ᴮ v₁) ⊢ t₂ ⇓ v
                --------------
                → γ ⊢ let' t₁ in' t₂ ⇓ v
    If-True   : ∀ {t₁ : Γ ⊢ Bool} {t₂ t₃ : Γ ⊢ T} {v : Valueᴮ T}
                → γ ⊢ t₁ ⇓ true
                → γ ⊢ t₂ ⇓ v
                --------------
                → γ ⊢ (if t₁ then t₂ else t₃) ⇓ v
    If-False  : ∀ {t₁ : Γ ⊢ Bool} {t₂ t₃ : Γ ⊢ T} {v : Valueᴮ T}
                → γ ⊢ t₁ ⇓ false
                → γ ⊢ t₃ ⇓ v
                --------------
                → γ ⊢ (if t₁ then t₂ else t₃) ⇓ v
    Arith     : ∀ {t₁ t₂ : Γ ⊢ Nat}
                → {n₁ n₂ : Valueᴮ Nat}
                → γ ⊢ t₁ ⇓ n₁
                → γ ⊢ t₂ ⇓ n₂
                --------------
                → γ ⊢ t₁ ⟨ ⊕ ⟩ᵃ t₂ ⇓ (⟦ ⊕ ⟧ᵃ (N↑ᴮ n₁) (N↑ᴮ n₂) N)
    Comp      : ∀ {t₁ t₂ : Γ ⊢ Nat}
                → {n₁ n₂ : ℕ}
                → γ ⊢ t₁ ⇓ (n₁ N)
                → γ ⊢ t₂ ⇓ (n₂ N)
                --------------
                → γ ⊢ t₁ ⟨ ⊙ ⟩ᶜ t₂ ⇓ 𝔹↓ᴮ (⟦ ⊙ ⟧ᶜ n₁ n₂)
\end{code}
