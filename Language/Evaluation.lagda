------------------------------------------------------------------------
--
-- Evaluation of terms (Only for testing purposes)
--
------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Evaluation where

open import AbstractMachines.Language.Types
open import AbstractMachines.Language.Reduction
open import AbstractMachines.Language.Reduction.Properties
open import AbstractMachines.Language.Normalization

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; ∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to _⸴_)
\end{code}

--------------------------------------------------------------------------------

<Finished>
\begin{code}
data Finished {Γ T} (t : Γ ⊢ T) : Set where
  done : Value t → Finished t
  out-of-gas : Finished t
\end{code}

<Steps>
\begin{code}
data Steps {T} : ∅ ⊢ T → Set where
  steps : {t t' : ∅ ⊢ T} → t ↠ t' → Finished t' → Steps t
\end{code}

<Evaluate-Gas>
\begin{code}
eval-gas : ∀ {T} → ℕ → (t : ∅ ⊢ T) → Steps t
eval-gas zero t = steps ↠-refl out-of-gas
eval-gas (suc n) t with progress t
... | done v = steps ↠-refl (done v)
... | step {t'} t⟶t' with eval-gas n t'
... | steps t'↠t'' fin = steps (↠-trans (↠-step t⟶t') t'↠t'') fin
\end{code}

--------------------------------------------------------------------------------

\begin{code}
data _⇓ : ∀ {T} → (∅ ⊢ T) → Set where
  done : ∀ {T} {t t' : ∅ ⊢ T} → {t ↠ t'} → (val-t' : Value {T = T} t') → t ⇓
\end{code}

<Eval-Normalization>
\begin{code}
eval : ∀ {T} → (t : ∅ ⊢ T) → t ⇓
eval t with normalization t
... | t' ⸴ val-t' ⸴ t↠t' = done {_} {_} {_} {t↠t'} val-t'
\end{code}
