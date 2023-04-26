------------------------------------------------------------------------
--
-- Binary operations used within the language
-- 
------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.BinaryOperation where

open import Data.Nat using (ℕ; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _+_; _∸_; _*_)
open import Data.Bool using (true; false; not) renaming (Bool to 𝔹)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
\end{code}

------------------------------------------------------------------------

<Arithmetic-operator-definition>
\begin{code}
data ArithmeticOp : Set where
  + : ArithmeticOp
  ∸ : ArithmeticOp
  * : ArithmeticOp
\end{code}

\begin{code}
⟦_⟧ᵃ : ArithmeticOp → (ℕ → ℕ → ℕ)
⟦ + ⟧ᵃ = _+_
⟦ ∸ ⟧ᵃ = _∸_
⟦ * ⟧ᵃ = _*_
\end{code}

<Compare-operator-definition>
\begin{code}
data CompareOp : Set where
  ≈ : CompareOp
  ≠ : CompareOp
  < : CompareOp
  ≤ : CompareOp
  > : CompareOp
  ≥ : CompareOp
\end{code}

<Mapping-compare-operations>
\begin{code}
⟦_⟧ᶜ : CompareOp → (ℕ → ℕ → 𝔹)
⟦ ≈ ⟧ᶜ = λ a b → a ≡ᵇ b
⟦ ≠ ⟧ᶜ = λ a b → not (a ≡ᵇ b)
⟦ < ⟧ᶜ = λ a b → a <ᵇ b
⟦ ≤ ⟧ᶜ = λ a b → a ≤ᵇ b
⟦ > ⟧ᶜ = λ a b → not (a ≤ᵇ b)
⟦ ≥ ⟧ᶜ = λ a b → b ≤ᵇ a
\end{code}
