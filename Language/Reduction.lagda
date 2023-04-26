--------------------------------------------------------------------------------
-
- Defining the reduction rules of the language
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Reduction where

open import AbstractMachines.Language.Types
open import AbstractMachines.Language.Substitution
open import AbstractMachines.Language.BinaryOperation
\end{code}

\begin{code}
private variable
  Γ        : Context
  T T₁ T₂  : Type
  ⊕        : ArithmeticOp
  ⊙        : CompareOp
  t t' t'' : Γ ⊢ T

infixr 1 _⟶_
\end{code}

--------------------------------------------------------------------------------

𝗥𝗲𝗱𝘂𝗰𝘁𝗶𝗼𝗻 𝗥𝗲𝗹𝗮𝘁𝗶𝗼𝗻
The reduction rules of the language
ξ-rules are reducing a part of a term until it is a value
β-rules "deconstruct" a term, making it simpler
<Reduction-Relation>
\begin{code}
data _⟶_ : (Γ ⊢ T) → (Γ ⊢ T) → Set where
  ξ-·₁ :      ∀ {t₁ t₁' : Γ ⊢ T₁ ⇒ T₂} {t₂ : Γ ⊢ T₁}
              → t₁ ⟶ t₁'
              --------------------
              → t₁ · t₂ ⟶ t₁' · t₂

  ξ-·₂ :      ∀ {v : Γ ⊢ T₁ ⇒ T₂} {t t' : Γ ⊢ T₁}
              → Value v
              → t ⟶ t'
              ----------------
              → v · t ⟶ v · t'

  β-ƛ :       ∀ {t : Γ , T₁ ⊢ T₂} {v : Γ ⊢ T₁}
              → Value v
              ---------------------
              → (ƛ t) · v ⟶ [ v ] t

  ξ-If :      ∀ {t₁ t₁' : Γ ⊢ Bool}
              → {t₂ t₃ : Γ ⊢ T}
              → t₁ ⟶ t₁'
              ------------------------------------------------
              → if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃

  β-If₁ :     ∀ {t₁ t₂ : Γ ⊢ T}
              ------------------------------
              → if true then t₁ else t₂ ⟶ t₁

  β-If₂ :     ∀ {t₁ t₂ : Γ ⊢ T}
              -------------------------------
              → if false then t₁ else t₂ ⟶ t₂

  ξ-Arith₁ :  ∀ {t₁ t₁' t₂ : Γ ⊢ Nat}
              → t₁ ⟶ t₁'
              ------------------------------
              → t₁ ⟨ ⊕ ⟩ᵃ t₂ ⟶ t₁' ⟨ ⊕ ⟩ᵃ t₂

  ξ-Arith₂ :  ∀ {v₁ : Γ ⊢ Nat} {t₂ t₂' : Γ ⊢ Nat}
              → Value v₁
              → t₂ ⟶ t₂'
              ------------------------------
              → v₁ ⟨ ⊕ ⟩ᵃ t₂ ⟶ v₁ ⟨ ⊕ ⟩ᵃ t₂'

  β-Arith :   ∀ {v₁ v₂ : Γ ⊢ Nat}
              → (nv₁ : Value v₁)
              → (nv₂ : Value v₂)
              -------------------------------------------
              → v₁ ⟨ ⊕ ⟩ᵃ v₂ ⟶ ⟦ ⊕ ⟧ᵃ (N↑ nv₁) (N↑ nv₂) N

  ξ-Comp₁ :   ∀ {t₁ t₁' t₂ : Γ ⊢ Nat}
              → t₁ ⟶ t₁'
              ------------------------------
              → t₁ ⟨ ⊙ ⟩ᶜ t₂ ⟶ t₁' ⟨ ⊙ ⟩ᶜ t₂

  ξ-Comp₂ :   ∀ {v₁ : Γ ⊢ Nat} {t₂ t₂' : Γ ⊢ Nat}
              → Value v₁
              → t₂ ⟶ t₂'
              ------------------------------
              → v₁ ⟨ ⊙ ⟩ᶜ t₂ ⟶ v₁ ⟨ ⊙ ⟩ᶜ t₂'

  β-Comp :    ∀ {v₁ v₂ : Γ ⊢ Nat}
              → (nv₁ : Value v₁)
              → (nv₂ : Value v₂)
              ----------------------------------------------
              → v₁ ⟨ ⊙ ⟩ᶜ v₂ ⟶ 𝔹↓ (⟦ ⊙ ⟧ᶜ (N↑ nv₁) (N↑ nv₂))

  ξ-Let :     ∀ {t₁ t₁' : Γ ⊢ T₁} {t₂ : Γ , T₁ ⊢ T₂}
              → t₁ ⟶ t₁'
              ----------------------------------
              → let' t₁ in' t₂ ⟶ let' t₁' in' t₂

  β-Let :     ∀ {v₁ : Γ ⊢ T₁} {t₂ : Γ , T₁ ⊢ T₂}
              → Value v₁
              ----------------------------
              → let' v₁ in' t₂ ⟶ [ v₁ ] t₂
\end{code}

--------------------------------------------------------------------------------

𝗠𝘂𝗹𝘁𝗶𝘀𝘁𝗲𝗽 𝗥𝗲𝗹𝗮𝘁𝗶𝗼𝗻
The multistep relation is the reflexive, transitive closure of the small
step relation.
<Multi-Step-Relation>
\begin{code}
data _↠_ : Γ ⊢ T → Γ ⊢ T → Set where
  ↠-step   : t ⟶ t' → t ↠ t'
  ↠-refl   : t ↠ t
  ↠-trans  : t ↠ t' → t' ↠ t'' → t ↠ t''
\end{code}

\begin{code}
pattern _↠↠_ t↠t' t'↠t'' = ↠-trans t↠t' t'↠t''

by-definition : t ↠ t
by-definition = ↠-refl
\end{code}

--------------------------------------------------------------------------------

\begin{code}
infix 1 ↠begin_
infixr 2 _↠⟨_⟩_ _⟶⟨_⟩_
infix 3 _↠∎
\end{code}

\begin{code}
↠begin_ : ∀ {Γ T} {x y : Γ ⊢ T} → x ↠ y → x ↠ y
↠begin_ x↠y = x↠y
\end{code}

\begin{code}
_↠⟨_⟩_ : ∀ {Γ T} {u v} → (t : Γ ⊢ T) → t ↠ u → u ↠ v → t ↠ v
_↠⟨_⟩_ t t↠u u↠v = ↠-trans t↠u u↠v
\end{code}

\begin{code}
_⟶⟨_⟩_ : ∀ {Γ T} {u v} → (t : Γ ⊢ T) → t ⟶ u → u ↠ v → t ↠ v
_⟶⟨_⟩_ t t⟶u u↠v = ↠-trans (↠-step t⟶u) u↠v
\end{code}

\begin{code}
_↠∎ : ∀ {Γ T} → (t : Γ ⊢ T) → t ↠ t
_↠∎ t = ↠-refl
\end{code}

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

\begin{code}
private module Example where
\end{code}

<Ex>
\begin{code}
  t₁ : ∅ ⊢ Bool
  t₁ = ((if ((2 N) ⟨ + ⟩ᵃ (4 N)) ⟨ < ⟩ᶜ (3 N) then (1 N) else (0 N))
       ⟨ ≈ ⟩ᶜ
       (42 N))

  ex : t₁ ↠ false
  ex = 
\end{code}

<Example>
\begin{code}
    ↠begin
        (if ((2 N) ⟨ + ⟩ᵃ (4 N)) ⟨ < ⟩ᶜ (3 N) then (1 N) else (0 N)) ⟨ ≈ ⟩ᶜ (42 N)
    ⟶⟨ ξ-Comp₁ (ξ-If (ξ-Comp₁ (β-Arith (2 N) (4 N)))) ⟩
        (if (6 N) ⟨ < ⟩ᶜ (3 N) then (1 N) else (0 N)) ⟨ ≈ ⟩ᶜ (42 N)
    ⟶⟨ ξ-Comp₁ (ξ-If (β-Comp (6 N) (3 N))) ⟩
        (if false then (1 N) else (0 N)) ⟨ ≈ ⟩ᶜ (42 N)
    ⟶⟨ ξ-Comp₁ β-If₂ ⟩
        (0 N) ⟨ ≈ ⟩ᶜ (42 N)
    ⟶⟨ β-Comp (0 N) (42 N) ⟩
        false
    ↠∎
\end{code}
