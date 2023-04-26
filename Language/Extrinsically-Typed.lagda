--------------------------------------------------------------------------------
-
- Testing of intrinsically typed term (not used in the thesis and broken)
-
--------------------------------------------------------------------------------

\begin{code}
module AbstractMachines.Language where

open import Data.String -- TODO: put this in Identifier
open import Data.String.Properties
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.List.Relation.Binary.Pointwise using (_∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
  
-- open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as Nat
open Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.DivMod using (_/_)
--open import Data.List using (List; _++_; length; reverse; map; foldr; downFrom; _∷_; [])
\end{code}

TODO:
  - Move arithmetic and compare operations to different file
  - Figure out how to do the compare operations
  - Evaluation rules of compare operations
  - Make own division operation
  - Better name for let expressions
  - Operator binding levels
  - Check the β-Arith rule
  - Rename Exp to Term

<Identifier>
\begin{code}
Id : Set
Id = String
\end{code}

<Types>
\begin{code}
data Type : Set where
  Bool : Type
  Nat  : Type
  _⇾_  : Type → Type → Type
\end{code}

<Arithmetic-operator-definition>
\begin{code}
data ArithmeticOp : Set where
  + : ArithmeticOp
  ∸ : ArithmeticOp
  · : ArithmeticOp
--  ÷ : ArithmeticOp
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

<Mapping-arithmetic-operations>
\begin{code}
⟦_⟧ᵃ : ArithmeticOp → (ℕ → ℕ → ℕ)
⟦ + ⟧ᵃ = Nat._+_
⟦ ∸ ⟧ᵃ = Nat._∸_
⟦ · ⟧ᵃ = Nat._*_
-- ⟦ ÷ ⟧ᵃ = {!(_/_)!} -- TODO: make own division operation
\end{code}

<Mapping-compare-operations>
\begin{code}
--⟦_⟧ᶜ : CompareOp → (ℕ → ℕ → Bool)
--⟦ x ⟧ᶜ = ?
\end{code}



TODO: Fix operator levels

<Expressions>
\begin{code}
data Exp : Set where
  -- Booleans
  false : Exp
  true  : Exp
  if_then_else_ : Exp → Exp → Exp → Exp
  -- Naturals
  _N    : ℕ → Exp
  --- Arithmetic Operations
  _⟨_⟩ᵃ_ : Exp → ArithmeticOp → Exp → Exp
  --- Comparision Operations
  _⟨_⟩ᶜ_ : Exp → CompareOp → Exp → Exp
  -- Let Binding
  ′_ : Id → Exp
  let'_≈_in'_ : Id → Exp → Exp → Exp -- TODO: Better name
  -- Function
  ƛ_⦂_∙_ : Id → Type → Exp → Exp
  -- Application
  _∙_ : Exp → Exp → Exp
\end{code}

\begin{code}
private variable
  e : Exp
  e₁ : Exp
  e₂ : Exp
  e₃ : Exp
\end{code}


<Values>
\begin{code}
data Value : Exp → Set where
  V-False : Value false
  V-True  : Value true
  V-Nat   : ∀ n → Value (n N)
  V-Lamb  : ∀ x t e → Value (ƛ x ⦂ t ∙ e)
\end{code}




Idea from https://github.com/nad/chi/blob/master/src/Free-variables.agda
<Free-Variables>
\begin{code}
data _∈FV_ (x : Id) : Exp → Set where
  Var     : ∀ {y} → x ≡ y → x ∈FV (′ y)
  Lambda  : ∀ {y e t} → x ≢ y → x ∈FV e → x ∈FV (ƛ y ⦂ t ∙ e)
  Applyₗ  : x ∈FV e₁ → x ∈FV (e₁ ∙ e₂)
  Applyᵣ  : x ∈FV e₂ → x ∈FV (e₁ ∙ e₂)
  If₁     : x ∈FV e₁ → x ∈FV (if e₁ then e₂ else e₃)
  If₂     : x ∈FV e₂ → x ∈FV (if e₁ then e₂ else e₃)
  If₃     : x ∈FV e₃ → x ∈FV (if e₁ then e₂ else e₃)
  Arith₁  : ∀ {⊕} → x ∈FV e₁ → x ∈FV (e₁ ⟨ ⊕ ⟩ᵃ e₂)
  Arith₂  : ∀ {⊕} → x ∈FV e₂ → x ∈FV (e₁ ⟨ ⊕ ⟩ᵃ e₂)
  Comp₁   : ∀ {⊕} → x ∈FV e₁ → x ∈FV (e₁ ⟨ ⊕ ⟩ᶜ e₂)
  Comp₂   : ∀ {⊕} → x ∈FV e₂ → x ∈FV (e₁ ⟨ ⊕ ⟩ᶜ e₂)
  Let₁     : ∀ {y} → x ≢ y → x ∈FV e₁ → x ∈FV (let' y ≈ e₁ in' e₂)
  Let₂     : ∀ {y} → x ≢ y → x ∈FV e₂ → x ∈FV (let' y ≈ e₁ in' e₂)
\end{code}

\begin{code}
FV-Test : "x" ∈FV (ƛ "y" ⦂ Nat ∙ ((′ "x") ∙ (′ "y")))
FV-Test = Lambda (λ ()) (Applyₗ (Var refl))
\end{code}

<Non-Free-Variables>
\begin{code}
_∉FV_ : Id → Exp → Set
x ∉FV t = ¬ (x ∈FV t)
\end{code}

\begin{code}
If-∉FV : ∀ {x} → x ∉FV e₁ → x ∉FV e₂ → x ∉FV e₃ → x ∉FV (if e₁ then e₂ else e₃)
If-∉FV ∉e₁ ∉e₂ ∉e₃ = λ {
                         (If₁ x∈FVe₁) → ∉e₁ x∈FVe₁
                       ; (If₂ x∈FVe₂) → ∉e₂ x∈FVe₂
                       ; (If₃ x∈FVe₃) → ∉e₃ x∈FVe₃
                       }
\end{code}

\begin{code}
_∈FV?_ : (x : Id) → (e : Exp) → Dec (x ∈FV e)
x ∈FV? false   = no (λ ())
x ∈FV? true    = no (λ ())
x ∈FV? (if e₁ then e₂ else e₃) with x ∈FV? e₁
... | yes  p₁  = yes  (If₁ p₁)
... | no   p₁  with x ∈FV? e₂
... | yes  p₂  = yes  (If₂ p₂)
... | no   p₂  with x ∈FV? e₃
... | yes  p₃  = yes  (If₃ p₃)
... | no   p₃  = no   (If-∉FV p₁ p₂ p₃)
x ∈FV? (x₁ N)  = no (λ ())
x ∈FV? (e₁ ⟨ ⊕ ⟩ᵃ e₂) with x ∈FV? e₁
... | yes p₁   = yes (Arith₁ p₁)
... | no  p₁   with x ∈FV? e₂
... | yes p₂   = yes (Arith₂ p₂)
... | no  p₂   = no λ{
                       (Arith₁ x∈FV) → p₁ x∈FV
                     ; (Arith₂ x∈FV) → p₂ x∈FV
                     }
x ∈FV? (e₁ ⟨ ⊕ ⟩ᶜ e₂) with x ∈FV? e₁
... | yes p₁   = yes (Comp₁ p₁)
... | no  p₁   with x ∈FV? e₂
... | yes p₂   = yes (Comp₂ p₂)
... | no  p₂   = no λ{
                       (Comp₁ x∈FV) → p₁ x∈FV
                     ; (Comp₂ x∈FV) → p₂ x∈FV
                     }
x ∈FV? (′ y) with x ≟ y
... | yes p = yes (Var p)
... | no  p = no λ { (Var y) → p y}
x ∈FV? (let' y ≈ e₁ in' e₂) with x ≟ y
... | yes x≡y = no λ{
                     (Let₁ x x∈FV) → x x≡y
                   ; (Let₂ x x∈FV) → x x≡y
                   }
... | no  x≢y with x ∈FV? e₁
... | yes p₁ = yes (Let₁ x≢y p₁)
... | no  p₁ with x ∈FV? e₂
... | yes p₂ = yes (Let₂ x≢y p₂)
... | no  p₂ = no λ{
                     (Let₁ x x∈FV) → p₁ x∈FV
                   ; (Let₂ x x∈FV) → p₂ x∈FV
                   }
x ∈FV? (ƛ y ⦂ t ∙ e) with x ≟ y
... | yes p₁ = no λ{ (Lambda x≢y x∈FV) → x≢y p₁}
... | no  p₁ with x ∈FV? e
... | yes p₂ = yes (Lambda p₁ p₂)
... | no  p₂ = no λ{ (Lambda x x∈FV) → p₂ x∈FV}
x ∈FV? (e₁ ∙ e₂) with x ∈FV? e₁
... | yes p₁ = yes (Applyₗ p₁)
... | no  p₁ with x ∈FV? e₂
... | yes p₂ = yes (Applyᵣ p₂)
... | no  p₂ = no λ{
                     (Applyₗ x∈FV) → p₁ x∈FV
                   ; (Applyᵣ x∈FV) → p₂ x∈FV
                   }
\end{code}

\begin{code}
α-conversion : Set
α-conversion = {!!}
\end{code}

Based on Pierce Definition 5.3.5
<Subsituition>
\begin{code}
[_↦_]_ : Id → Exp → Exp → Exp
[ x ↦ e₁ ] false = false
[ x ↦ e₁ ] true = true
[ x ↦ e₁ ] (if e₂ then e₃ else e₄) =  (if ([ x ↦ e₁ ] e₂) then ([ x ↦ e₁ ] e₃) else ([ x ↦ e₁ ] e₄))
[ x ↦ e₁ ] (x₁ N) = x₁ N
[ x ↦ e₁ ] (e₂ ⟨ x₁ ⟩ᵃ e₃) = (([ x ↦ e₁ ] e₂) ⟨ x₁ ⟩ᵃ ([ x ↦ e₁ ] e₃))
[ x ↦ e₁ ] (e₂ ⟨ x₁ ⟩ᶜ e₃) = (([ x ↦ e₁ ] e₂) ⟨ x₁ ⟩ᶜ ([ x ↦ e₁ ] e₃))
[ x ↦ e₁ ] ′ y with x ≟ y
... | yes _ = e₁
... | no _  = ′ y
[ x ↦ e₁ ] (let' y ≈ e₂ in' e₃) with x ≟ y
... | yes p = let' y ≈ e₂ in' e₃
... | no  p = {!!}
[ x ↦ e₁ ] (ƛ y ⦂ t ∙ e₂) with x ≟ y | y ∈FV? e₁
... | yes _ | _ = (ƛ y ⦂ t ∙ e₂)
... | no _  | yes p =  (ƛ y ⦂ t ∙ e₂)
... | no _  | no  _ = ƛ y ⦂ t ∙ ([ x ↦ e₁ ] e₂)
[ x ↦ e₁ ] (e₂ ∙ e₃) =  ([ x ↦ e₁ ] e₂) ∙ ([ x ↦ e₁ ] e₃)

_ : [ "x" ↦ (3 N) ] (ƛ "y" ⦂ Nat ∙ ((′ "x") ⟨ + ⟩ᵃ (′ "y"))) ≡ (ƛ "y" ⦂ Nat ∙ ((′ "x") ⟨ + ⟩ᵃ (′ "y")))
_ = {!!}
\end{code}

<Rules>
\begin{code}
data _⟶_ : Exp → Exp → Set where
  ξ-IF : ∀ {e₁'}
       → e₁ ⟶ e₁'
       -----------
       → (if e₁ then e₂ else e₃) ⟶ (if e₁' then e₂ else e₃)
  β-IF-True  : (if true then e₂ else e₃)  ⟶ e₂
  β-IF-False : (if false then e₂ else e₃) ⟶ e₃
  β-Arith : ∀ {⊕ : ArithmeticOp} {n₁ n₂}
            → (Value (n₁ N))
            → (Value (n₂ N))
            -----------------
            → ((n₁ N) ⟨ ⊕ ⟩ᵃ (n₂ N)) ⟶ ((⟦ ⊕ ⟧ᵃ n₁ n₂) N) -- Check if this makes sense
  ξ-Arith₁ : ∀ {⊕ : ArithmeticOp} {e₁'}
             → e₁ ⟶ e₁'
             -----------
             → (e₁ ⟨ ⊕ ⟩ᵃ e₂) ⟶ (e₁' ⟨ ⊕ ⟩ᵃ e₂)
  ξ-Arith₂ : ∀ {⊕ : ArithmeticOp} {e₂'} {v₁}
             → Value v₁
             → e₂ ⟶ e₂'
             -----------
             → (v₁ ⟨ ⊕ ⟩ᵃ e₂) ⟶ (v₁ ⟨ ⊕ ⟩ᵃ e₂')
  β-Let : ∀ x v₁ e₂
          → (let' x ≈ v₁ in' e₂) ⟶ {!!}
\end{code}

\begin{code}
infixl 19 _⦂_ -- TODO: is this correct?

data _⦂_ : Exp → Type → Set where
  -- Booleans
  T-False : false ⦂ Bool
  T-True  : true  ⦂ Bool
  T-If    : ∀ {t}
            → e₁ ⦂ Bool
            → e₂ ⦂ t
            → e₃ ⦂ t
            --------
            → if e₁ then e₂ else e₃ ⦂ t
  -- Naturals
  T-N : ∀ {n} → n N ⦂ Nat
  T-+ : ∀ {n₁ n₂} → n₁ ⟨ + ⟩ᵃ n₂ ⦂ Nat
\end{code}
