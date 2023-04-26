------------------------------------------------------------------------
--
-- Module showing well-scoped DeBruijn terms (Not used in the thesis)
--
------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Well-Scoped where

open import Data.Nat using (ℕ; suc; zero; _+_; _<_; _<?_; _≟_)
open import Data.Fin using (Fin; toℕ; fromℕ) renaming (zero to fzero; suc to fsuc; _+_ to _f+_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; _≢_; cong)
\end{code}

<Term-Definition>
\begin{code}
data Term (n : ℕ) : Set where
  Var  : Fin n → Term n
  Lam  : Term (1 + n) → Term n
  App  : Term n → Term n → Term n
\end{code}

\begin{code}
_ : ∀ {n} → Term n
_ = Lam (App (Var fzero) (Var fzero))

test : Term 2
test = (Lam (App (Var (fzero)) (Var (fsuc fzero))))

ClosedTerm : Set
ClosedTerm = Term 0

close : ∀ {n} → Term n → ClosedTerm
close {zero} term = term
close {suc n} term = close (Lam term)

isClosed : ∀ {n} → Term n → Dec ClosedTerm
isClosed {zero} term = yes term
isClosed {suc n} term = isClosed (Lam term)

infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m + n)
fzero    ↑ˡ n = fzero
(fsuc i) ↑ˡ n = fsuc (i ↑ˡ n)

infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n + m)
zero    ↑ʳ i = i
(suc n) ↑ʳ i = fsuc (n ↑ʳ i)

f : ∀ {n} → Fin n → (d : ℕ) → Fin (d + n)
f fzero zero = fzero
f fzero (suc d) = fzero
f (fsuc fin) zero = fzero
f (fsuc fin) (suc d) = fzero

+-suc : ∀ {m n} → m + suc n ≡ suc (m + n)
+-suc {zero} {n} = refl
+-suc {suc m} {n} = cong suc +-suc

g : ∀ {d n} → Term (d + suc n) ≡ Term (1 + (d + n))
g {zero} {n} = refl
g {suc d} {n} = cong Term (cong suc +-suc)

{-↑ : ∀ n → (d : ℕ) → ℕ → Term n → Term (suc (d + n))
↑ n d c (Var x) with n <? c
... | yes p = Var {!!} --(f x d)
... | no  p = Var {!!} --(d ↑ʳ x)
↑ n d c (Lam term) = Lam ( (↑ (suc n) {!!} (c + 1) term))
↑ n d c (App term₁ term₂) =  App (↑ n d c term₁) (↑ n d c term₂)-}
\end{code}

\begin{code}
data T : Set where
  Var : ℕ → T
  App : T → T → T
  Lam : T → T


shift : ℕ → T → T
shift d term = shift' d 0 term where
  shift' : ℕ → ℕ → T → T
  shift' d c (Var n) with n <? c
  ... | yes p = Var n
  ... | no  p = Var (d + n)
  shift' d c (Lam term) = Lam ( (shift' d (c + 1) term))
  shift' d c (App term₁ term₂) =  App (shift' d c term₁) (shift' d c term₂)

ex : T
ex = Lam (Lam (App (Var 1) (App (Var 0) (Var 2))))

ex2 : T
ex2 = Lam (App (Var 0) (Lam (App (Var 0) (App (Var 1) (Var 2)))))

[_↦_]_ : ℕ → T → T → T
[ j ↦ s ] Var k with j ≟ k
... | yes p = s
... | no  p = Var k
[ j ↦ s ] App t₁ t₂ = App ([ j ↦ s ] t₁) ( [ j ↦ s ] t₂)
[ j ↦ s ] Lam t = Lam ([ (j + 1) ↦ (shift 1 s) ] t)
\end{code}

