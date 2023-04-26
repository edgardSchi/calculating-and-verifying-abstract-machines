--------------------------------------------------------------------------------
-
- Properties of small-step evaluation rules
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Reduction.Properties where

open import AbstractMachines.Language.Types
open import AbstractMachines.Language.Reduction public

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)
\end{code}

\begin{code}
private variable
  Γ        : Context
  T        : Type
  t u u' v : Γ ⊢ T
\end{code}

--------------------------------------------------------------------------------

𝗡𝗼𝗿𝗺𝗮𝗹 𝗙𝗼𝗿𝗺
A term t is in normal form, if there does not exist a term t' such that t can
be reduced to t'
<Normal-Form>
\begin{code}
NF : (Γ ⊢ T) → Set
NF t = ∀ {t'} → ¬ (t ⟶ t')
\end{code}

Every value is in normal form
<Values-Dont-Reduce>
\begin{code}
Value→NF : Value t → NF t
Value→NF true   = λ ()
Value→NF false  = λ ()
Value→NF (_ N)  = λ ()
Value→NF (ƛⱽ _) = λ ()
\end{code}

--------------------------------------------------------------------------------
- Single Step Determinism
--------------------------------------------------------------------------------

𝗦𝗶𝗻𝗴𝗹𝗲 𝗦𝘁𝗲𝗽 𝗗𝗲𝘁𝗲𝗿𝗺𝗶𝗻𝗶𝘀𝗺
The single step reduction is deterministic, i.e. a term t can only be reduced to
one other term
<Single-Step-Determinism>
\begin{code}
⟶-det : t ⟶ u → t ⟶ u' → u ≡ u'
\end{code}
\begin{code}
⟶-det (ξ-·₁ {t₂ = t₂} t⟶u)            (ξ-·₁ t⟶u')           = cong (_· t₂) (⟶-det t⟶u t⟶u')
⟶-det (ξ-·₁ t⟶u)                      (ξ-·₂ t⇥ _)           = ⊥-elim (Value→NF t⇥ t⟶u)
⟶-det (ξ-·₂ t⇥ _)                     (ξ-·₁ t⟶u')           = ⊥-elim (Value→NF t⇥ t⟶u')
⟶-det (ξ-·₂ {v = v} _ t⟶u)            (ξ-·₂ _ t⟶u')         = cong (v ·_) (⟶-det t⟶u t⟶u')
⟶-det (ξ-·₂ _ t⟶u)                    (β-ƛ t⇥)              = ⊥-elim (Value→NF t⇥ t⟶u)
⟶-det (β-ƛ t⇥)                        (ξ-·₂ _ t⟶u)          = ⊥-elim (Value→NF t⇥ t⟶u)
⟶-det (β-ƛ x)                         (β-ƛ x₁)              = refl
⟶-det (ξ-If {t₂ = t₂} {t₃ = t₃} t⟶u)  (ξ-If t⟶u')           = cong (if_then t₂ else t₃) (⟶-det t⟶u t⟶u')
⟶-det β-If₁                           β-If₁                 = refl
⟶-det β-If₂                           β-If₂                 = refl
⟶-det (ξ-Arith₁ {t₂ = t₂} t⟶u)        (ξ-Arith₁ t⟶u')       = cong (_⟨ _ ⟩ᵃ t₂) (⟶-det t⟶u t⟶u')
⟶-det (ξ-Arith₁ t⟶u)                  (ξ-Arith₂ x t⟶u')     = ⊥-elim (Value→NF x t⟶u)
⟶-det (ξ-Arith₁ t⟶u)                  (β-Arith nv₁ nv₂)     = ⊥-elim (Value→NF nv₁ t⟶u)
⟶-det (ξ-Arith₂ v t⟶u)                (ξ-Arith₁ t⟶u')       = ⊥-elim (Value→NF v t⟶u')
⟶-det (ξ-Arith₂ (n N) t⟶u)            (ξ-Arith₂ V-N t⟶u')   = cong ((n N) ⟨ _ ⟩ᵃ_) ( ⟶-det t⟶u t⟶u')
⟶-det (ξ-Arith₂ x t⟶u)                (β-Arith nv₁ nv₂)     = ⊥-elim (Value→NF nv₂ t⟶u)
⟶-det (β-Arith nv₁ nv₂)               (ξ-Arith₁ t⟶u')       = ⊥-elim (Value→NF nv₁ t⟶u')
⟶-det (β-Arith _ nv₂)                 (ξ-Arith₂ _ t⟶u')     = ⊥-elim (Value→NF nv₂ t⟶u')
⟶-det (β-Arith (_ N) (_ N))           (β-Arith (_ N) (_ N)) = refl
⟶-det (ξ-Comp₁ {t₂ = t₂} t⟶u)         (ξ-Comp₁ t⟶u')        = cong (_⟨ _ ⟩ᶜ t₂) (⟶-det t⟶u t⟶u')
⟶-det (ξ-Comp₁ t⟶u)                   (ξ-Comp₂ t⇥ t⟶u')     = ⊥-elim (Value→NF t⇥ t⟶u)
⟶-det (ξ-Comp₁ t⟶u)                   (β-Comp nv₁ nv₂)      = ⊥-elim (Value→NF nv₁ t⟶u)
⟶-det (ξ-Comp₂ t⇥ t⟶u)                (ξ-Comp₁ t⟶u')        = ⊥-elim (Value→NF t⇥ t⟶u')
⟶-det (ξ-Comp₂ (n N) t⟶u)             (ξ-Comp₂ V-N t⟶u')    = cong ((n N) ⟨ _ ⟩ᶜ_) ( ⟶-det t⟶u t⟶u')
⟶-det (ξ-Comp₂ x t⟶u)                 (β-Comp nv₁ nv₂)      = ⊥-elim (Value→NF nv₂ t⟶u)
⟶-det (β-Comp nv₁ nv₂)                (ξ-Comp₁ t⟶u')        = ⊥-elim (Value→NF nv₁ t⟶u')
⟶-det (β-Comp nv₁ nv₂)                (ξ-Comp₂ x t⟶u')      = ⊥-elim (Value→NF nv₂ t⟶u')  
⟶-det (β-Comp (_ N) (_ N))            (β-Comp (_ N) (_ N))  = refl
⟶-det (ξ-Let {t₂ = t₂} t⟶u)           (ξ-Let t⟶u')          = cong (let'_in' t₂) (⟶-det t⟶u t⟶u')
⟶-det (ξ-Let t⟶u)                     (β-Let v)             = ⊥-elim (Value→NF v t⟶u)
⟶-det (β-Let v)                       (ξ-Let t⟶u')          = ⊥-elim (Value→NF v t⟶u')
⟶-det (β-Let v₁)                      (β-Let v₂)            = refl
\end{code}

----------------------------------------------------------- ---------------------
- Multi Step Properties
--------------------------------------------------------------------------------

Concatination of multi and single step produces a new multi step reduction
\begin{code}
_↠+⟶_ : t ↠ u → u ⟶ v → t ↠ v
↠-step t⟶u    ↠+⟶ u⟶v  = ↠-step t⟶u ↠↠ ↠-step u⟶v
↠-refl        ↠+⟶ u⟶v  = ↠-step u⟶v
(t↠u ↠↠ t↠u') ↠+⟶ u⟶v  = t↠u ↠↠ (t↠u' ↠+⟶ u⟶v)
\end{code}

If we have a term t in normal form and a reduction from t to u, then t
and u must be the same term
\begin{code}
NF-refl : NF t → t ↠ u → t ≡ u
NF-refl nf-t (↠-step s)     = ⊥-elim (nf-t s)
NF-refl nf-t ↠-refl         = refl
NF-refl nf-t (t↠u ↠↠ t↠u') with NF-refl nf-t t↠u
... | refl = NF-refl nf-t t↠u'
\end{code}

--------------------------------------------------------------------------------
- Properties requiring the single step reduction to be deterministic
--------------------------------------------------------------------------------

Originally these properties where a in parameterized module requiring a function
for determinism of the single step relation, since the proofs do not need to know
how the reductions rules work
\begin{code}
--private module Unique (⟶-det : ∀ {t t' t'' : Γ ⊢ T} → t ⟶ t' → t ⟶ t'' → t' ≡ t'') where
\end{code}

If a term u is in normal form and there is a term t that can be reduced to u
in a single step and to some term u' in multiple steps, then either u ≡ u'
or u' ≡ t
\begin{code}
⟶↠-unique : NF u → t ⟶ u → t ↠ u' → u ≡ u' ⊎ u' ≡ t
⟶↠-unique nf-u t⟶u (↠-step s)  = inj₁ (⟶-det t⟶u s)
⟶↠-unique nf-u t⟶u ↠-refl      = inj₂ refl
⟶↠-unique nf-u t⟶u (t↠u' ↠↠ t↠u'') with ⟶↠-unique nf-u t⟶u t↠u'
... | inj₁ refl rewrite NF-refl nf-u t↠u'' = inj₁ refl
... | inj₂ refl = ⟶↠-unique nf-u t⟶u t↠u''
\end{code}

If a term t reduces to a term u in a single step and also reduces
to a term v in multiple steps, then either u can be reduced to v
or v ≡ t
\begin{code}
⟶↠-diff : t ⟶ u → t ↠ v → u ↠ v ⊎ v ≡ t
⟶↠-diff t⟶u (↠-step s) rewrite ⟶-det t⟶u s  = inj₁ ↠-refl
⟶↠-diff t⟶u ↠-refl                          = inj₂ refl
⟶↠-diff t⟶u (t↠v ↠↠ t↠v') with ⟶↠-diff t⟶u t↠v
... | inj₁ u↠v   = inj₁ (u↠v ↠↠ t↠v')
... | inj₂ refl  = ⟶↠-diff t⟶u t↠v'
\end{code}

If a term t can be reduced to a term u and a term v in multiple
steps, then either u reduces to v or v reduces to u
\begin{code}
↠-conn : t ↠ u → t ↠ v → u ↠ v ⊎ v ↠ u
↠-conn t↠u ↠-refl = inj₂ t↠u
↠-conn t↠u (↠-step s) with ⟶↠-diff s t↠u
... | inj₁ v↠u   = inj₂ v↠u
... | inj₂ refl  = inj₁ (↠-step s)
↠-conn t↠u (t↠v ↠↠ t↠v') with ↠-conn t↠u t↠v
... | inj₁ u↠t'  = inj₁ (u↠t' ↠↠ t↠v')
... | inj₂ t'↠u  = ↠-conn t'↠u t↠v'
\end{code}

𝗨𝗻𝗶𝗾𝘂𝗲𝗻𝗲𝘀𝘀 𝗼𝗳 𝗡𝗼𝗿𝗺𝗮𝗹 𝗙𝗼𝗿𝗺𝘀
If some term t reduces to two normal forms u and v, then both
must be the same term
<NF-Unique>
\begin{code}
NF-unique : NF u → NF v → t ↠ u → t ↠ v → u ≡ v
\end{code}
\begin{code}
NF-unique nf-u nf-v ↠-refl ↠-refl             = refl
NF-unique nf-u nf-v (↠-step t⟶u) (↠-step t⟶v) = ⟶-det t⟶u t⟶v
NF-unique nf-u nf-v (↠-step t⟶u) ↠-refl       = ⊥-elim (nf-v t⟶u)
NF-unique nf-u nf-v ↠-refl       (↠-step t⟶v) = ⊥-elim (nf-u t⟶v)
NF-unique nf-u nf-v (↠-step t⟶u) (t↠e ↠↠ e↠v) with ⟶↠-unique nf-u t⟶u (t↠e ↠↠ e↠v)
... | inj₁ refl = refl
... | inj₂ refl = ⊥-elim (nf-v t⟶u)
NF-unique nf-u nf-v (t↠e ↠↠ e↠u) (↠-step t⟶v) with ⟶↠-unique nf-v t⟶v (t↠e ↠↠ e↠u)
... | inj₁ refl = refl
... | inj₂ refl = ⊥-elim (nf-u t⟶v)
NF-unique nf-u nf-v ↠-refl (u↠e ↠↠ e↠v) with NF-refl nf-u u↠e
... | refl = NF-refl nf-u e↠v
NF-unique nf-u nf-v (v↠e ↠↠ e↠u) ↠-refl with NF-refl nf-v v↠e
... | refl = sym (NF-refl nf-v e↠u)
NF-unique nf-u nf-v (t↠e ↠↠ e↠u) (t↠e' ↠↠ e'↠v) with ↠-conn t↠e t↠e'
... | inj₁ e↠e' = NF-unique nf-u nf-v e↠u (e↠e' ↠↠ e'↠v)
... | inj₂ e'↠e with ↠-conn e'↠e e'↠v
... | inj₁ e↠v = NF-unique nf-u nf-v e↠u e↠v
... | inj₂ v↠e with NF-refl nf-v v↠e
... | refl rewrite NF-refl nf-v e↠u = refl
\end{code}

--------------------------------------------------------------------------------
- Progress
--------------------------------------------------------------------------------

𝗣𝗿𝗼𝗴𝗿𝗲𝘀𝘀
Defining the progress property, where a term t has either a reduction or
is a value
<Progress-Definition>
\begin{code}
data Progress (t : ∅ ⊢ T) : Set where
  step : ∀ {t' : ∅ ⊢ T} → t ⟶ t' → Progress t
  done : Value t → Progress t
\end{code}

<Progress-Proof>
\begin{code}
progress : ∀ (t : ∅ ⊢ T) → Progress t
\end{code}
\begin{code}
progress true = done true
progress false = done false
progress (if t₁ then t₂ else t₃) with progress t₁
... | step t₁⟶t₁' = step (ξ-If t₁⟶t₁')
... | done true = step β-If₁
... | done false = step β-If₂
progress (n N) = done (n N)
progress (t₁ ⟨ ⊕ ⟩ᵃ t₂) with progress t₁
... | step t₁⟶t₁' = step (ξ-Arith₁ t₁⟶t₁')
... | done (n₁ N) with progress t₂
...   | step t₂⟶t₂' = step (ξ-Arith₂ (n₁ N) t₂⟶t₂')
...   | done (n₂ N) = step (β-Arith (n₁ N) (n₂ N))
progress (t₁ ⟨ ⊙ ⟩ᶜ t₂) with progress t₁
... | step t₁⟶t₁' = step (ξ-Comp₁ t₁⟶t₁')
... | done (n₁ N) with progress t₂
...   | step t₂⟶t₂' = step (ξ-Comp₂ (n₁ N) t₂⟶t₂')
...   | done (n₂ N) = step (β-Comp (n₁ N) (n₂ N))
progress (let' t₁ in' t₂) with progress t₁
... | step t₁⟶t₁' = step (ξ-Let t₁⟶t₁')
... | done (ƛⱽ t) = step (β-Let (ƛⱽ t))
... | done true = step (β-Let true)
... | done false = step (β-Let false)
... | done (n N) = step (β-Let (n N))
progress (ƛ t) = done (ƛⱽ t)
progress (t₁ · t₂) with progress t₁
... | step t₁⟶t₁' = step (ξ-·₁ t₁⟶t₁')
... | done (ƛⱽ t₁') with progress t₂
... | step t₂⟶t₂' = step (ξ-·₂ (ƛⱽ t₁') t₂⟶t₂')
...   | done (ƛⱽ t) = step (β-ƛ (ƛⱽ t))
...   | done true = step (β-ƛ true)
...   | done false = step (β-ƛ false)
...   | done (n N) = step (β-ƛ (n N))
\end{code}
