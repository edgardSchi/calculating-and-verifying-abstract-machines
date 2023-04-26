--------------------------------------------------------------------------------
-
- Proving normalization of the language
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Normalization where

open import AbstractMachines.Language.Types hiding (_∘_)
open import AbstractMachines.Language.Substitution
open import AbstractMachines.Language.Substitution.Properties
open import AbstractMachines.Language.Reduction.Properties

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Product using (∃; ∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to _⸴_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Equivalence using (equivalence; _⇔_; Equivalence; id; _∘_)
open import Function.Equality using (_⟨$⟩_)
\end{code}

\begin{code}
private variable
  Γ Δ   : Context
  T A B : Type
  t t'  : Γ ⊢ T
  σ     : Γ ↷ Δ
\end{code}

TODO: Find a good way of abbreviating Equivalence.(to/from) _ ⟨$⟩ _
TODO: Move the *-rules to a different file

--------------------------------------------------------------------------------

\begin{code}
ξ-·₁* : ∀ {T₁ T₂ Γ} {t t' : Γ ⊢ T₁ ⇒ T₂} {t₂ : Γ ⊢ T₁} → t ↠ t' → (t · t₂) ↠ (t' · t₂)
ξ-·₁* (↠-step x) = ↠-step (ξ-·₁ x)
ξ-·₁* ↠-refl = ↠-refl
ξ-·₁* (↠-trans t t₁) = ↠-trans (ξ-·₁* t) (ξ-·₁* t₁)
\end{code}

\begin{code}
ξ-·₂* : ∀ {Γ T₁ T₂} {v : Γ ⊢ T₁ ⇒ T₂} {t t' : Γ ⊢ T₁} → Value v → t ↠ t' → (v · t) ↠ (v · t')
ξ-·₂* v (↠-step x) = ↠-step (ξ-·₂ v x)
ξ-·₂* v ↠-refl = ↠-refl
ξ-·₂* v (↠-trans x x₁) = ↠-trans (ξ-·₂* v x) (ξ-·₂* v x₁)
\end{code}

\begin{code}
ξ-If* : ∀ {Γ T} {t₁ t₁' : Γ ⊢ Bool}
        → {t₂ t₃ : Γ ⊢ T}
        → t₁ ↠ t₁'
        → (if t₁ then t₂ else t₃) ↠ (if t₁' then t₂ else t₃)
ξ-If* (↠-step s) = ↠-step (ξ-If s)
ξ-If* ↠-refl = ↠-refl
ξ-If* (↠-trans a b) = ↠-trans (ξ-If* a) (ξ-If* b)
\end{code}

\begin{code}
ξ-Arith₁* : ∀ {Γ ⊕} {t₁ t₁' t₂ : Γ ⊢ Nat} → t₁ ↠ t₁' → (t₁ ⟨ ⊕ ⟩ᵃ t₂) ↠ (t₁' ⟨ ⊕ ⟩ᵃ t₂)
ξ-Arith₁* (↠-step s) = ↠-step (ξ-Arith₁ s)
ξ-Arith₁* ↠-refl = ↠-refl
ξ-Arith₁* (↠-trans a b) = ↠-trans (ξ-Arith₁* a) (ξ-Arith₁* b)
\end{code}

\begin{code}
ξ-Arith₂* : ∀ {Γ ⊕} {v₁ : Γ ⊢ Nat} {t₂ t₂' : Γ ⊢ Nat} → Value v₁ → t₂ ↠ t₂' → (v₁ ⟨ ⊕ ⟩ᵃ t₂) ↠ (v₁ ⟨ ⊕ ⟩ᵃ t₂')
ξ-Arith₂* v (↠-step s) = ↠-step (ξ-Arith₂ v s)
ξ-Arith₂* v ↠-refl = ↠-refl
ξ-Arith₂* v (↠-trans a b) = ↠-trans (ξ-Arith₂* v a) (ξ-Arith₂* v b)
\end{code}

\begin{code}
ξ-Comp₁* : ∀ {Γ ⊕} {t₁ t₁' t₂ : Γ ⊢ Nat} → t₁ ↠ t₁' → (t₁ ⟨ ⊕ ⟩ᶜ t₂) ↠ (t₁' ⟨ ⊕ ⟩ᶜ t₂)
ξ-Comp₁* (↠-step s) = ↠-step (ξ-Comp₁ s)
ξ-Comp₁* ↠-refl = ↠-refl
ξ-Comp₁* (↠-trans a b) = ↠-trans (ξ-Comp₁* a) (ξ-Comp₁* b)
\end{code}

\begin{code}
ξ-Comp₂* : ∀ {Γ ⊕} {v₁ : Γ ⊢ Nat} {t₂ t₂' : Γ ⊢ Nat} → Value v₁ → t₂ ↠ t₂' → (v₁ ⟨ ⊕ ⟩ᶜ t₂) ↠ (v₁ ⟨ ⊕ ⟩ᶜ t₂')
ξ-Comp₂* v (↠-step s) = ↠-step (ξ-Comp₂ v s)
ξ-Comp₂* v ↠-refl = ↠-refl
ξ-Comp₂* v (↠-trans a b) = ↠-trans (ξ-Comp₂* v a) (ξ-Comp₂* v b)
\end{code}

\begin{code}
ξ-Let* : ∀ {Γ T₁ T₂} {t₁ t₁' : Γ ⊢ T₁} {t₂ : Γ , T₁ ⊢ T₂} → t₁ ↠ t₁' → (let' t₁ in' t₂) ↠ (let' t₁' in' t₂)
ξ-Let* (↠-step s) = ↠-step (ξ-Let s)
ξ-Let* ↠-refl = ↠-refl
ξ-Let* (↠-trans a b) = ↠-trans (ξ-Let* a) (ξ-Let* b)
\end{code}

--------------------------------------------------------------------------------

𝗛𝗮𝗹𝘁
Defining the meaning of a term halting
A term halts if it reduces to a value
<Halt-Definition>
\begin{code}
Halts : Γ ⊢ T → Set
Halts = λ t → ∃[ t' ] Value t' × t ↠ t'
\end{code}

Values trivially always halt
\begin{code}
values-halt : ∀ {t : Γ ⊢ T} → Value t → Halts t
values-halt {t = t} val-t = t ⸴ val-t ⸴ ↠-refl
\end{code}

𝗦𝗮𝘁𝘂𝗿𝗮𝘁𝗲𝗱 𝗦𝗲𝘁𝘀
We define saturated sets as sets where closed terms of the base types halt, terms of
type T₁ ⇒ T₂ halt and all terms t' that are also in the saturated set are again
in the saturated set when using function application t · t'
<Saturated-Definition>
\begin{code}
Saturated : ∅ ⊢ T → Set
Saturated {T₁ ⇒ T₂} t  = Halts t × (∀ t' → Saturated t' → Saturated (t · t'))
Saturated {Nat}     t  = Halts t
Saturated {Bool}    t  = Halts t
\end{code}

If a closed term is saturated, then it also halts
\begin{code}
sat-halts : ∀ {t : ∅ ⊢ T} → Saturated t → Halts t
sat-halts {T ⇒ T₁} (t-halts ⸴ _)  = t-halts
sat-halts {Nat}    t-halts       = t-halts
sat-halts {Bool}   t-halts       = t-halts
\end{code}

𝗜𝗻𝘀𝘁𝗮𝗻𝘁𝗶𝗮𝘁𝗶𝗼𝗻
Instantiation of a substitution from a context Γ to an empty set is given by
either the empty substitution or given an instantiation with some kind of
substitution σ and a value that is also saturated, we extend σ by t 
<Instantiation-Definition>
\begin{code}
data Instantiation : ∅ ↷ Γ → Set where
  ∅    : Instantiation ∅
  _,_  : Instantiation σ → ∀ {t : ∅ ⊢ T} → Value t → Saturated t
       ----------------------
       → Instantiation (σ , t)
\end{code}

--------------------------------------------------------------------------------
- Properties of Halt and Saturated
--------------------------------------------------------------------------------

The single step reduction preserves the halt property
<Single-Step-Preserves-Halt>
\begin{code}
⟶-preserves-halt : t ⟶ t' → Halts t ⇔ Halts t'
\end{code}
\begin{code}
⟶-preserves-halt {t = t} {t' = t'} t⟶t' = equivalence => <=
  where
    => : Halts t → Halts t'
    => (u ⸴ val-u ⸴ ↠-step s) rewrite sym (⟶-det s t⟶t') = u ⸴ val-u ⸴ ↠-refl
    => (u ⸴ val-u ⸴ ↠-refl) = ⊥-elim (Value→NF val-u t⟶t')
    => (u ⸴ val-u ⸴ t↠v ↠↠ v↠u) with ⟶↠-diff t⟶t' t↠v
    ... | inj₁ t'↠v = u ⸴ val-u ⸴ (t'↠v ↠↠ v↠u)
    ... | inj₂ refl with ⟶↠-diff t⟶t' v↠u
    ... | inj₁ t'↠v = u ⸴ val-u ⸴ t'↠v
    ... | inj₂ refl = ⊥-elim (Value→NF val-u t⟶t')

    <= : Halts t' → Halts t
    <= (u ⸴ val-u  ⸴ t'↠u) = u ⸴ val-u ⸴ (↠-step t⟶t' ↠↠ t'↠u)
\end{code}

The single step reduction preserves the saturated property
<Single-Step-Preserves-Sat>
\begin{code}
⟶-preserves-sat : t ⟶ t' → Saturated t ⇔ Saturated t'
\end{code}
\begin{code}
⟶-preserves-sat t⟶t' = equivalence (=> t⟶t') (<= t⟶t')
  where
    => : ∀ {T t'} → {t : _ ⊢ T} → t ⟶ t' → Saturated t → Saturated t'
    => {T ⇒ T₁} t⟶t' (halts-t ⸴ f)
      = Equivalence.to (⟶-preserves-halt t⟶t') ⟨$⟩ halts-t ⸴ λ s sat-s → => (ξ-·₁ t⟶t') (f s sat-s)
    => {Nat} t⟶t'  halts-t  = Equivalence.to (⟶-preserves-halt t⟶t') ⟨$⟩ halts-t
    => {Bool} t⟶t' halts-t  = Equivalence.to (⟶-preserves-halt t⟶t') ⟨$⟩ halts-t

    <= : ∀ {T} {t'} → {t : _ ⊢ T} → t ⟶ t' → Saturated t' → Saturated t
    <= {T₁ ⇒ T₂} t⟶t' (halts-t' ⸴ f) =
      Equivalence.from (⟶-preserves-halt t⟶t') ⟨$⟩ halts-t' ⸴ λ s sat-s → <= (ξ-·₁ t⟶t') (f s sat-s)
    <= {Nat} t⟶t' halts-t' = Equivalence.from (⟶-preserves-halt t⟶t') ⟨$⟩ halts-t'
    <= {Bool} t⟶t' halts-t' = Equivalence.from (⟶-preserves-halt t⟶t') ⟨$⟩ halts-t'
\end{code}

The multi step reduction preserves the saturated property
<Multi-Step-Preserves-Sat>
\begin{code}
↠-preserves-sat : t ↠ t' → Saturated t ⇔ Saturated t'
\end{code}
\begin{code}
↠-preserves-sat (↠-step s)     = ⟶-preserves-sat s
↠-preserves-sat ↠-refl         = id
↠-preserves-sat (t↠u ↠↠ u↠t')  = ↠-preserves-sat u↠t' ∘ ↠-preserves-sat t↠u
\end{code}

--------------------------------------------------------------------------------
- Proving the saturate lemma
--------------------------------------------------------------------------------

\begin{code}
sub-sub↠sub : ∀ (σ : ∅ ↷ Γ) → (u : ∅ ⊢ A) → (t : Γ , A ⊢ B)
            → substitute (∅ , u) (substitute (extend σ) t) ↠ substitute (σ , u) t
sub-sub↠sub σ u t rewrite sym (sub↷↷≡sub-sub (∅ , u) (extend σ) t) | ∅↷↷drop σ u = ↠-refl
\end{code}

The saturate lemma for variables
\begin{code}
saturateⱽ : ∀ (σ : ∅ ↷ Γ)
            → Instantiation σ
            → (x : T ∈ Γ)
            → Saturated (substituteⱽ σ x)
saturateⱽ .(_ , _) ((_ , _) y)   Z      = y
saturateⱽ (σ , t)  ((ins , _) _) (S x)  = saturateⱽ σ ins x
\end{code}

𝗦𝗮𝘁𝘂𝗿𝗮𝘁𝗲 𝗟𝗲𝗺𝗺𝗮
The saturate lemma says that for every instantiation σ and term t the substitution
of σ and t is saturated
<Saturate-Lemma>
\begin{code}
saturate : Instantiation σ → (t : Γ ⊢ T)
         ------------------------
         → Saturated (substitute σ t)
\end{code}
\begin{code}
saturate ins true = true ⸴ true ⸴ ↠-refl
saturate ins false = false ⸴ false ⸴ ↠-refl
saturate ins (if t₁ then t₂ else t₃) with saturate ins t₁
... | true  ⸴ true  ⸴ steps =
  Equivalence.from (↠-preserves-sat (ξ-If* steps ↠↠ ↠-step β-If₁)) ⟨$⟩ saturate ins t₂
... | false ⸴ false ⸴ steps =
  Equivalence.from (↠-preserves-sat (ξ-If* steps ↠↠ ↠-step β-If₂)) ⟨$⟩ saturate ins t₃
saturate ins (n N) = n N ⸴ (n N) ⸴ ↠-refl
saturate ins (l ⟨ ⊕ ⟩ᵃ r) with saturate ins l | saturate ins r
... | n-l N ⸴ (_ N) ⸴ steps-l | n-r N ⸴ (n-r N) ⸴ steps-r =
  Equivalence.from
    (↠-preserves-sat (ξ-Arith₁* steps-l ↠↠ (ξ-Arith₂* (_ N) steps-r ↠↠ ↠-step (β-Arith (n-l N) (n-r N)))))
  ⟨$⟩ (⟦ ⊕ ⟧ᵃ n-l n-r N ⸴ (_ N) ⸴ ↠-refl)
saturate {Γ} ins (l ⟨ ⊕ ⟩ᶜ r) with saturate ins l | saturate ins r
... | n-l N ⸴ (_ N) ⸴ steps-l | n-r N ⸴ (_ N) ⸴ steps-r =
  Equivalence.from
    (↠-preserves-sat (ξ-Comp₁* {⊕ = ⊕} steps-l ↠↠ (ξ-Comp₂* (_ N) steps-r ↠↠ ↠-step (β-Comp (n-l N) (n-r N)))))
  ⟨$⟩ (𝔹↓ (⟦ ⊕ ⟧ᶜ n-l n-r) ⸴ ⟦⟧ᶜ-val {∅} {⊕} n-l n-r ⸴ ↠-refl)
saturate {σ = σ} ins (′ x) = saturateⱽ σ ins x
saturate {_} {σ} ins (t₁ · t₂) with saturate ins t₁ | saturate ins t₂
... | (t' ⸴ val-t' ⸴ t₁↠t') ⸴ snd | sat-t₂ = snd (substitute σ t₂) sat-t₂
saturate {Γ} {σ = σ} {T = T} ins (let'_in'_ {T₁ = T₁} t₁ t₂) with saturate ins t₁
... | sat-t₁ = t-sat sat-t₁
  where
\end{code}
<Saturate-Lemma-Let-Aux-Defs>
\begin{code}
    σ' : (∅ , T₁) ↷ (Γ , T₁)
    t₁' = substitute σ t₁
    t₂' = substitute σ' t₂
\end{code}
\begin{code}

    σ' =  drop ∅ ⊆-↷ σ , (′ Z)

    t-sat : ∀ {u} → Saturated u → Saturated (let' u in' t₂')
    t-sat {u} sat-u with sat-halts sat-u
    ... | v ⸴ val-v ⸴ u↠v = Equivalence.from (↠-preserves-sat let↠sub) ⟨$⟩ sat
      where
        sat-v : Saturated v
        sat-v = Equivalence.to (↠-preserves-sat u↠v) ⟨$⟩ sat-u

        sat : Saturated (substitute (σ , v) t₂)
        sat = saturate ((ins , val-v) sat-v) t₂

        let↠sub : (let' u in' t₂') ↠ (substitute (σ , v) t₂)
        let↠sub =
\end{code}
<Saturate-Lemma-Let-Evaluation>
\begin{code}
          ↠begin
            let' u in' t₂'
          ↠⟨ ξ-Let* u↠v ⟩
            let' v in' t₂'
          ⟶⟨ β-Let val-v ⟩
            substitute (∅ , v) t₂'
          ↠⟨ by-definition ⟩
            substitute (∅ , v) (substitute σ' t₂)
          ↠⟨ sub-sub↠sub σ v t₂ ⟩
            substitute (σ , v) t₂
          ↠∎
\end{code}
\begin{code}
saturate {Γ} {σ} {T = A ⇒ B} ins (ƛ t') = (values-halt (ƛⱽ _)) ⸴ t-sat
  where
    t'ˢ = substitute (extend σ) t'

    t-sat : (u : _ ⊢ A) → Saturated u → Saturated ((ƛ t'ˢ) · u)
    t-sat u sat-u with sat-halts sat-u
    ... | v ⸴ val-v ⸴ u↠v = (Equivalence.from (↠-preserves-sat ƛ↠sub)) ⟨$⟩ sat
      where
        sat-v : Saturated v
        sat-v = Equivalence.to (↠-preserves-sat u↠v) ⟨$⟩ sat-u

        sat : Saturated (substitute (σ , v) t') 
        sat = saturate ((ins , val-v) sat-v) t'

        ƛ↠sub : ((ƛ t'ˢ) · u) ↠ (substitute (σ , v) t')
        ƛ↠sub =
\end{code}
<Saturate-Lemma-Lambda-Evaluation>
\begin{code}
          ↠begin
            (ƛ substitute (extend σ) t') · u
          ↠⟨ ξ-·₂* (ƛⱽ _) u↠v ⟩
            (ƛ substitute (extend σ) t') · v
          ⟶⟨ β-ƛ val-v ⟩
            [ v ] substitute (extend σ) t'
          ↠⟨ by-definition ⟩
            substitute (∅ , v) (substitute (extend σ) t')
          ↠⟨ sub-sub↠sub σ v t' ⟩
            substitute (σ , v) t'
          ↠∎
\end{code}

--------------------------------------------------------------------------------
- Normalization
--------------------------------------------------------------------------------

𝗡𝗼𝗿𝗺𝗮𝗹𝗶𝘇𝗮𝘁𝗶𝗼𝗻
Every closed term halts, i.e. reduces to a value
<Normalization>
\begin{code}
normalization : ∀ (t : ∅ ⊢ T) → Halts t
\end{code}
\begin{code}
normalization t rewrite sym (sub-refl t) = sat-halts (saturate ∅ t)
\end{code}
