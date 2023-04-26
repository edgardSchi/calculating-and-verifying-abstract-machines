--------------------------------------------------------------------------------
-
- Properties of substitution
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Substitution.Properties where

open import AbstractMachines.Language.Types
open import AbstractMachines.Language.Weakening
open import AbstractMachines.Language.Substitution

open import Relation.Binary.PropositionalEquality as EQ
open EQ using (_≡_; refl; sym; _≢_; cong)
open EQ.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
\end{code}

\begin{code}
private variable
  Γ Δ Ε Ζ : Context
  T       : Type
\end{code}

--------------------------------------------------------------------------------

\begin{code}
assoc-rsr : (Γ⊆Δ : Γ ⊆ Δ) → (σ : Γ ↷ Ζ) → (Ε⊆Ζ : Ε ⊆ Ζ)
          → Γ⊆Δ ⊆-↷ (σ ↷-⊆ Ε⊆Ζ) ≡ (Γ⊆Δ ⊆-↷ σ) ↷-⊆ Ε⊆Ζ
assoc-rsr Γ⊆Δ σ ∅               = refl
assoc-rsr Γ⊆Δ (σ , _) (drop Ε⊆Ζ)
  rewrite assoc-rsr Γ⊆Δ σ Ε⊆Ζ   = refl
assoc-rsr Γ⊆Δ (σ , _) (copy Ε⊆Ζ)
  rewrite assoc-rsr Γ⊆Δ σ Ε⊆Ζ   = refl
\end{code}

\begin{code}
assoc-rrs : ∀ {Γ Δ Ε Ζ} → (Δ⊆Γ : Δ ⊆ Γ) → (Ε⊆Δ : Ε ⊆ Δ) → (σ : Ε ↷ Ζ)
            → Δ⊆Γ ⊆-↷ (Ε⊆Δ ⊆-↷ σ) ≡ (⊆-refl Ε⊆Δ Δ⊆Γ) ⊆-↷ σ
assoc-rrs Δ⊆Γ Ε⊆Δ ∅                                   = refl
assoc-rrs Δ⊆Γ Ε⊆Δ (σ , x)
  rewrite assoc-rrs Δ⊆Γ Ε⊆Δ σ | wk-wk≡refl Δ⊆Γ Ε⊆Δ x  = refl
\end{code}

\begin{code}
copy-drop≡drop : (Γ⊆Δ : Γ ⊆ Δ) → (σ : Γ ↷ Ε)
               → copy Γ⊆Δ ⊆-↷ (drop ⊆-id ⊆-↷ σ)
                 ≡
                 (drop {T = T} ⊆-id) ⊆-↷ (Γ⊆Δ ⊆-↷ σ)
copy-drop≡drop {T = T} Γ⊆Δ σ
  rewrite assoc-rrs (⊆-wk {T = T}) Γ⊆Δ σ |
          ⊆-refl-idₗ Γ⊆Δ |
          assoc-rrs (copy {T = T} Γ⊆Δ) (⊆-wk {T = T}) σ |
          ⊆-refl-idᵣ Γ⊆Δ
  = refl
\end{code}

\begin{code}
wk-sub≡subⱽ : (Γ⊆Δ : Γ ⊆ Δ) → (σ : Γ ↷ Ε) → (x : T ∈ Ε)
            → weaken Γ⊆Δ (substituteⱽ σ x) ≡ substituteⱽ (Γ⊆Δ ⊆-↷ σ) x
wk-sub≡subⱽ Γ⊆Δ (σ , _) Z                                  = refl
wk-sub≡subⱽ Γ⊆Δ (σ , _) (S y) rewrite wk-sub≡subⱽ Γ⊆Δ σ y  = refl
\end{code}

\begin{code}
wk-sub≡sub : (Γ⊆Δ : Γ ⊆ Δ) → (σ : Γ ↷ Ε) → (t : Ε ⊢ T)
           → weaken Γ⊆Δ (substitute σ t) ≡ substitute (Γ⊆Δ ⊆-↷ σ) t
wk-sub≡sub Γ⊆Δ σ true
  = refl
wk-sub≡sub Γ⊆Δ σ false
  = refl
wk-sub≡sub Γ⊆Δ σ (if t₁ then t₂ else t₃)
  rewrite wk-sub≡sub Γ⊆Δ σ t₁ | wk-sub≡sub Γ⊆Δ σ t₂ | wk-sub≡sub Γ⊆Δ σ t₃
  = refl
wk-sub≡sub Γ⊆Δ σ (x N)
  = refl
wk-sub≡sub Γ⊆Δ σ (l ⟨ ⊕ ⟩ᵃ r)
  rewrite wk-sub≡sub Γ⊆Δ σ l | wk-sub≡sub Γ⊆Δ σ r
  = refl
wk-sub≡sub Γ⊆Δ σ (l ⟨ ⊗ ⟩ᶜ r) 
  rewrite wk-sub≡sub Γ⊆Δ σ l | wk-sub≡sub Γ⊆Δ σ r = refl
wk-sub≡sub Γ⊆Δ σ (t₁ · t₂)
  rewrite wk-sub≡sub Γ⊆Δ σ t₁ | wk-sub≡sub Γ⊆Δ σ t₂
  = refl
wk-sub≡sub Γ⊆Δ σ (′ x) = wk-sub≡subⱽ Γ⊆Δ σ x
wk-sub≡sub Γ⊆Δ σ (let'_in'_ {T₁ = T} t₁ t₂)
  rewrite wk-sub≡sub Γ⊆Δ σ t₁ | wk-sub≡sub (copy Γ⊆Δ) (extend σ) t₂
  = cong (λ x → let' substitute (Γ⊆Δ ⊆-↷ σ) t₁
    in' substitute (x , (′ Z)) t₂) (copy-drop≡drop Γ⊆Δ σ)
wk-sub≡sub {T = T} Γ⊆Δ σ (ƛ t)
  rewrite wk-sub≡sub (copy Γ⊆Δ) (extend σ) t
  = cong (λ x → ƛ substitute (x , (′ Z)) t) (copy-drop≡drop Γ⊆Δ σ)
\end{code}

\begin{code}
assoc-rss : (Γ⊆Δ : Γ ⊆ Δ) → (σ : Γ ↷ Ε) → (ρ : Ε ↷ Ζ)
          → Γ⊆Δ ⊆-↷ (σ ↷↷ ρ) ≡ (Γ⊆Δ ⊆-↷ σ) ↷↷ ρ
assoc-rss Γ⊆Δ σ ∅
  = refl
assoc-rss Γ⊆Δ σ (ρ , t) rewrite assoc-rss Γ⊆Δ σ ρ | wk-sub≡sub Γ⊆Δ σ t
  = refl
\end{code}

\begin{code}
sub-wk≡subⱽ : (σ : Γ ↷ Δ) → (Ε⊆Δ : Ε ⊆ Δ) → (x : T ∈ Ε)
            → substituteⱽ σ (weakenⱽ Ε⊆Δ x) ≡ substituteⱽ (σ ↷-⊆ Ε⊆Δ) x
sub-wk≡subⱽ (σ , T) (drop Ε⊆Δ) x rewrite sub-wk≡subⱽ σ Ε⊆Δ x      = refl
sub-wk≡subⱽ (σ , T) (copy Ε⊆Δ) Z                                  = refl
sub-wk≡subⱽ (σ , T) (copy Ε⊆Δ) (S y) rewrite sub-wk≡subⱽ σ Ε⊆Δ y  = refl
\end{code}

\begin{code}
sub-wk≡sub : (σ : Γ ↷ Δ) → (Ε⊆Δ : Ε ⊆ Δ) → (t : Ε ⊢ T)
      → substitute σ (weaken Ε⊆Δ t) ≡ substitute (σ ↷-⊆ Ε⊆Δ) t
sub-wk≡sub σ Ε⊆Δ true
  = refl
sub-wk≡sub σ Ε⊆Δ false
  = refl
sub-wk≡sub σ Ε⊆Δ (if t₁ then t₂ else t₃)
  rewrite sub-wk≡sub σ Ε⊆Δ t₁ | sub-wk≡sub σ Ε⊆Δ t₂ | sub-wk≡sub σ Ε⊆Δ t₃
  = refl
sub-wk≡sub σ Ε⊆Δ (x N)
  = refl
sub-wk≡sub σ Ε⊆Δ (l ⟨ ⊕ ⟩ᵃ r)
  rewrite sub-wk≡sub σ Ε⊆Δ l | sub-wk≡sub σ Ε⊆Δ r
  = refl
sub-wk≡sub σ Ε⊆Δ (l ⟨ ⊕ ⟩ᶜ r)
  rewrite sub-wk≡sub σ Ε⊆Δ l | sub-wk≡sub σ Ε⊆Δ r
  = refl
sub-wk≡sub σ Ε⊆Δ (t₁ · t₂)
  rewrite sub-wk≡sub σ Ε⊆Δ t₁ | sub-wk≡sub σ Ε⊆Δ t₂
  = refl
sub-wk≡sub σ Ε⊆Δ (′ x) = sub-wk≡subⱽ σ Ε⊆Δ x
sub-wk≡sub {T = T} σ Ε⊆Δ ((let'_in'_) {T₁ = T₂} t₁ t₂)
  rewrite sub-wk≡sub σ Ε⊆Δ t₁ |
          sub-wk≡sub (extend σ) (copy Ε⊆Δ) t₂ |
          assoc-rsr (⊆-wk {_} {T₂}) σ Ε⊆Δ
  = refl
sub-wk≡sub {T = A ⇒ B} σ Ε⊆Δ (ƛ t)
  rewrite sub-wk≡sub (extend σ) (copy Ε⊆Δ) t |
          assoc-rsr (⊆-wk {_} {A}) σ Ε⊆Δ
  = refl
\end{code}

\begin{code}
assoc-srs : (ρ : Ε ↷ Ζ) → (Ε⊆Ζ : Ε ⊆ Δ) → (σ : Γ ↷ Δ)
          → σ ↷↷ (Ε⊆Ζ ⊆-↷ ρ) ≡ (σ ↷-⊆ Ε⊆Ζ) ↷↷ ρ
assoc-srs ∅ Ε⊆Ζ σ
  = refl
assoc-srs (ρ , x) Ε⊆Ζ σ
  rewrite assoc-srs ρ Ε⊆Ζ σ |
          sym (sub-wk≡sub σ Ε⊆Ζ x)
  = refl
\end{code}

\begin{code}
sub↷↷≡sub-subⱽ : (σ : Γ ↷ Ε) → (ρ : Ε ↷ Δ) → (x : T ∈ Δ)
                  → substituteⱽ (σ ↷↷ ρ) x ≡ substitute σ (substituteⱽ ρ x)
sub↷↷≡sub-subⱽ σ (ρ , _) Z
  = refl
sub↷↷≡sub-subⱽ σ (ρ , T) (S x)
  rewrite sub↷↷≡sub-subⱽ σ ρ x
  = refl
\end{code}

\begin{code}
sub↷↷≡sub-sub : ∀ {T Γ Δ Ε} → (σ : Γ ↷ Ε) → (ρ : Ε ↷ Δ) → (t : Δ ⊢ T)
            → substitute (σ ↷↷ ρ) t ≡ substitute σ (substitute ρ t)
sub↷↷≡sub-sub σ ρ true = refl
sub↷↷≡sub-sub σ ρ false = refl
sub↷↷≡sub-sub σ ρ (if t₁ then t₂ else t₃)
  rewrite sub↷↷≡sub-sub σ ρ t₁ | sub↷↷≡sub-sub σ ρ t₂ | sub↷↷≡sub-sub σ ρ t₃
    = refl
sub↷↷≡sub-sub σ ρ (x N) = refl
sub↷↷≡sub-sub σ ρ (l ⟨ ⊕ ⟩ᵃ r) rewrite sub↷↷≡sub-sub σ ρ l | sub↷↷≡sub-sub σ ρ r
  = refl
sub↷↷≡sub-sub σ ρ (l ⟨ ⊕ ⟩ᶜ r) rewrite sub↷↷≡sub-sub σ ρ l | sub↷↷≡sub-sub σ ρ r
  = refl
sub↷↷≡sub-sub σ ρ (t₁ · t₂)
  rewrite sub↷↷≡sub-sub σ ρ t₁ | sub↷↷≡sub-sub σ ρ t₂
  = refl
sub↷↷≡sub-sub σ ρ (′ x) = sub↷↷≡sub-subⱽ σ ρ x
sub↷↷≡sub-sub σ ρ ((let'_in'_) {T₁ = T} t₁ t₂)
  rewrite sub↷↷≡sub-sub σ ρ t₁
  = cong (let' substitute σ (substitute ρ t₁) in'_) f
    where
    f : substitute ((drop ⊆-id ⊆-↷ (σ ↷↷ ρ)) , (′ Z)) t₂ ≡
        substitute ((drop ⊆-id ⊆-↷ σ) , (′ Z)) (substitute ((drop ⊆-id ⊆-↷ ρ) , (′ Z)) t₂)
    f =
      begin
        substitute ((drop ⊆-id ⊆-↷ (σ ↷↷ ρ)) , (′ Z)) t₂
      ≡⟨ cong (λ x → substitute (x , (′ Z)) t₂) (assoc-rss ⊆-wk σ ρ) ⟩
        substitute (((drop ⊆-id ⊆-↷ σ) ↷↷ ρ) , (′ Z)) t₂
      ≡⟨ cong (λ x → substitute ((x ↷↷ ρ) , (′ Z)) t₂) (sym (⊆-↷-id (⊆-wk ⊆-↷ σ))) ⟩
        substitute ((((drop ⊆-id ⊆-↷ σ) ↷-⊆ ⊆-id) ↷↷ ρ) , (′ Z)) t₂
      ≡⟨ cong (λ x → substitute (x , (′ Z)) t₂) (sym (assoc-srs ρ ⊆-wk (extend σ))) ⟩
        substitute ((((drop ⊆-id ⊆-↷ σ) , (′ Z)) ↷↷ (drop ⊆-id ⊆-↷ ρ)) , (′ Z)) t₂
      ≡⟨ sub↷↷≡sub-sub (extend σ) (extend ρ) t₂ ⟩
        substitute ((drop ⊆-id ⊆-↷ σ) , (′ Z)) (substitute ((drop ⊆-id ⊆-↷ ρ) , (′ Z)) t₂)
      ∎
sub↷↷≡sub-sub {T = A ⇒ B} σ ρ (ƛ t) = cong ƛ_ f
  where
  f : (substitute (extend (σ ↷↷ ρ)) t) ≡
      (substitute (extend σ) (substitute (extend ρ) t))
  f =
    begin
      substitute (extend (σ ↷↷ ρ)) t
    ≡⟨ cong (λ x → substitute (x , (′ Z)) t) (assoc-rss ⊆-wk σ ρ) ⟩
     substitute (((drop ⊆-id ⊆-↷ σ) ↷↷ ρ) , (′ Z)) t
    ≡⟨ cong (λ x → substitute ((x ↷↷ ρ) , (′ Z)) t) (sym (⊆-↷-id (⊆-wk ⊆-↷ σ))) ⟩
     substitute ((((drop ⊆-id ⊆-↷ σ) ↷-⊆ ⊆-id) ↷↷ ρ) , (′ Z)) t
    ≡⟨ cong (λ x → substitute (x , (′ Z)) t) (sym (assoc-srs ρ (⊆-wk {_} {A}) (extend σ))) ⟩
     substitute ((extend σ ↷↷ (drop ⊆-id ⊆-↷ ρ)) , (′ Z)) t
    ≡⟨ sub↷↷≡sub-sub (extend σ) (extend ρ) t ⟩
     substitute (extend σ) (substitute (extend ρ) t)
    ∎
\end{code}

\begin{code}
sub-wkⱽ : (Δ⊆Γ : Δ ⊆ Γ) → (σ : Δ ↷ Ε) → (x : T ∈ Ε)
           → substituteⱽ (Δ⊆Γ ⊆-↷ σ) x ≡ weaken Δ⊆Γ (substituteⱽ σ x)
sub-wkⱽ Δ⊆Γ (σ , y) Z      = refl
sub-wkⱽ Δ⊆Γ (σ , y) (S x)  = sub-wkⱽ Δ⊆Γ σ x
\end{code}

\begin{code}
sub-reflⱽ : ∀ {Γ T} → (x : T ∈ Γ) → substituteⱽ Γ↷Γ x ≡ (′ x)
sub-reflⱽ Z = refl
sub-reflⱽ {Γ , B} {T} (S x) =
  begin
    substituteⱽ Γ↷Γ (S x)
  ≡⟨⟩
    substituteⱽ ((drop ⊆-id ⊆-↷ Γ↷Γ) , (′ Z)) (S x)
  ≡⟨ sub-wkⱽ (drop ⊆-id) Γ↷Γ x ⟩
    weaken (drop ⊆-id) (substituteⱽ Γ↷Γ x)
  ≡⟨ cong (λ y → weaken (drop ⊆-id) y) (sub-reflⱽ x) ⟩
    weaken (drop ⊆-id ) (′ x)
  ≡⟨ cong (λ y → ′ (S y)) (wk-id≡reflⱽ x) ⟩
    ′ (S x)
  ∎
\end{code}

\begin{code}
sub-refl : (t : Γ ⊢ T) → substitute Γ↷Γ t ≡ t
sub-refl true
  = refl
sub-refl false
  = refl
sub-refl (if t₁ then t₂ else t₃)
  rewrite sub-refl t₁ | sub-refl t₂ | sub-refl t₃
  = refl
sub-refl (x N)
  = refl
sub-refl (l ⟨ ⊕ ⟩ᵃ r)
  rewrite sub-refl l | sub-refl r
  = refl
sub-refl (l ⟨ ⊗ ⟩ᶜ r)
  rewrite sub-refl l | sub-refl r
  = refl
sub-refl (let' t₁ in' t₂)
  rewrite sub-refl t₁ | sub-refl t₂
  = refl
sub-refl (t₁ · t₂)
  rewrite sub-refl t₁ | sub-refl t₂
  = refl
sub-refl (ƛ t)
  rewrite sub-refl t
  = refl
sub-refl (′ x) = sub-reflⱽ x
\end{code}

\begin{code}
sub-∅ : (t : ∅ ⊢ T) → substitute ∅ t ≡ t
sub-∅ = sub-refl
\end{code}

\begin{code}
∅↷↷drop : ∀ {Γ T} → (σ : ∅ ↷ Γ) → (u : ∅ ⊢ T)
            → (∅ , u) ↷↷ (drop ∅ ⊆-↷ σ) ≡ σ
∅↷↷drop ∅ u = refl
∅↷↷drop (σ , x) u
  rewrite ∅↷↷drop σ u
        | sub-wk≡sub (∅ , u) ⊆-wk x
        | sub-∅ x
  = refl
\end{code}
