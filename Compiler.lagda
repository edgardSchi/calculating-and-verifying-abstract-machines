--------------------------------------------------------------------------------
-
- Deriving a compiler for an abstract machine
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Compiler where

open import Data.Nat using (ℕ; _+_; zero; suc; _∸_; _*_) renaming (_<_ to _≺_)
open import Data.Bool using () renaming (Bool to 𝔹)
open import Data.Vec hiding (count; length) renaming (_∷_ to _∷ⱽ_)
open import Data.List hiding (length; _++_; [_]; _∷ʳ_; lookup)
open import Data.Fin using (Fin)
open import Data.Product using (∃; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import AbstractMachines.Language.Types
  renaming (+ to +ₗ; ∸ to ∸ₗ; * to *ₗ; ≈ to ≈ₗ; ≠ to ≠ₗ;
            < to <ₗ; ≤ to ≤ₗ; > to >ₗ; ≥ to ≥ₗ)
  hiding (lookup; _,_)
open import AbstractMachines.Language.Big-Step
open import AbstractMachines.Language.Reduction.Properties hiding (by-definition)
\end{code}

\begin{code}
private variable
  n m o p : ℕ
  Γ Δ Ε : Context
  T T' : Type
  t t' : (Γ ⊢ T)
\end{code}

--------------------------------------------------------------------------------

\begin{code}
mutual
\end{code}

𝗠𝗮𝗰𝗵𝗶𝗻𝗲 𝗖𝗼𝗱𝗲 𝗩𝗮𝗹𝘂𝗲𝘀
The values that can be produced during compilation by the abstract machine
<Value-Definition>
\begin{code}
  data Valueᶜ : Set where
    TRUE     : Valueᶜ
    FALSE    : Valueᶜ
    NATURAL  : ℕ → Valueᶜ
    CLOSURE  : Code → Environmentᶜ m → Valueᶜ
\end{code}

𝗘𝗻𝘃𝗶𝗿𝗼𝗻𝗺𝗲𝗻𝘁
An environment is simply a vector of values
<Environment-Definition>
\begin{code}
  Environmentᶜ = Vec Valueᶜ
\end{code}

We change to constructor for vectors to the more familiar comma operator
\begin{code}
  pattern _,_ γ v = v Data.Vec.∷ γ
\end{code}

𝗠𝗮𝗰𝗵𝗶𝗻𝗲 𝗜𝗻𝘀𝘁𝗿𝘂𝗰𝘁𝗶𝗼𝗻𝘀
Instructions of the abstract machine, obtained through the derivation
process
<Code-Definition>
\begin{code}
  data Code : Set where
    PUSH     : (v : Valueᶜ) → Code → Code
    LOOKUP   : (Fin n) → Code → Code
    RET      : Code
    APP      : Code → Code
    ABS      : Code → Code → Code
    SAVE     : Code → Code
    DISCARD  : Code → Code
    ADD      : Code → Code
    SUB      : Code → Code
    MUL      : Code → Code
    EQ       : Code → Code
    NEQ      : Code → Code
    LT       : Code → Code
    LTE      : Code → Code
    GT       : Code → Code
    GTE      : Code → Code
    IF       : Code → Code → Code
    HALT     : Code
\end{code}

<Lookup>
\begin{code}
∈→ℕ : ∀ (x : T ∈ Γ) → ℕ
∈→ℕ Z      = zero
∈→ℕ (S x)  = suc (∈→ℕ x)

∈→Fin : ∀ (x : T ∈ Γ) → Fin (length Γ)
∈→Fin Z = Fin.zero
∈→Fin (S x) = Fin.suc (∈→Fin x)
\end{code}

𝗦𝘁𝗮𝗰𝗸
Stack the machine operates on, as a simple vector.
The third constructor was added during the derivation process
<Stack>
\begin{code}
data Stack : ℕ → Set where
  []      : Stack 0
  _∷_     : Valueᶜ → Stack n → Stack (1 + n)
  _/_∷ᶜ_  : Code → Environmentᶜ m → Stack n → Stack (1 + n)
\end{code}

𝗖𝗼𝗻𝗳𝗶𝗴𝘂𝗿𝗮𝘁𝗶𝗼𝗻
The machines configuration consisting of the environment
and stack. It represents the machine's current state
<Config>
\begin{code}
Config : ℕ → ℕ → Set
Config m n = Environmentᶜ m × Stack n
\end{code}

Pattern synonym for constructing the config. Avoids
confusion with the environment's comma operator
<Config-Pattern>
\begin{code}
pattern ⟪_∥_⟫ γ s = Data.Product._,_ γ s
\end{code}

𝗖𝗼𝗺𝗽𝗶𝗹𝗲 𝗙𝘂𝗻𝗰𝘁𝗶𝗼𝗻
Function transforming a term from the source language to
machine instructions. It uses continuation passing style
for the derivation process.
All definitions where obtained through the derivation
process.
<Compile-Dash-Function>
\begin{code}
compile' : Γ ⊢ T → Code → Code
compile' true c = PUSH TRUE c
compile' false c = PUSH FALSE c
compile' (n N) c = PUSH (NATURAL n) c
compile' (if t₁ then t₂ else t₃) c
  = compile' t₁ (IF (compile' t₂ c) (compile' t₃ c))
compile' (t₁ ⟨ +ₗ ⟩ᵃ t₂) c = compile' t₁ (compile' t₂ (ADD c))
compile' (t₁ ⟨ ∸ₗ ⟩ᵃ t₂) c = compile' t₁ (compile' t₂ (SUB c))
compile' (t₁ ⟨ *ₗ ⟩ᵃ t₂) c = compile' t₁ (compile' t₂ (MUL c))
compile' (t₁ ⟨ ≈ₗ ⟩ᶜ t₂) c = compile' t₁ (compile' t₂ (EQ c))
compile' (t₁ ⟨ ≠ₗ ⟩ᶜ t₂) c = compile' t₁ (compile' t₂ (NEQ c))
compile' (t₁ ⟨ <ₗ ⟩ᶜ t₂) c = compile' t₁ (compile' t₂ (LT c))
compile' (t₁ ⟨ ≤ₗ ⟩ᶜ t₂) c = compile' t₁ (compile' t₂ (LTE c))
compile' (t₁ ⟨ >ₗ ⟩ᶜ t₂) c = compile' t₁ (compile' t₂ (GT c))
compile' (t₁ ⟨ ≥ₗ ⟩ᶜ t₂) c = compile' t₁ (compile' t₂ (GTE c))
compile' (let' t₁ in' t₂) c
  = compile' t₁ (SAVE (compile' t₂ (DISCARD c)))
compile' (′ x) c = LOOKUP (∈→Fin x) c
compile' (ƛ_ t) c = (ABS (compile' t RET) c)
compile' (t₁ · t₂) c = compile' t₁ (compile' t₂ (APP c))
\end{code}

\begin{code}
mutual
\end{code}

𝗖𝗼𝗻𝘃𝗲𝗿𝘀𝗶𝗼𝗻 𝗙𝘂𝗻𝗰𝘁𝗶𝗼𝗻𝘀
Functions for converting between values of the source and
target language.
The case for closures was obtained through the derivation
process.
<Conv-Functions>
\begin{code}
    conv : Valueᴮ T → Valueᶜ
    conv true = TRUE
    conv false = FALSE
    conv (n N) = NATURAL n
    conv (closure t γ) = CLOSURE (compile' t RET) (convₑ γ)

    convₑ : Environmentᴮ Γ → Environmentᶜ (length Γ)
    convₑ ∅ = []
    convₑ (γ ,ᴮ v) = (convₑ γ) , (conv v)
\end{code}

𝗘𝘅𝗲𝗰𝘂𝘁𝗲
An execution relates machine code to config. The original
paper uses an actual function, but in the context of Agda
we use this in combination with small-step semantics.
<Execute-Definition>
\begin{code}
data Execute : Code → Config m n → Set where
  execute : (c : Code) → (conf : Config m n) → Execute c conf
\end{code}

Mapping of operators
\begin{code}
_≈_ = ⟦ ≈ₗ ⟧ᶜ
_≠_ = ⟦ ≠ₗ ⟧ᶜ
_<_ = ⟦ <ₗ ⟧ᶜ
_≤_ = ⟦ ≤ₗ ⟧ᶜ
_>_ = ⟦ >ₗ ⟧ᶜ
_≥_ = ⟦ ≥ₗ ⟧ᶜ

𝔹↓ᶜ : 𝔹 → Valueᶜ
𝔹↓ᶜ 𝔹.false = FALSE
𝔹↓ᶜ 𝔹.true  = TRUE
\end{code}

\begin{code}
private variable
  n₁ n₂ : ℕ
  q r : ℕ
  v : Valueᶜ
  x : T ∈ Γ
  c c' c'' c₁ c₂ : Code
  γ : Environmentᶜ m
  δ : Environmentᶜ o
  conf   : Config m n
  conf'  : Config o p
  conf'' : Config q r
  s : Stack m
\end{code}

𝗦𝗺𝗮𝗹𝗹-𝗦𝘁𝗲𝗽 𝗦𝗲𝗺𝗮𝗻𝘁𝗶𝗰𝘀
Semantics of executing machine code, relating two executions.
This mimics the 'exec' function from the original paper. All
constructors are obtained from the derivation process.
<Small-Step-Definition>
\begin{code}
data _⟹_ : Execute c conf → Execute c' conf' → Set where
  executePUSH      : execute (PUSH v c) ⟪ γ ∥ s ⟫ ⟹ execute c ⟪ γ ∥ v ∷ s ⟫
  executeLOOKUP    : ∀ {n : Fin m} → {γ : Environmentᶜ m}
                     → execute (LOOKUP n c) ⟪ γ ∥ s ⟫
                       ⟹
                       execute c ⟪ γ ∥ lookup γ n ∷ s ⟫
  executeRET       : execute RET ⟪ γ ∥ v ∷ c / δ ∷ᶜ s ⟫ ⟹ execute c ⟪ δ ∥ v ∷ s ⟫
  executeAPP       : execute (APP c) ⟪ γ ∥ v ∷ CLOSURE c' δ ∷ s ⟫
                     ⟹
                     execute c' ⟪ δ , v ∥ c / γ ∷ᶜ s ⟫
  executeABS       : execute (ABS c' c) ⟪ γ ∥ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ CLOSURE c' γ ∷ s ⟫
  executeSAVE      : execute (SAVE c) ⟪ γ ∥ v ∷ s ⟫ ⟹ execute c ⟪ γ , v ∥ s ⟫
  executeDISCARD   : execute (DISCARD c) ⟪ γ , v ∥ s ⟫ ⟹ execute c ⟪ γ ∥ s ⟫
  executeIF-TRUE   : execute (IF c₁ c₂) ⟪ γ ∥ TRUE ∷ s ⟫
                     ⟹
                     execute c₁ ⟪ γ ∥ s ⟫
  executeIF-FALSE  : execute (IF c₁ c₂) ⟪ γ ∥ FALSE ∷ s ⟫
                     ⟹
                     execute c₂ ⟪ γ ∥ s ⟫
  executeADD       : execute (ADD c) ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ NATURAL (n₁ + n₂) ∷ s ⟫
  executeSUB       : execute (SUB c) ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ NATURAL (n₁ ∸ n₂) ∷ s ⟫
  executeMUL       : execute (MUL c) ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ NATURAL (n₁ * n₂) ∷ s ⟫
  executeEQ        : execute (EQ c)  ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ 𝔹↓ᶜ (n₁ ≈ n₂) ∷ s ⟫
  executeNEQ       : execute (NEQ c) ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ 𝔹↓ᶜ (n₁ ≠ n₂) ∷ s ⟫
  executeLT        : execute (LT c)  ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ 𝔹↓ᶜ (n₁ < n₂) ∷ s ⟫
  executeLTE       : execute (LTE c) ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ 𝔹↓ᶜ (n₁ ≤ n₂) ∷ s ⟫
  executeGT        : execute (GT c)  ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ 𝔹↓ᶜ (n₁ > n₂) ∷ s ⟫
  executeGTE       : execute (GTE c) ⟪ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
                     ⟹
                     execute c ⟪ γ ∥ 𝔹↓ᶜ (n₁ ≥ n₂) ∷ s ⟫
\end{code}


--------------------------------------------------------------------------------
- Definitions for derivation process
--------------------------------------------------------------------------------

\begin{code}
data _⟹*_ : Execute c conf → Execute c' conf' → Set where
  executeRefl   : execute c conf ⟹* execute c conf
  executeTrans  : execute c conf ⟹* execute c' conf'
                → execute c' conf' ⟹* execute c'' conf''
                → execute c conf ⟹* execute c'' conf''
  executeStep   : execute c conf ⟹ execute c' conf'
                → execute c conf ⟹* execute c' conf'
\end{code}

\begin{code}
by-definition : ∀ {c : Code} → {conf : Config m n} → execute c conf ⟹* execute c conf
by-definition = executeRefl

define = by-definition
\end{code}

\begin{code}
infix 3 _⟹*∎ *⟸-begin_
infixr 2 step-⟹* step-⟹ 
infixl 2 step-*⟸ step-⟸ _⟸⟨define:_⟩_
infix 1 ⟹*begin_ _*⟸∎
\end{code}

\begin{code}
⟹*begin_ : ∀ {m} → {c c' : Code}
            → {conf : Config m n}
            → {conf' : Config o p}
            → execute c conf ⟹* execute c' conf'
            → execute c conf ⟹* execute c' conf'
⟹*begin_ p = p

*⟸-begin_ : ∀ {c : Code} → {conf : Config m n} → Execute c conf → execute c conf ⟹* execute c conf
*⟸-begin_ p = executeRefl
\end{code}

\begin{code}
step-⟹* : ∀ {c c' c'' : Code}
           → {conf : Config m n}
           → {conf' : Config o p}
           → {conf'' : Config q r}
           → Execute c conf
           → execute c' conf' ⟹* execute c'' conf''
           → execute c conf ⟹* execute c' conf'
           → execute c conf ⟹* execute c'' conf''
step-⟹* _ p q = executeTrans q p

syntax step-⟹* exec exec'⟹*exec'' exec⟹*exec' = exec ⟹*⟨ exec⟹*exec' ⟩ exec'⟹*exec''


step-*⟸ : ∀ {c c' c'' : Code}
           → {conf : Config m n}
           → {conf' : Config o p}
           → {conf'' : Config q r}
           → execute c' conf' ⟹* execute c'' conf''
           → execute c conf ⟹* execute c' conf'
           → Execute c conf
           → execute c conf ⟹* execute c'' conf''
step-*⟸ p q _ = executeTrans q p

syntax step-*⟸ exec'⟹*exec'' exec⟹*exec' exec = exec'⟹*exec'' *⟸⟨ exec⟹*exec' ⟩ exec


step-⟹ : ∀ {c c' c'' : Code}
           → {conf : Config m n}
           → {conf' : Config o p}
           → {conf'' : Config q r}
           → Execute c conf
           → execute c' conf' ⟹* execute c'' conf''
           → execute c conf ⟹ execute c' conf'
           → execute c conf ⟹* execute c'' conf''
step-⟹ _ p q = executeTrans (executeStep q) p

syntax step-⟹ exec exec'⟹*exec'' exec⟹exec' = exec ⟹⟨ exec⟹exec' ⟩ exec'⟹*exec''


step-⟸ : ∀ {c c' c'' : Code}
           → {conf : Config m n}
           → {conf' : Config o p}
           → {conf'' : Config q r}
           → execute c' conf' ⟹* execute c'' conf''
           → execute c conf ⟹ execute c' conf'
           → Execute c conf
           → execute c conf ⟹* execute c'' conf''
step-⟸ p q _ = executeTrans (executeStep q) p

syntax step-⟸ exec'⟹*exec'' exec⟹exec' exec = exec'⟹*exec'' ⟸⟨ exec⟹exec' ⟩ exec

_⟸⟨define:_⟩_ = step-⟸
\end{code}

\begin{code}
_⟹*∎ : ∀ {c : Code} → {conf : Config m n} → Execute c conf → execute c conf ⟹* execute c conf
_⟹*∎ _ = executeRefl

_*⟸∎ : ∀ {m} → {c c' : Code}
        → {conf : Config m n}
        → {conf' : Config o p}
        → execute c conf ⟹* execute c' conf'
        → execute c conf ⟹* execute c' conf'
_*⟸∎ p = p
\end{code}

--------------------------------------------------------------------------------
- Helper functions and lemmas
--------------------------------------------------------------------------------

\begin{code}
≡-config : ∀ {c : Code} {conf : Config m n} {conf' : Config m n}
           → conf ≡ conf'
           → execute c conf ⟹* execute c conf'
≡-config refl = executeRefl
\end{code}

\begin{code}
≡-stack : ∀ {s : Stack m} {s' : Stack m} {γ : Environmentᶜ n}
          → s ≡ s'
          → execute c ⟪ γ ∥ s ⟫ ⟹* execute c ⟪ γ ∥ s' ⟫
≡-stack refl = executeRefl
\end{code}

<Map-Lookup>
\begin{code}
map-lookup : ∀ (γ : Environmentᴮ Γ)
             → (x : T ∈ Γ)
             → lookup (convₑ γ) (∈→Fin x) ≡ conv (lookupᴮ γ x)
\end{code}
\begin{code}
map-lookup (γ ,ᴮ x) Z = refl
map-lookup (γ ,ᴮ x) (S y) = map-lookup γ y
\end{code}

\begin{code}
natural≡conv : ∀ {v : Valueᴮ Nat} → conv v ≡ NATURAL (N↑ᴮ v)
natural≡conv {n N} = refl

definition-of-conv : ∀ {s : Stack m} {γ : Environmentᶜ n} {v : Valueᴮ Nat}
                     → execute c ⟪ γ ∥ NATURAL (N↑ᴮ v) ∷ s ⟫
                       ⟹*
                       execute c ⟪ γ ∥ conv v ∷ s ⟫
definition-of-conv {s = s} = ≡-stack (cong (_∷ s) (sym natural≡conv))

bool≡conv : ∀ {b : 𝔹} → conv (𝔹↓ᴮ b) ≡ 𝔹↓ᶜ b
bool≡conv {𝔹.false} = refl
bool≡conv {𝔹.true} = refl
\end{code}

--------------------------------------------------------------------------------
- Compiler derivation
--------------------------------------------------------------------------------

𝗦𝗽𝗲𝗰𝗶𝗳𝗶𝗰𝗮𝘁𝗶𝗼𝗻
Specification of correctness for the compiler. This is used
to calculate the definitions from above.
<Spec-Definition>
\begin{code}
spec' :
     ∀ {γ : Environmentᴮ Γ}
     → (t : Γ ⊢ T)
     → {v : Valueᴮ T}
     → (γ ⊢ t ⇓ v)
     → (c : Code)
     → (s : Stack m)
     → execute (compile' t c) ⟪ convₑ γ ∥ s ⟫
       ⟹*
       execute c ⟪ convₑ γ ∥ conv v ∷ s ⟫
spec' {γ = γ} true True c s =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv true ∷ s ⟫
  *⟸⟨ by-definition ⟩
    execute c ⟪ convₑ γ ∥ TRUE ∷ s ⟫
  ⟸⟨define: executePUSH ⟩
    execute (PUSH TRUE c) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} false False c s =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ FALSE ∷ s ⟫
  ⟸⟨define: executePUSH ⟩
    execute (PUSH FALSE c) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (n N) Num c s =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ NATURAL n ∷ s ⟫
  ⟸⟨define: executePUSH ⟩
    execute (PUSH (NATURAL n) c) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (if t₁ then t₂ else t₃) (If-True {v = v} t₁⇓true t₂⇓v) c s
  with spec' t₂ t₂⇓v c s | spec' t₁ t₁⇓true (IF (compile' t₂ c) _) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv v ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ c) ⟪ convₑ γ ∥ s ⟫
  ⟸⟨define: executeIF-TRUE ⟩
    execute (IF (compile' t₂ c) _) ⟪ convₑ γ ∥ TRUE ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (IF (compile' t₂ c) _)) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (if t₁ then t₂ else t₃) (If-False {v = v} t₁⇓false t₃⇓v) c s
  with spec' t₃ t₃⇓v c s | spec' t₁ t₁⇓false (IF _ (compile' t₃ c)) s
... | indHyp-t₃ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv v ∷ s ⟫
  *⟸⟨ indHyp-t₃ ⟩
    execute (compile' t₃ c) ⟪ convₑ γ ∥ s ⟫
  ⟸⟨define: executeIF-FALSE ⟩
    execute (IF _ (compile' t₃ c)) ⟪ convₑ γ ∥ FALSE ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (IF _ (compile' t₃ c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (′ x) (Var {v = v} {l = l}) c s =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv v ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ v → conv v ∷ s) l) ⟩
    execute c ⟪ convₑ γ ∥ conv (lookupᴮ γ x) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ v → v ∷ s) (map-lookup γ x)) ⟩
    execute c ⟪ convₑ γ ∥ lookup (convₑ γ) (∈→Fin x) ∷ s ⟫
  ⟸⟨define: executeLOOKUP ⟩
    execute (LOOKUP (∈→Fin x) c) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {m = m} {γ = γ} (ƛ_ t') Lambda c s = 
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv (closure t' γ) ∷ s ⟫
  *⟸⟨ by-definition ⟩
    execute c ⟪ convₑ γ ∥ CLOSURE (compile' t' RET) (convₑ γ) ∷ s ⟫
  ⟸⟨define: executeABS ⟩
    execute (ABS (compile' t' RET) c) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ · t₂) (App {T₁ = T₁} {δ = δ} {t = t'} {v = v} {v₂ = v₂} t₁⇓clos t₂⇓v₂ t'⇓v) c s
  with spec' t' t'⇓v RET (c / (convₑ γ) ∷ᶜ s) | spec' t₂ t₂⇓v₂ (APP c) (CLOSURE (compile' t' RET) (convₑ δ) ∷ s) | spec' t₁ t₁⇓clos (compile' t₂ (APP c)) s
... | indHyp-t' | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv v ∷ s ⟫
  ⟸⟨define: executeRET ⟩
    execute RET ⟪ convₑ δ , conv v₂ ∥ conv v ∷ c / (convₑ γ) ∷ᶜ s ⟫
  *⟸⟨ indHyp-t' ⟩
    execute (compile' t' RET) ⟪ convₑ δ , conv v₂ ∥ c / (convₑ γ) ∷ᶜ s ⟫
  ⟸⟨define: executeAPP ⟩
    execute (APP c)
      ⟪ convₑ γ ∥ conv v₂ ∷ CLOSURE (compile' t' RET) (convₑ δ) ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (APP c))
      ⟪ convₑ γ ∥ CLOSURE (compile' t' RET) (convₑ δ) ∷ s ⟫
  *⟸⟨ define ⟩
    execute (compile' t₂ (APP c)) ⟪ convₑ γ ∥ conv (closure t' δ) ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (APP c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (let' t₁ in' t₂) (Let {v₁ = v₁} {v = v} t₁⇓v₁ t₂⇓v) c s
  with spec' t₁ t₁⇓v₁ (SAVE (compile' t₂ (DISCARD c))) s | spec' t₂ t₂⇓v (DISCARD c) s
... | indHyp-t₁ | indHyp-t₂ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv v ∷ s ⟫
  ⟸⟨define: executeDISCARD ⟩
    execute (DISCARD c) ⟪ convₑ γ , conv v₁ ∥ conv v ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (DISCARD c)) ⟪ convₑ γ , conv v₁ ∥ s ⟫
  ⟸⟨define: executeSAVE ⟩
    execute (SAVE (compile' t₂ (DISCARD c))) ⟪ convₑ γ ∥ conv v₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (SAVE (compile' t₂ (DISCARD c)))) ⟪ convₑ γ ∥ s ⟫ 
  *⟸∎
spec' {γ = γ} (t₁ ⟨ +ₗ ⟩ᵃ t₂) (Arith {n₁ = n₁} {n₂ = n₂} t₁⇓n₁ t₂⇓n₂) c s
  with spec' t₂ t₂⇓n₂ (ADD c) (NATURAL (N↑ᴮ n₁) ∷ s) | spec' t₁ t₁⇓n₁ (compile' t₂ (ADD c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv (_N (N↑ᴮ n₁ + N↑ᴮ n₂)) ∷ s ⟫
  *⟸⟨ by-definition ⟩
    execute c ⟪ convₑ γ ∥ NATURAL (N↑ᴮ n₁ + N↑ᴮ n₂) ∷ s ⟫
  ⟸⟨define: executeADD ⟩
    execute (ADD c) ⟪ convₑ γ ∥ NATURAL (N↑ᴮ n₂) ∷ NATURAL (N↑ᴮ n₁) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ NATURAL (N↑ᴮ n₁) ∷ s) natural≡conv) ⟩
    execute (ADD c) ⟪ convₑ γ ∥ conv n₂ ∷ (NATURAL (N↑ᴮ n₁) ∷ s) ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (ADD c)) ⟪ convₑ γ ∥ NATURAL (N↑ᴮ n₁) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) natural≡conv) ⟩
    execute (compile' t₂ (ADD c)) ⟪ convₑ γ ∥ conv n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (ADD c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ ⟨ ∸ₗ ⟩ᵃ t₂) (Arith {n₁ = n₁} {n₂ = n₂} t₁⇓n₁ t₂⇓n₂) c s
  with spec' t₂ t₂⇓n₂ (SUB c) (NATURAL (N↑ᴮ n₁) ∷ s) | spec' t₁ t₁⇓n₁ (compile' t₂ (SUB c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ NATURAL (N↑ᴮ n₁ ∸ N↑ᴮ n₂) ∷ s ⟫
  ⟸⟨define: executeSUB ⟩
    execute (SUB c) ⟪ (convₑ γ) ∥ NATURAL (N↑ᴮ n₂) ∷ NATURAL (N↑ᴮ n₁) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ NATURAL (N↑ᴮ n₁) ∷ s) natural≡conv) ⟩
    execute (SUB c) ⟪ convₑ γ ∥ conv n₂ ∷ (NATURAL (N↑ᴮ n₁) ∷ s) ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (SUB c)) ⟪ convₑ γ ∥ NATURAL (N↑ᴮ n₁) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) natural≡conv) ⟩
    execute (compile' t₂ (SUB c)) ⟪ convₑ γ ∥ conv n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (SUB c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ ⟨ *ₗ ⟩ᵃ t₂) (Arith {n₁ = n₁} {n₂ = n₂} t₁⇓n₁ t₂⇓n₂) c s
  with spec' t₂ t₂⇓n₂ (MUL c) (NATURAL (N↑ᴮ n₁) ∷ s) | spec' t₁ t₁⇓n₁ (compile' t₂ (MUL c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ NATURAL (N↑ᴮ n₁ * N↑ᴮ n₂) ∷ s ⟫
  ⟸⟨define: executeMUL ⟩
    execute (MUL c) ⟪ (convₑ γ) ∥ NATURAL (N↑ᴮ n₂) ∷ NATURAL (N↑ᴮ n₁) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ NATURAL (N↑ᴮ n₁) ∷ s) natural≡conv) ⟩
    execute (MUL c) ⟪ convₑ γ ∥ conv n₂ ∷ (NATURAL (N↑ᴮ n₁) ∷ s) ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (MUL c)) ⟪ convₑ γ ∥ NATURAL (N↑ᴮ n₁) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) natural≡conv) ⟩
    execute (compile' t₂ (MUL c)) ⟪ convₑ γ ∥ conv n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (MUL c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ ⟨ ≈ₗ ⟩ᶜ t₂) (Comp {n₁ = n₁} {n₂ = n₂} t₁⇓v₁ t₂⇓v₂) c s
  with spec' t₂ t₂⇓v₂ (EQ c) (NATURAL n₁ ∷ s) | spec' t₁ t₁⇓v₁ (compile' t₂ (EQ c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv (𝔹↓ᴮ (n₁ ≈ n₂)) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) (sym bool≡conv)) ⟩
    execute c ⟪ convₑ γ ∥ 𝔹↓ᶜ (n₁ ≈ n₂) ∷ s ⟫ --execute c ⟪ convₑ γ ∥ 𝔹↓ᶜ b ∷ s ⟫
  ⟸⟨define: executeEQ ⟩
    execute (EQ c) ⟪ convₑ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (EQ c)) ⟪ convₑ γ ∥ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (EQ c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ ⟨ ≠ₗ ⟩ᶜ t₂) (Comp {n₁ = n₁} {n₂ = n₂} t₁⇓v₁ t₂⇓v₂) c s
  with spec' t₂ t₂⇓v₂ (NEQ c) (NATURAL n₁ ∷ s) | spec' t₁ t₁⇓v₁ (compile' t₂ (NEQ c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv (𝔹↓ᴮ (n₁ ≠ n₂)) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) (sym bool≡conv)) ⟩
    execute c ⟪ convₑ γ ∥ 𝔹↓ᶜ (n₁ ≠ n₂) ∷ s ⟫
  ⟸⟨define: executeNEQ ⟩
    execute (NEQ c) ⟪ convₑ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (NEQ c)) ⟪ convₑ γ ∥ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (NEQ c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ ⟨ <ₗ ⟩ᶜ t₂) (Comp {n₁ = n₁} {n₂ = n₂} t₁⇓v₁ t₂⇓v₂) c s
  with spec' t₂ t₂⇓v₂ (LT c) (NATURAL n₁ ∷ s) | spec' t₁ t₁⇓v₁ (compile' t₂ (LT c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv (𝔹↓ᴮ (n₁ < n₂)) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) (sym bool≡conv)) ⟩
    execute c ⟪ convₑ γ ∥ 𝔹↓ᶜ (n₁ < n₂) ∷ s ⟫
  ⟸⟨define: executeLT ⟩
    execute (LT c) ⟪ convₑ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (LT c)) ⟪ convₑ γ ∥ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (LT c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ ⟨ ≤ₗ ⟩ᶜ t₂) (Comp {n₁ = n₁} {n₂ = n₂} t₁⇓v₁ t₂⇓v₂) c s
  with spec' t₂ t₂⇓v₂ (LTE c) (NATURAL n₁ ∷ s) | spec' t₁ t₁⇓v₁ (compile' t₂ (LTE c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv (𝔹↓ᴮ (n₁ ≤ n₂)) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) (sym bool≡conv)) ⟩
    execute c ⟪ convₑ γ ∥ 𝔹↓ᶜ (n₁ ≤ n₂) ∷ s ⟫
  ⟸⟨define: executeLTE ⟩
    execute (LTE c) ⟪ convₑ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (LTE c)) ⟪ convₑ γ ∥ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (LTE c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ ⟨ >ₗ ⟩ᶜ t₂) (Comp {n₁ = n₁} {n₂ = n₂} t₁⇓v₁ t₂⇓v₂) c s
  with spec' t₂ t₂⇓v₂ (GT c) (NATURAL n₁ ∷ s) | spec' t₁ t₁⇓v₁ (compile' t₂ (GT c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv (𝔹↓ᴮ (n₁ > n₂)) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) (sym bool≡conv)) ⟩
    execute c ⟪ convₑ γ ∥ 𝔹↓ᶜ (n₁ > n₂) ∷ s ⟫
  ⟸⟨define: executeGT ⟩
    execute (GT c) ⟪ convₑ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (GT c)) ⟪ convₑ γ ∥ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (GT c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
spec' {γ = γ} (t₁ ⟨ ≥ₗ ⟩ᶜ t₂) (Comp {n₁ = n₁} {n₂ = n₂} t₁⇓v₁ t₂⇓v₂) c s
  with spec' t₂ t₂⇓v₂ (GTE c) (NATURAL n₁ ∷ s) | spec' t₁ t₁⇓v₁ (compile' t₂ (GTE c)) s
... | indHyp-t₂ | indHyp-t₁ =
  *⟸-begin
    execute c ⟪ convₑ γ ∥ conv (𝔹↓ᴮ (n₁ ≥ n₂)) ∷ s ⟫
  *⟸⟨ ≡-stack (cong (λ x → x ∷ s) (sym bool≡conv)) ⟩
    execute c ⟪ convₑ γ ∥ 𝔹↓ᶜ (n₁ ≥ n₂) ∷ s ⟫
  ⟸⟨define: executeGTE ⟩
    execute (GTE c) ⟪ convₑ γ ∥ NATURAL n₂ ∷ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₂ ⟩
    execute (compile' t₂ (GTE c)) ⟪ convₑ γ ∥ NATURAL n₁ ∷ s ⟫
  *⟸⟨ indHyp-t₁ ⟩
    execute (compile' t₁ (compile' t₂ (GTE c))) ⟪ convₑ γ ∥ s ⟫
  *⟸∎
\end{code}

A compile function without continuation, based on compile'
<Compile-Function>
\begin{code}
compile : Γ ⊢ T → Code
compile t = compile' t HALT
\end{code}

A specification without continuation, based on spec'
<Spec-Function>
\begin{code}
spec :
     ∀ {γ : Environmentᴮ Γ}
     → (t : Γ ⊢ T)
     → {v : Valueᴮ T}
     → (γ ⊢ t ⇓ v)
     → (s : Stack m)
     → execute (compile t) ⟪ convₑ γ ∥ s ⟫
       ⟹*
       execute HALT ⟪ convₑ γ ∥ conv v ∷ s ⟫
spec t t⇓v s = spec' t t⇓v HALT s
\end{code}

--------------------------------------------------------------------------------
- Examples
--------------------------------------------------------------------------------

\begin{code}
example1 : ∅ ⊢ Nat
example1 = _N 3

example2 : ∅ ⊢ Nat
example2 = (ƛ_ (# 0)) · (_N 10)

example3 : Code
example3 = ABS (LOOKUP (Fin.zero {n = 0}) RET) (PUSH (NATURAL 10) (APP HALT))

comp2≡3 : compile example2 ≡ example3
comp2≡3 = refl

example3Exec : execute (ABS (LOOKUP Fin.zero RET) (PUSH (NATURAL 10) (APP HALT))) ⟪ [] ∥ [] ⟫
               ⟹*
               execute HALT ⟪ [] ∥ NATURAL 10 ∷ [] ⟫
example3Exec =
  ⟹*begin
     execute (ABS (LOOKUP Fin.zero RET) (PUSH (NATURAL 10) (APP HALT))) ⟪ [] ∥ [] ⟫
  ⟹*⟨ executeStep executeABS ⟩
    execute (PUSH (NATURAL 10) (APP HALT))
      ⟪ [] ∥ CLOSURE (LOOKUP Fin.zero RET) [] ∷ [] ⟫
  ⟹*⟨ executeStep executePUSH ⟩
    execute (APP HALT) ⟪ [] ∥ NATURAL 10 ∷ (CLOSURE (LOOKUP Fin.zero RET) [] ∷ []) ⟫
  ⟹*⟨ executeStep executeAPP ⟩
    execute (LOOKUP Fin.zero RET) ⟪ [] , NATURAL 10 ∥ HALT / [] ∷ᶜ [] ⟫
  ⟹*⟨ executeStep executeLOOKUP ⟩
    execute RET ⟪ [] , NATURAL 10 ∥ NATURAL 10 ∷ (HALT / [] ∷ᶜ []) ⟫
  ⟹*⟨ executeStep executeRET ⟩
    execute HALT ⟪ [] ∥ NATURAL 10 ∷ [] ⟫
  ⟹*∎
\end{code}
