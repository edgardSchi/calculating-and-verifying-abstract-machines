--------------------------------------------------------------------------------
-
- Example terms of the language
-
--------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --safe #-}
module AbstractMachines.Language.Examples where

open import AbstractMachines.Language.Types
open import AbstractMachines.Language.Reduction
open import AbstractMachines.Language.Normalization
\end{code}

--------------------------------------------------------------------------------

Definining the negation function
<Negation>
\begin{code}
! : (∅ ⊢ Bool ⇒ Bool)
! = ƛ (if (# 0) then false else true)
\end{code}

\begin{code}
test = ! · true
\end{code}
