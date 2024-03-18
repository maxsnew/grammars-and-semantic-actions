{-# OPTIONS #-}
module Semantics.PDA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Maybe
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Empty.Base
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
-- open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

open import Semantics.Grammar
open import Semantics.NFA

private
  variable ℓ ℓ' : Level

module PDADefs ℓ ℓ' (Σ₀ : hSet ℓ) (Γ₀ : hSet ℓ') where
  open NFADefs ℓ Σ₀ public

  Stack = List (Γ₀ .fst)

  record PDA : Type {!!} where
    constructor mkPDA
    field
      Q : FinSet ℓ
      init : Q .fst
      acc : Q .fst
      init-stack-sym : Γ₀ .fst
      transition : FinSet ℓ
      src : transition .fst → Q .fst
      dst : transition .fst → Q .fst
      pop : transition .fst → Γ₀ .fst
      push : transition .fst → Stack
      label : transition .fst → Σ₀ .fst
      ε-transition : FinSet ℓ
      ε-src : ε-transition .fst → Q .fst
      ε-dst : ε-transition .fst → Q .fst
      ε-pop : ε-transition .fst → Γ₀ .fst
      ε-push : ε-transition .fst → Stack

  open PDA

  data PDATrace (P : PDA) :
    (state : P .Q .fst) → (w : String) → (l : Stack) → Type (ℓ-max ℓ ℓ') where
    nil : ∀ {l} → PDATrace P (P .acc) [] l
    cons :
      ∀ {w'}{l} → {t : P .transition .fst} →
      PDATrace P (P .dst t) w' (rev(P .push t) ++ l) →
      PDATrace P (P .src t) (P .label t ∷ w') (P .pop t ∷ l)
    ε-cons :
      ∀ {w'}{l} → {t : P .ε-transition .fst} →
      PDATrace P (P .ε-dst t) w' (P .ε-push t ++ l) →
      PDATrace P (P .ε-src t) w' (P .ε-pop t ∷ l)

module _ where
  data zo : Type ℓ-zero where
    zero : zo
    one : zo

  data AZ : Type ℓ-zero where
    a :  AZ
    z : AZ

  open PDADefs ℓ-zero ℓ-zero (zo , {!!}) (AZ , {!!})
  open PDADefs.PDA

  0ⁿ1ⁿ : PDA
  Q 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
  init 0ⁿ1ⁿ = lift (inl _)
  acc 0ⁿ1ⁿ = lift (inr (inr (inl _)))
  init-stack-sym 0ⁿ1ⁿ = z
  transition 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
  src 0ⁿ1ⁿ (lift fzero) = lift (inl _)
  dst 0ⁿ1ⁿ (lift fzero) = lift (inl _)
  pop 0ⁿ1ⁿ (lift fzero) = z
  push 0ⁿ1ⁿ (lift fzero) = z ∷ [ a ]
  label 0ⁿ1ⁿ (lift fzero) = zero
  src 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (inl _)
  dst 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (inl _)
  pop 0ⁿ1ⁿ (lift (fsuc fzero)) = a
  push 0ⁿ1ⁿ (lift (fsuc fzero)) = a ∷ [ a ]
  label 0ⁿ1ⁿ (lift (fsuc fzero)) = zero
  src 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = lift (inr (inl _))
  dst 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = lift (inr (inl _))
  pop 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = a
  push 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = []
  label 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = one
  ε-transition 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
  ε-src 0ⁿ1ⁿ (lift fzero) = lift (inl _)
  ε-dst 0ⁿ1ⁿ (lift fzero) = lift (inr (inl _))
  ε-pop 0ⁿ1ⁿ (lift fzero) = a
  ε-push 0ⁿ1ⁿ (lift fzero) = [ a ]
  ε-src 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (inl _)
  ε-dst 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (inr (inl _))
  ε-pop 0ⁿ1ⁿ (lift (fsuc fzero)) = z
  ε-push 0ⁿ1ⁿ (lift (fsuc fzero)) = [ z ]
  ε-src 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = lift (inr (inl _))
  ε-dst 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = lift ((inr (inr (inl _))))
  ε-pop 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = z
  ε-push 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = [ z ]

  0ⁿ1ⁿParse : (w : String) → Type ℓ-zero
  0ⁿ1ⁿParse w = PDATrace 0ⁿ1ⁿ (0ⁿ1ⁿ .init) w [ 0ⁿ1ⁿ .init-stack-sym ]


  mt : 0ⁿ1ⁿParse []
  mt =
    ε-cons {t = lift (fsuc fzero)}
      (ε-cons {t = lift (fsuc (fsuc fzero))} nil)

  zeroone : 0ⁿ1ⁿParse (zero ∷ [ one ])
  zeroone =
    cons {t = lift fzero}(
      ε-cons {t = lift fzero}(
        cons {t = lift (fsuc (fsuc fzero))}(
          ε-cons {t = lift (fsuc (fsuc fzero))} nil)))

  zero⁴one⁴ :  0ⁿ1ⁿParse (zero ∷ zero ∷ zero ∷ zero ∷ one ∷ one ∷ one ∷ [ one ])
  zero⁴one⁴ =
    cons {t = lift fzero}
      (cons {t = lift (fsuc fzero)}
        (cons {t = lift (fsuc fzero)}
          (cons {t = lift (fsuc fzero)}
            (ε-cons {t = lift fzero}
              (cons {t = lift (fsuc (fsuc fzero))}
                (cons {t = lift (fsuc (fsuc fzero))}
                  (cons {t = lift (fsuc (fsuc fzero))}
                    (cons {t = lift (fsuc (fsuc fzero))}
                      (ε-cons {t = lift (fsuc (fsuc fzero))} nil)))))))))
