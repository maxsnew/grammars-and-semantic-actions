module Semantics.PDA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.SumFin

open import Semantics.Grammar
open import Semantics.NFA

private
  variable ℓ ℓ' : Level

module PDADefs ℓ ℓ' (Σ₀ : hSet ℓ) (Γ₀ : hSet ℓ') where
  open NFADefs ℓ Σ₀ public

  Stack = List (Γ₀ .fst)

  record PDA : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    constructor mkPDA
    field
      Q : FinSet ℓ
      init : Q .fst
      isAcc : Q .fst → DecProp ℓ
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
    (state : P .Q .fst) →
    (w : String) → (l : Stack) →
    Type (ℓ-max ℓ ℓ') where
    nil : ∀ {l}{q} → P .isAcc q .fst .fst →
      PDATrace P q [] l
    cons :
      ∀ {w'}{l} → {t : P .transition .fst} →
      PDATrace P (P .dst t) w' (rev(P .push t) ++ l) →
      PDATrace P (P .src t) (P .label t ∷ w') (P .pop t ∷ l)
    ε-cons :
      ∀ {w'}{l} → {t : P .ε-transition .fst} →
      PDATrace P (P .ε-dst t) w' (P .ε-push t ++ l) →
      PDATrace P (P .ε-src t) w' (P .ε-pop t ∷ l)

module _ where
  open PDADefs ℓ-zero ℓ-zero (Fin 2 , isSetFin) (Fin 2 , isSetFin)
  open PDADefs.PDA

  0ⁿ1ⁿ : PDA
  Q 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
  init 0ⁿ1ⁿ = lift (inl _)
  isAcc 0ⁿ1ⁿ x =
    ((x ≡ lift (fsuc (fsuc fzero))) , isSetLift isSetFin _ _) ,
    discreteLift discreteFin x (lift (fsuc (fsuc fzero)))
  init-stack-sym 0ⁿ1ⁿ = fzero
  transition 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
  src 0ⁿ1ⁿ (lift fzero) = lift (fzero)
  dst 0ⁿ1ⁿ (lift fzero) = lift (fzero)
  pop 0ⁿ1ⁿ (lift fzero) = fzero
  push 0ⁿ1ⁿ (lift fzero) = fzero ∷ [ fsuc fzero ]
  label 0ⁿ1ⁿ (lift fzero) = fzero
  src 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (fzero)
  dst 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (fzero)
  pop 0ⁿ1ⁿ (lift (fsuc fzero)) = fsuc fzero
  push 0ⁿ1ⁿ (lift (fsuc fzero)) = fsuc fzero ∷ [ fsuc fzero ]
  label 0ⁿ1ⁿ (lift (fsuc fzero)) = fzero
  src 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = lift (fsuc fzero)
  dst 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = lift (fsuc fzero)
  pop 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = fsuc fzero
  push 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = []
  label 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = fsuc fzero
  ε-transition 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
  ε-src 0ⁿ1ⁿ (lift fzero) = lift (fzero)
  ε-dst 0ⁿ1ⁿ (lift fzero) = lift (fsuc fzero)
  ε-pop 0ⁿ1ⁿ (lift fzero) = (fsuc fzero)
  ε-push 0ⁿ1ⁿ (lift fzero) = [ (fsuc fzero) ]
  ε-src 0ⁿ1ⁿ (lift (fsuc fzero)) = lift fzero
  ε-dst 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (fsuc fzero)
  ε-pop 0ⁿ1ⁿ (lift (fsuc fzero)) = fzero
  ε-push 0ⁿ1ⁿ (lift (fsuc fzero)) = [ fzero ]
  ε-src 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = lift (fsuc fzero)
  ε-dst 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = lift (fsuc (fsuc fzero))
  ε-pop 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = fzero
  ε-push 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = [ fzero ]

  0ⁿ1ⁿParse : (w : String) → Type ℓ-zero
  0ⁿ1ⁿParse w =
    PDATrace 0ⁿ1ⁿ (0ⁿ1ⁿ .init) w [ 0ⁿ1ⁿ .init-stack-sym ]

  mt : 0ⁿ1ⁿParse []
  mt =
    ε-cons {t = lift (fsuc fzero)}
      (ε-cons {t = lift (fsuc (fsuc fzero))} (nil refl))

  zeroone : 0ⁿ1ⁿParse (fzero ∷ [ fsuc fzero ])
  zeroone =
    cons {t = lift fzero}(
      ε-cons {t = lift fzero}(
        cons {t = lift (fsuc (fsuc fzero))}(
          ε-cons {t = lift (fsuc (fsuc fzero))} (nil refl))))

  zero⁴one⁴ :
    0ⁿ1ⁿParse (
      fzero ∷ fzero ∷ fzero ∷ fzero ∷
      (fsuc fzero) ∷ (fsuc fzero) ∷ (fsuc fzero) ∷ [ fsuc fzero ])
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
                      (ε-cons {t = lift (fsuc (fsuc fzero))} (nil refl))))))))))
