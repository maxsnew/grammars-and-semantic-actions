
{-# OPTIONS #-}
module Semantics.DFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
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
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.CommMonoid.Instances.FreeComMonoid

open import Cubical.Tactics.Reflection
open import Semantics.Grammar

private
  variable ℓ ℓ' : Level

negateDecProp : ∀ {ℓ} → DecProp ℓ → DecProp ℓ
negateDecProp ((A , isPropA) , yes p) =
  ((¬ A) , isProp→ isProp⊥) , no (λ x → x p)
negateDecProp ((A , isPropA) , no ¬p) =
  ((¬ A) , isProp→ isProp⊥) , yes ¬p


negateCompute : ∀ {ℓ} {A : DecProp ℓ} →
  ¬ A .fst .fst → (negateDecProp A) .fst .fst
negateCompute {ℓ} {A} x =
  decRec
    (λ a → a)
    (λ ¬a → {!Stable¬!})
    (negateDecProp A .snd)

module DFADefs ℓ (Σ₀ : hSet ℓ) where
  open GrammarDefs ℓ Σ₀ public

  record DFA : Type (ℓ-suc ℓ) where
    constructor mkDFA
    field
      Q : FinSet ℓ
      init : Q .fst
      isAcc : Q .fst → DecProp ℓ
      δ : Q .fst → Σ₀ .fst → Q .fst

  open DFA

  negate : (D : DFA) → DFA
  Q (negate D) = D .Q
  init (negate D) = D .init
  isAcc (negate D) q = negateDecProp (D .isAcc q)
  δ (negate D) = D .δ

  negateInvol : (D : DFA) → D ≡ negate (negate D)
  negateInvol D = {!refl!}

  data DFATrace (D : DFA) : D .Q .fst → String → Type ℓ where
    nil : ∀ {q} → D .isAcc q .fst .fst → DFATrace D q []
    cons :
      ∀ {w'} {c} →
      {q : D .Q .fst} →
      DFATrace D (D .δ q c) w' →
      DFATrace D q (c ∷ w')


  module isSetDFATraceProof (D : DFA) where
    DFATrace-X = D .Q .fst × String

    DFATrace-S : DFATrace-X → Type ℓ
    DFATrace-S (q , w) =
      ((D .isAcc q .fst .fst) × (w ≡ [])) ⊎
      (Σ[ c ∈ Σ₀ .fst ] fiber (λ w' → c ∷ w') w)

    DFATrace-P : ∀ x → DFATrace-S x → Type
    DFATrace-P (q , w) (inl x) = ⊥
    DFATrace-P (q , w) (inr x) = ⊤

    DFATrace-inX : ∀ x (s : DFATrace-S x) → DFATrace-P x s → DFATrace-X
    DFATrace-inX (q , w) (inr (c , fibw')) _ = D .δ q c , fibw' .fst

    DFATrace→W : ∀ {q : D .Q .fst} {w : String} →
      DFATrace D q w → IW DFATrace-S DFATrace-P DFATrace-inX ((q , w))
    DFATrace→W (nil qIsAcc) = node (inl (qIsAcc , refl)) (λ ())
    DFATrace→W (cons {w' = w'} {c = c} x) =
      node (inr (c , w' , refl)) λ _ → DFATrace→W x

    W→DFATrace : ∀ {q : D .Q .fst} {w : String} →
      IW DFATrace-S DFATrace-P DFATrace-inX ((q , w)) → DFATrace D q w
    W→DFATrace (node (inl (qIsAcc , w≡[])) subtree) =
      transport (sym (cong (λ a → DFATrace D _ a) w≡[])) (DFATrace.nil qIsAcc)
    W→DFATrace (node (fsuc (c , fibw)) subtree) =
      transport (cong (λ a → DFATrace D _ a) (fibw .snd))
        (DFATrace.cons {D = D} {w' = fibw .fst} {q = _}
          (W→DFATrace (subtree _)))

    DFATraceRetractofW : ∀ {q }{w} (tr : DFATrace D q w) →
      W→DFATrace (DFATrace→W tr) ≡ tr
    DFATraceRetractofW (nil x) = transportRefl (nil x)
    DFATraceRetractofW (cons tr) =
      transportRefl (cons (W→DFATrace (DFATrace→W tr))) ∙
      cong (λ a → cons a) (DFATraceRetractofW tr)

    isSetDFATrace-S : ∀ q w → isSet (DFATrace-S (q , w))
    isSetDFATrace-S q w =
      isSet⊎
        (isSet× (isProp→isSet (D .isAcc q .fst .snd)) (isGroupoidString _ _))
        (isSetΣ (Σ₀ .snd)
          (λ c → isSetΣ isSetString (λ w' → isGroupoidString _ _)))

    isSetDFATrace : ∀ q w → isSet (DFATrace D q w)
    isSetDFATrace q w =
      isSetRetract DFATrace→W W→DFATrace DFATraceRetractofW
        (isOfHLevelSuc-IW 1 (λ _ → isSetDFATrace-S _ _) ((q , w)))

  open isSetDFATraceProof
  DFAGrammar : (D : DFA) → Grammar
  DFAGrammar D w = DFATrace D (D .init) w , isSetDFATrace D _ _

  module _ (D : DFA) where
    getAcceptingState :
      (w : String) →
      (q : D .Q .fst) →
      DFATrace D q w →
      Σ[ q' ∈ D .Q .fst ] (D .isAcc q' .fst .fst)
    getAcceptingState .[] q (nil x) = q , x
    getAcceptingState .(_ ∷ _) q (cons p) = getAcceptingState _ (D .δ q _) p

    extendTraceByLiteral :
      (c : Σ₀ .fst) →
      (q : D .Q .fst) →
      (w : String) →
      (tr : DFATrace D q w) →
      D .isAcc (D .δ (getAcceptingState w q tr .fst) c) .fst .fst →
      Σ[ t ∈ DFATrace D q (w ++ [ c ]) ]
          D .δ (getAcceptingState w q tr .fst) c ≡ getAcceptingState (w ++ [ c ]) q t .fst
    extendTraceByLiteral c q .[] (nil x) δcisAcc = (cons (nil δcisAcc)) , refl
    extendTraceByLiteral c q .(_ ∷ _) (cons {c = c'} tr) δcisAcc =
      cons (the-rec-call .fst) ,
      the-rec-call .snd
      where
      the-rec-call = extendTraceByLiteral c (D .δ q c') _ tr δcisAcc


  module _ (D : DFA) where
    extendTraceByLiteralIntoNegation :
      (c : Σ₀ .fst) →
      (q : D .Q .fst) →
      (w : String) →
      (tr : DFATrace D q w) →
      (negate D) .isAcc ((negate D) .δ (getAcceptingState D w q tr .fst) c) .fst .fst →
      Σ[ t ∈ DFATrace (negate D) q (w ++ [ c ]) ]
          (negate D) .δ (getAcceptingState D w q tr .fst) c ≡
            getAcceptingState (negate D) (w ++ [ c ]) q t .fst
    extendTraceByLiteralIntoNegation c q .[] (nil x₁) δcnotAcc = (cons (nil δcnotAcc)) , refl
    extendTraceByLiteralIntoNegation c q .(_ ∷ _) (cons tr) δcnotAcc =
      (cons (the-rec-call .fst)) ,
      the-rec-call .snd
      where
      the-rec-call = extendTraceByLiteralIntoNegation c (negate D .δ q _) _ tr δcnotAcc

  module _
    (D : DFA)
    (decEqQ : Discrete (D .Q .fst))
    (isFinSetΣ₀ : isFinSet (Σ₀ .fst))
    where

    open Iso


    ⊕Σ₀ : Grammar
    ⊕Σ₀ w =
      (Σ[ c ∈ Σ₀ .fst ] literal c w .fst) ,
      isSetΣ (Σ₀ .snd) (λ c → literal c w .snd)

    decEqΣ₀ : Discrete (Σ₀ .fst)
    decEqΣ₀ = isFinSet→Discrete isFinSetΣ₀

    run :
      ParseTransformer
        (KL* ⊕Σ₀)
        (DFAGrammar D ⊕ DFAGrammar (negate D))
    run p =
      fold*l
        ⊕Σ₀
        (DFAGrammar D ⊕ DFAGrammar (negate D))
        mt-case
        cons-case
        p
      where
      mt-case : ParseTransformer
        ILin (DFAGrammar D ⊕ DFAGrammar (negate D))
      mt-case w≡[] =
        decRec
          (λ initIsAcc →
            inl (
              transport
                (cong (λ a → DFATrace D (D .init) a) (sym w≡[]))
                (DFATrace.nil {D = D} initIsAcc)))
          (λ initIsAcc→⊥ →
            inr
              (
              transport
                (cong (λ a → DFATrace (negate D) ((negate D) .init) a) (sym w≡[]))
                (DFATrace.nil {D = negate D} {!!})
              )
          )
          (D .isAcc (D .init) .snd)

      cons-case : ParseTransformer
        ((DFAGrammar D ⊕ DFAGrammar (negate D)) ⊗ ⊕Σ₀)
        (DFAGrammar D ⊕ DFAGrammar (negate D))
      cons-case {w} (((w' , w'') , w≡w'++w'') , inl p , c , w''≡c) =
        decRec
          (λ nextIsAcc →
            inl (
              transport
                (cong (λ b → DFATrace D (D .init) b) (cong (λ a → w' ++ a) w''≡c ∙ sym w≡w'++w''))
                (extendTraceByLiteral D c (D .init) w' p nextIsAcc .fst)
            )
          )
          (λ nextIsAcc→⊥ →
            inr (
                transport
                  (cong (λ b → DFATrace (negate D) ((negate D) .init) b) (cong (λ a → w' ++ a) w''≡c ∙ sym w≡w'++w''))
                  (extendTraceByLiteralIntoNegation D c (D .init) w' p {!nextIsAcc→⊥!} .fst)
            )
          )
          (D .isAcc (D .δ (getAcceptingState D w' (D .init) p .fst) c) .snd)
      cons-case {w} (((w' , w'') , w≡w'++w'') , inr p , c , w''≡c) =
        decRec
          (λ nextAccByNeg →
            inr
              (transport
                (cong (λ b → DFATrace (negate D) (D .init) b) (cong (λ a → w' ++ a) w''≡c ∙ sym w≡w'++w''))
                (extendTraceByLiteral (negate D) c (D .init) w' p nextAccByNeg .fst)
                )
          )
          (λ nextAccByNeg→⊥ →
            inl
              (transport
                (cong₂ (λ a b → DFATrace a ({!negate D!} .init) b) (sym (negateInvol D)) (cong (λ a → w' ++ a) w''≡c ∙ sym w≡w'++w''))
                (extendTraceByLiteralIntoNegation (negate D) c (D .init) w' p {!!} .fst)
                )
          )
          ((negate D) .isAcc (D .δ (getAcceptingState (negate D) w' (D .init) p .fst) c) .snd)

module examples where
  data zero-one : Type ℓ-zero where
    zero : zero-one
    one : zero-one

  isSet-zero-one : isSet zero-one
  isSet-zero-one = {!!}

  zero-one-hSet : hSet ℓ-zero
  zero-one-hSet = zero-one , isSet-zero-one

  open DFADefs ℓ-zero zero-one-hSet public
  open DFADefs.DFA

  D : DFA
  Q D = (Fin 3) , isFinSetFin
  init D = inl _
  isAcc D = λ x → ((x ≡ fzero) , isSetFin x fzero) , discreteFin x fzero
  δ D fzero zero = fromℕ 0
  δ D fzero one = fromℕ 1
  δ D (fsuc fzero) zero = fromℕ 2
  δ D (fsuc fzero) one = fromℕ 0
  δ D (fsuc (fsuc fzero)) zero = fromℕ 1
  δ D (fsuc (fsuc fzero)) one = fromℕ 2

  w = one ∷ zero ∷ zero ∷ one ∷ []

  p : DFAGrammar D w .fst
  p = DFADefs.cons (DFADefs.cons (DFADefs.cons (DFADefs.cons (DFADefs.nil refl))))

  qAcc : Σ (D .Q .fst) (λ q' → D .isAcc q' .fst .fst)
  qAcc = getAcceptingState D w (D .init) p

  _ : qAcc ≡ (fzero , refl)
  _ = refl
