module Semantics.NFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Semantics.Grammar public

private
  variable ℓ ℓ' : Level

module NFADefs ℓ (Σ₀ : hSet ℓ) where
  open GrammarDefs ℓ Σ₀ public

  record NFA : Type (ℓ-suc ℓ) where
    constructor mkNFA
    field
      Q : FinSet ℓ
      init : Q .fst
      isAcc : Q .fst → DecProp ℓ
      transition : FinSet ℓ
      src : transition .fst → Q .fst
      dst : transition .fst → Q .fst
      label : transition .fst → Σ₀ .fst
      ε-transition : FinSet ℓ
      ε-src : ε-transition .fst → Q .fst
      ε-dst : ε-transition .fst → Q .fst

    decEqQ : Discrete (Q .fst)
    decEqQ = isFinSet→Discrete (Q .snd)

  open NFA

  data NFATrace (N : NFA) : (state : N .Q .fst) → (w : String) → Type ℓ where
    nil : ∀ {q} → N .isAcc q .fst .fst → NFATrace N q []
    cons :
      ∀ {w'} →
      {t : N .transition .fst} →
      NFATrace N (N .dst t) w' →
      NFATrace N (N .src t) (N .label t ∷ w')
    ε-cons :
      ∀ {w'} →
      {t : N .ε-transition .fst} →
      NFATrace N (N .ε-dst t) w' →
      NFATrace N (N .ε-src t) w'

  module isSetNFATraceProof
    (N : NFA)
    where
    NFATrace-X = N .Q .fst × String
    NFATrace-S : NFATrace-X → Type ℓ
    NFATrace-S (s , w) =
      (N .isAcc s .fst .fst × (w ≡ [])) ⊎ (
      Σ (fiber (N .src) s) (λ t → fiber (λ w' → (N .label (t .fst)) ∷ w') w)  ⊎
      fiber (N .ε-src) s)

    NFATrace-P : ∀ x → NFATrace-S x → Type
    NFATrace-P (state , word) (inl S) = ⊥
    NFATrace-P (state , word) (inr (inl (x , y))) = ⊤
    NFATrace-P (state , word) (inr (inr S)) = ⊤

    NFATrace-inX : ∀ x (s : NFATrace-S x) → NFATrace-P x s → NFATrace-X
    NFATrace-inX x (fsuc (inl (t , fibt))) _ = (N .dst (t .fst)) , (fibt .fst)
    NFATrace-inX x (fsuc (fsuc t)) _ = (N .ε-dst (t .fst)) , (x .snd)

    NFATrace→W :
      ∀ {s : N .Q .fst} {w : String} →
      NFATrace N s w → IW NFATrace-S NFATrace-P NFATrace-inX ((s , w))
    NFATrace→W (nil x) =
      node (inl (x , refl)) (λ ())
    NFATrace→W {s}{w} (cons {w'}{t} x) =
      node (inr (inl ((t , refl) , w' , refl)))
        (λ _ → NFATrace→W x)
    NFATrace→W {s}{w} (ε-cons {w'}{t} x) =
      node (inr (inr (t , refl)))
        (λ _ → NFATrace→W x)

    IWNFA = IW NFATrace-S NFATrace-P NFATrace-inX

    W→NFATrace :
      ∀ {s : N .Q .fst} {w : String} →
      IW NFATrace-S NFATrace-P NFATrace-inX ((s , w)) → NFATrace N s w
    W→NFATrace (node (inl x) subtree) =
      transport
        (sym (cong₂ (λ a b → NFATrace N a b)
          refl (x .snd)))
        (NFATrace.nil {N = N} (x .fst))
    W→NFATrace (node (fsuc (inl x)) subtree) =
      transport
        (cong₂ (λ a b → NFATrace N a b)
          (x .fst .snd) (x .snd .snd))
        (NFATrace.cons {N = N} (W→NFATrace (subtree _)))
    W→NFATrace {s}{w} (node (fsuc (fsuc x)) subtree) =
      transport
        (cong (λ a → NFATrace N a w) (x .snd))
        (NFATrace.ε-cons {N = N} (W→NFATrace (subtree _)))

    NFATraceRetractofW : ∀ {s}{w} (tr : NFATrace N s w) →
      W→NFATrace (NFATrace→W tr) ≡ tr
    NFATraceRetractofW (nil x) = transportRefl (nil x)
    NFATraceRetractofW (cons tr) =
      transportRefl (cons (W→NFATrace (NFATrace→W tr))) ∙
      cong (λ a → cons a) (NFATraceRetractofW tr)
    NFATraceRetractofW (ε-cons tr) =
      transportRefl (ε-cons (W→NFATrace (NFATrace→W tr))) ∙
      cong (λ a → ε-cons a) (NFATraceRetractofW tr)

    isSetNFATrace-S : ∀ s w → isSet (NFATrace-S (s , w))
    isSetNFATrace-S s w =
      isSet⊎
        (isSet×
          (isProp→isSet (N .isAcc s .fst .snd))
          (isGroupoidString _ _)
          )
        (isSet⊎
          (isSetΣ
            (isSetΣ (isFinSet→isSet (N .transition .snd))
            (λ t → isSet→isGroupoid (isFinSet→isSet (N .Q .snd)) _ _))
            λ fib → isSetΣ isSetString
              (λ w' → isGroupoidString _ _))
          (isSetΣ (isFinSet→isSet (N .ε-transition .snd))
            (λ t → isSet→isGroupoid
              (isFinSet→isSet (N .Q .snd)) _ _)))

    isSetNFATrace :
      (state : N .Q .fst) →
      (w : String) → isSet (NFATrace N state w)
    isSetNFATrace s w =
      isSetRetract
        NFATrace→W
        W→NFATrace
        NFATraceRetractofW
        (isOfHLevelSuc-IW 1
          (λ x → isSetNFATrace-S (x .fst) (x .snd))
          ((s , w)))

  open isSetNFATraceProof
  NFAGrammar : (N : NFA) → Grammar
  NFAGrammar N w = (NFATrace N (N .init) w) , isSetNFATrace N (N .init) w

  literalNFA : (c : Σ₀ .fst) → NFA
  fst (Q (literalNFA c)) = Lift (Fin 2)
  snd (Q (literalNFA c)) = isFinSetLift isFinSetFin
  init (literalNFA c) = lift fzero
  isAcc (literalNFA c) x =
    ((x ≡ lift (fsuc fzero)) , isSetLift isSetFin _ _) ,
    discreteLift discreteFin x (lift (fsuc fzero))
  transition (literalNFA c) = (Lift Unit) , (isFinSetLift isFinSetUnit)
  src (literalNFA c) (lift _) = literalNFA c .init
  dst (literalNFA c) (lift _) = lift (fsuc fzero)
  label (literalNFA c) (lift _) = c
  fst (ε-transition (literalNFA c)) = Lift ⊥
  snd (ε-transition (literalNFA c)) = isFinSetLift isFinSetFin
  ε-src (literalNFA c) (lift x) = ⊥.rec x
  ε-dst (literalNFA c) (lift x )= ⊥.rec x

  emptyNFA : NFA
  Q emptyNFA = Lift (Fin 2) , isFinSetLift isFinSetFin
  init emptyNFA = lift fzero
  isAcc emptyNFA x =
    ((x ≡ lift (fsuc fzero)) , isSetLift isSetFin _ _) ,
    discreteLift discreteFin x (lift (fsuc fzero))
  transition emptyNFA = Lift ⊥ , isFinSetLift isFinSetFin
  src emptyNFA (lift x) = ⊥.rec x
  dst emptyNFA (lift x) = ⊥.rec x
  label emptyNFA (lift x) = ⊥.rec x
  ε-transition emptyNFA = Lift Unit , isFinSetLift isFinSetUnit
  ε-src emptyNFA _ = emptyNFA .init
  ε-dst emptyNFA _ = lift (fsuc fzero)

  emptyIW→w≡[] : ∀ {q}{w} →
    IW (NFATrace-S emptyNFA) (NFATrace-P emptyNFA)
    (NFATrace-inX emptyNFA) (q , w) → w ≡ []
  emptyIW→w≡[] (node (inl x) subtree) = x .snd
  emptyIW→w≡[] (node (inr (inr x)) subtree) =
    emptyIW→w≡[] (subtree _)

  module _ (c : Σ₀ .fst) where
    NFAc = literalNFA c

    -- TODO try with RepIW trees
    literalIW→w≡[c] : ∀ {q}{w} →
      IW (NFATrace-S NFAc) (NFATrace-P NFAc)
      (NFATrace-inX NFAc) (q , w) → (w ≡ []) ⊎ (w ≡ [ c ])
    literalIW→w≡[c] (node (inl x) subtree) = inl (x .snd)
    literalIW→w≡[c] (node (inr (inl x)) subtree) = {!!}
      -- inr (
        -- Cubical.Data.Sum.elim
          -- (λ mt → sym (x .snd .snd) ∙ cong (λ a → c ∷ a) mt)
          -- (λ cp → {!!})
          -- (literalIW→w≡[c] (subtree _)))

    literalCanonical : ∀ {w} → NFATrace NFAc (NFAc .init) w → Σ Grammar (λ g → g w .fst)
    literalCanonical p = {!!}
      where
      canonical : literalCanonical p .fst ≡ {!ILin!}
      canonical = refl

  -- NFA Combinators
  module _
    (N : NFA)
    where

    module _
      (N' : NFA)
      where

      ⊕NFA : NFA
      -- States stratified into init, N states, N' states
      Q ⊕NFA .fst = ⊤ ⊎ (N .Q .fst ⊎ N' .Q .fst)
      Q ⊕NFA .snd =
        isFinSet⊎
          (_ , isFinSetUnit)
          (_ , (isFinSet⊎ (N .Q) (N' .Q)))
      -- initial state
      init ⊕NFA = inl _
      -- Acceptance at subautomata accepting states
      isAcc ⊕NFA x =
        -- LOL this is way too complicated
        -- could've just pattern matched on x
        DecProp⊎
          (DecPropΣ
            (((fiber (inr ∘ inl) x) , inr∘inl-prop-fibs) ,
              decRec
                (Cubical.HITs.PropositionalTruncation.elim
                    (λ _ → isPropDec inr∘inl-prop-fibs)
                    (λ y → yes y))
                (λ ∄preimage →
                  no λ y → ∄preimage ∣ y ∣₁
                )
                (DecPropIso .Iso.inv
                  (_ , isDecProp∃ (N .Q)
                    (λ y → (inr (inl y) ≡ x) ,
                      isDecProp≡ (⊕NFA .Q) (inr (inl y)) x) ) .snd))
            (N .isAcc ∘ fst))
          (DecPropΣ
            ((fiber (inr ∘ inr) x , inr∘inr-prop-fibs) ,
              decRec
                (Cubical.HITs.PropositionalTruncation.elim
                  (λ _ → isPropDec inr∘inr-prop-fibs)
                  λ y → yes y)
                (λ ∄preimage → no λ y → ∄preimage ∣ y ∣₁)
                (DecPropIso .Iso.inv
                  ((_ , isDecProp∃ (N' .Q) λ y → (inr (inr  y) ≡ x) ,
                    (isDecProp≡ (⊕NFA .Q) (inr (inr y)) x))) .snd))
            (N' .isAcc ∘ fst))
          mutex
          where
          inr∘inl-prop-fibs =
            isEmbedding→hasPropFibers
              (compEmbedding (_ , isEmbedding-inr)
                             (_ , isEmbedding-inl) .snd) x

          inr∘inr-prop-fibs =
            isEmbedding→hasPropFibers
              (compEmbedding
                (_ , isEmbedding-inr)
                (_ , isEmbedding-inr) .snd) x

          mutex =
            (λ (q , _) (q' , _) →
              lower (⊎Path.encode _ _
                (isEmbedding→Inj isEmbedding-inr _ _
                  (q .snd ∙ (sym (q' .snd))))))
      transition ⊕NFA .fst =
        N .transition .fst ⊎ N' .transition .fst
      transition ⊕NFA .snd =
        isFinSet⊎ (N .transition) (N' .transition)
      -- the labeled transitions have same src, dst, and label as
      -- in original automata
      src ⊕NFA (inl x) = inr (inl (N .src x))
      src ⊕NFA (inr x) = inr (inr (N' .src x))
      dst ⊕NFA (inl x) = inr (inl (N .dst x))
      dst ⊕NFA (inr x) = inr (inr (N' .dst x))
      label ⊕NFA (inl x) = N .label x
      label ⊕NFA (inr x) = N' .label x
      fst (ε-transition ⊕NFA) =
        Fin 2 ⊎
        (N .ε-transition .fst ⊎ N' .ε-transition .fst)
      snd (ε-transition ⊕NFA) =
        isFinSet⊎
          (_ , isFinSetFin)
          (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))
      -- ε-transitions to subautomata initial states
      ε-src ⊕NFA (inl fzero) = ⊕NFA .init
      ε-dst ⊕NFA (inl fzero) = inr (inl (N .init))
      ε-src ⊕NFA (inl (inr fzero)) = ⊕NFA .init
      ε-dst ⊕NFA (inl (inr fzero)) = inr (inr (N' .init))
      -- internal ε-transitions from subautomata
      ε-src ⊕NFA (inr (inl x)) = inr (inl (N .ε-src x))
      ε-dst ⊕NFA (inr (inl x)) = inr (inl (N .ε-dst x))
      ε-src ⊕NFA (inr (inr x)) = inr (inr (N' .ε-src x))
      ε-dst ⊕NFA (inr (inr x)) = inr (inr (N' .ε-dst x))

      ⊗NFA : NFA
      Q ⊗NFA .fst = N .Q .fst ⊎ N' .Q .fst
      Q ⊗NFA .snd = isFinSet⊎ (N .Q) (N' .Q)
      init ⊗NFA = inl (N .init)
      isAcc ⊗NFA (inl x) =
        DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
      isAcc ⊗NFA (inr x) = N' .isAcc x
      transition ⊗NFA .fst = N .transition .fst ⊎ N' .transition .fst
      transition ⊗NFA .snd = isFinSet⊎ (N .transition) (N' .transition)
      src ⊗NFA (inl x) = inl (N .src x)
      dst ⊗NFA (inl x) = inl (N .dst x)
      src ⊗NFA (inr x) = inr (N' .src x)
      dst ⊗NFA (inr x) = inr (N' .dst x)
      label ⊗NFA (inl x) = N .label x
      label ⊗NFA (inr x) = N' .label x
      ε-transition ⊗NFA .fst =
        (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
        (N .ε-transition .fst ⊎ N' .ε-transition .fst)
      ε-transition ⊗NFA .snd =
        isFinSet⊎
          (_ , isFinSetΣ (N .Q)
            λ x → _ ,
              isDecProp→isFinSet
                (N .isAcc x .fst .snd)
                (N .isAcc x .snd))
          ((_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
      ε-src ⊗NFA (inl x) = inl (x .fst)
      ε-dst ⊗NFA (inl x) = inr (N' .init)
      ε-src ⊗NFA (inr (inl x)) = inl (N .ε-src x)
      ε-dst ⊗NFA (inr (inl x)) = inl (N .ε-dst x)
      ε-src ⊗NFA (inr (inr x)) = inr (N' .ε-src x)
      ε-dst ⊗NFA (inr (inr x)) = inr (N' .ε-dst x)

    KL*NFA : NFA
    Q KL*NFA .fst = N .Q .fst ⊎ ⊤
    Q KL*NFA .snd = isFinSet⊎ (N .Q) (_ , isFinSetUnit)
    init KL*NFA = inl (N .init)
    isAcc KL*NFA (inl x) =
      DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
    isAcc KL*NFA (inr x) =
      DecPropIso .Iso.inv (Unit* , (true , (invEquiv LiftEquiv)))
    transition KL*NFA = N .transition
    src KL*NFA x = inl (N .src x)
    dst KL*NFA x = inl (N .dst x)
    label KL*NFA = N .label
    ε-transition KL*NFA .fst =
      ⊤ ⊎
      ((Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
        (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst))
    ε-transition KL*NFA .snd =
      isFinSet⊎
        (_ , isFinSetUnit)
        (_ , isFinSet⊎
          (_ , isFinSetAccΣ)
          (_ , isFinSetAccΣ))
      where
      isFinSetAccΣ :
        isFinSet
          (Σ-syntax (N .Q .fst) (λ q → N .isAcc q .fst .fst))
      isFinSetAccΣ =
        isFinSetΣ (N .Q)
          (λ x → _ ,
            isDecProp→isFinSet
              (N .isAcc x .fst .snd)
              (N .isAcc x .snd))
    ε-src KL*NFA (inl x) = inl (N .init)
    ε-dst KL*NFA (inl x) = inr _
    ε-src KL*NFA (inr (inl x)) = inl (x .fst)
    ε-dst KL*NFA (inr (inl x)) = inl (N .init)
    ε-src KL*NFA (inr (inr x)) = inl (x .fst)
    ε-dst KL*NFA (inr (inr x)) = inr _

  NFAfromRegularGrammar : RegularGrammar → NFA
  NFAfromRegularGrammar ILinReg = emptyNFA
  NFAfromRegularGrammar (g ⊗Reg h) =
    ⊗NFA (NFAfromRegularGrammar g) (NFAfromRegularGrammar h)
  NFAfromRegularGrammar (literalReg c) = literalNFA c
  NFAfromRegularGrammar (g ⊕Reg h) =
    ⊕NFA (NFAfromRegularGrammar g) (NFAfromRegularGrammar h)
  NFAfromRegularGrammar (KL*Reg g) = KL*NFA (NFAfromRegularGrammar g)

  NFA→Reg : (g : RegularGrammar) →
    ParseTransformer
      (NFAGrammar (NFAfromRegularGrammar g))
      (RegularGrammar→Grammar g)
  NFA→Reg GrammarDefs.ILinReg x = {!!}
  NFA→Reg (g GrammarDefs.⊗Reg g₁) x = {!!}
  NFA→Reg (GrammarDefs.literalReg x₁) x = {!!}
  NFA→Reg (g GrammarDefs.⊕Reg g₁) x = {!!}
  NFA→Reg (GrammarDefs.KL*Reg g) x = {!!}

  module _ (a b : Σ₀ .fst) where
    g : RegularGrammar
    g = literalReg a ⊗Reg literalReg b

    N = NFAfromRegularGrammar (KL*Reg g)

    -- Parsing larger strings is borderline unusable,
    -- even though technically possible,
    -- because you need to manually give the transition parameter
    w : String
    w = []

    p : NFAGrammar N w .fst
    p = ε-cons {t = inl tt} (nil tt*)
