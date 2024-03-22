{-# OPTIONS #-}
module Semantics.NFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum
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

DecProp⊎ :
  ∀ {ℓ} → (A : DecProp ℓ) → (B : DecProp ℓ) →
  (A .fst .fst → B .fst .fst → ⊥) → DecProp ℓ
fst (fst (DecProp⊎ A B AB→⊥)) = A .fst .fst ⊎ B .fst .fst
snd (fst (DecProp⊎ A B AB→⊥)) =
  isProp⊎ (A .fst .snd) (B .fst .snd) AB→⊥
snd (DecProp⊎ A B AB→⊥) =
  decRec
    (λ a → yes (inl a))
    (λ ¬a →
      decRec
        (λ b → yes (inr b))
        (λ ¬b → no (Cubical.Data.Sum.rec ¬a ¬b))
        (B .snd))
    (A .snd)

DecPropΣ :
  ∀ {ℓ} → (A : DecProp ℓ) → (B : A .fst .fst → DecProp ℓ) →
  DecProp ℓ
fst (fst (DecPropΣ A B)) = Σ[ a ∈ A .fst .fst ] B a .fst .fst
snd (fst (DecPropΣ A B)) = isPropΣ (A .fst .snd) (λ a → B a .fst .snd)
snd (DecPropΣ A B) =
  decRec
    (λ a →
    decRec
      (λ ba → yes (a , ba))
      (λ ¬ba →
        no (λ x →
          ¬ba (transport
            (cong (λ c → B c .fst .fst) (A .fst .snd _ _)) (x .snd) )))
      (B a .snd))
    (λ ¬a → no (λ x → ¬a (x .fst)))
    (A .snd)

DecProp∃ :
  ∀ {ℓ}{ℓ'} → (A : FinSet ℓ) → (B : A .fst → DecProp ℓ') →
  DecProp {!!}
fst (fst (DecProp∃ A B)) = ∥ (Σ[ a ∈ A .fst ] B a .fst .fst) ∥₁
snd (fst (DecProp∃ A B)) = isPropPropTrunc
snd (DecProp∃ A B) =
  decRec
    {!!}
    {!!}
    {!!}
-- TODO refactor everything to use alternate decprop fuckkkk

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

  -- NFA Combinators
  module _
    (N : NFA)
    (N' : NFA)
    where

    ⊕NFA : (N : NFA) → (N' : NFA) → NFA
    -- States stratified into init, N states, N' states, acc
    Q (⊕NFA N N') .fst = ⊤ ⊎ (N .Q .fst ⊎ ((N' .Q .fst) ⊎ ⊤))
    Q (⊕NFA N N') .snd =
      isFinSet⊎
        (_ , isFinSetUnit)
        (_ , (isFinSet⊎ (N .Q)
          (_ , (isFinSet⊎ (N' .Q) (_ , isFinSetUnit)))))
    -- initial state
    init (⊕NFA N N') = inl _
    -- Acceptance at subautomata accepting states
    isAcc (⊕NFA N N') x =
      DecProp⊎
        (DecPropΣ
          (((fiber (inr ∘ inl) x) , inr∘inl-prop-fibs) ,
            decRec
              {!!}
              {!!}
              {!isDecProp∃ (⊕NFA N N' .Q) ? !})
          (N .isAcc ∘ fst))
        (DecPropΣ
          ((fiber (inr ∘ inr ∘ inl) x , inr∘inr∘inl-prop-fibs) ,
            {!!})
          (N' .isAcc ∘ fst))
        mutex
        where
        inr∘inl-prop-fibs = {!!}

        inr∘inr∘inl-prop-fibs = {!!}

        mutex =
          (λ (q , _) (q' , _) →
            lower (⊎Path.encode _ _
              (isEmbedding→Inj isEmbedding-inr _ _
                (q .snd ∙ (sym (q' .snd))))))

        DecPropFiber :
          ∀ {A}{B : DecProp ℓ}{ℓ} → (f : A → B .fst .fst) →
          hasPropFibers f →
          (b : B .fst .fst) → DecProp ℓ
        DecPropFiber {A} {B} f x b =
          ((fiber f b) , (x b)) , {!!}

        -- (((Σ[ q ∈ fiber (inr ∘ inl) x ] N .isAcc (q .fst) .fst .fst) ,
        --   isPropΣ
        --   (isEmbedding→hasPropFibers
        --     (compEmbedding (_ , isEmbedding-inr)
        --                    (_ , isEmbedding-inl) .snd) x)
        --   λ q → N .isAcc (q .fst) .fst .snd
        -- ) ,
        -- {!!})
        -- (((Σ[ q ∈ fiber (inr ∘ inr ∘ inl) x ] N' .isAcc (q .fst) .fst .fst) ,
        -- isPropΣ
        --   (isEmbedding→hasPropFibers
        --     (compEmbedding (_ , isEmbedding-inr)
        --       (compEmbedding (_ , isEmbedding-inr)
        --                      (_ , isEmbedding-inl)) .snd) x)
        --   λ q → N' .isAcc (q .fst) .fst .snd) ,
        -- {!!})
    -- the labeled transitions come from N and N'
    transition (⊕NFA N N') .fst =
      N .transition .fst ⊎ N' .transition .fst
    transition (⊕NFA N N') .snd =
      isFinSet⊎ (N .transition) (N' .transition)
    -- the labeled transitions have same src, dst, and label as
    -- in original automata
    src (⊕NFA N N') (inl x) = inr (inl (N .src x))
    src (⊕NFA N N') (inr x) = inr (inr (inl (N' .src x)))
    dst (⊕NFA N N') (inl x) = inr (inl (N .dst x))
    dst (⊕NFA N N') (inr x) = inr (inr (inl (N' .dst x)))
    label (⊕NFA N N') (inl x) = N .label x
    label (⊕NFA N N') (inr x) = N' .label x
    fst (ε-transition (⊕NFA N N')) =
      Fin 2 ⊎
      ((Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
      ((Σ[ q ∈ N' .Q .fst ] N' .isAcc q .fst .fst) ⊎
      (N .ε-transition .fst ⊎
      N' .ε-transition .fst)))
    snd (ε-transition (⊕NFA N N')) =
      isFinSet⊎
        (_ , isFinSetFin)
        (_ , isFinSet⊎ (_ ,
          isFinSetΣ (N .Q) (λ q → N .isAcc q .fst .fst ,
            isDecProp→isFinSet
              (N .isAcc q .fst .snd) (N .isAcc q .snd)))
          (_ , (isFinSet⊎ (_ ,
            isFinSetΣ (N' .Q) (λ q → N' .isAcc q .fst .fst ,
            isDecProp→isFinSet
              (N' .isAcc q .fst .snd) (N' .isAcc q .snd)))
            (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))))
    -- ε-transitions to subautomata initial states
    ε-src (⊕NFA N N') (inl fzero) = ⊕NFA N N' .init
    ε-dst (⊕NFA N N') (inl fzero) = inr (inl (N .init))
    ε-src (⊕NFA N N') (inl (inr fzero)) = ⊕NFA N N' .init
    ε-dst (⊕NFA N N') (inl (inr fzero)) = inr (inr (inl (N' .init)))
    -- ε-transitions from subautomata accepting states to accepting state
    ε-src (⊕NFA N N') (inr (inl x)) = {!!}
    ε-dst (⊕NFA N N') (inr (inl x)) = {!!}
    ε-src (⊕NFA N N') (inr (inr (inl x))) = {!!}
    ε-dst (⊕NFA N N') (inr (inr (inl x))) = {!!}
    ε-src (⊕NFA N N') (inr (inr (inr (inl x)))) = {!!}
    ε-dst (⊕NFA N N') (inr (inr (inr (inl x)))) = {!!}
    ε-src (⊕NFA N N') (inr (inr (inr (inr x)))) = {!!}
    ε-dst (⊕NFA N N') (inr (inr (inr (inr x)))) = {!!}
    -- ε-src (⊗NFA N N') (inl (lift fzero)) = (⊗NFA N N') .init
    -- ε-dst (⊗NFA N N') (inl (lift fzero)) = inr (inl (N .init))
    -- -- N acc to N' init
    -- -- ε-src (⊗NFA N N') (inl (lift (fsuc fzero))) = inr (inl (N .acc))
    -- ε-src (⊗NFA N N') (inl (lift (fsuc fzero))) = {!!}
    -- ε-dst (⊗NFA N N') (inl (lift (fsuc fzero))) = inr (inr (inl (N' .init)))
    -- -- N' acc to acc
    -- ε-src (⊗NFA N N') (inl (lift (fsuc (fsuc fzero)))) =
    --   -- inr (inr (inl (N' .acc)))
    --   {!!}
    -- -- ε-dst (⊗NFA N N') (inl (lift (fsuc (fsuc fzero)))) = (⊗NFA N N') .acc
    -- ε-dst (⊗NFA N N') (inl (lift (fsuc (fsuc fzero)))) = {!!}
    -- -- N ε-transitions
    -- ε-src (⊗NFA N N') (inr (inl x)) = inr (inl (N .ε-src x))
    -- ε-dst (⊗NFA N N') (inr (inl x)) = inr (inl (N .ε-dst x))
    -- -- N' ε-transitions
    -- ε-src (⊗NFA N N') (inr (inr x)) = inr (inr (inl (N' .ε-src x)))
    -- ε-dst (⊗NFA N N') (inr (inr x)) = inr (inr (inl (N' .ε-dst x)))

  -- ⊕NFA : (N : NFA) → (N' : NFA) → NFA
  -- -- States stratified into init, N states, N' states, acc
  -- Q (⊕NFA N N') .fst = ⊤ ⊎ (N .Q .fst ⊎ ((N' .Q .fst) ⊎ ⊤))
  -- Q (⊕NFA N N') .snd =
  --   isFinSet⊎
  --     (_ , isFinSetUnit)
  --     (_ , (isFinSet⊎ (N .Q)
  --       (_ , (isFinSet⊎ (N' .Q) (_ , isFinSetUnit)))))
  -- -- initial state
  -- init (⊕NFA N N') = inl _
  -- -- accepting state
  -- acc (⊕NFA N N') = inr (inr (inr _))
  -- -- the labeled transitions come from N and N'
  -- transition (⊕NFA N N') .fst =
  --   N .transition .fst ⊎ N' .transition .fst
  -- transition (⊕NFA N N') .snd =
  --   isFinSet⊎ (N .transition) (N' .transition)
  -- -- the labeled transitions have same src, dst, and label as
  -- -- in original automata
  -- src (⊕NFA N N') (inl x) = inr (inl (N .src x))
  -- src (⊕NFA N N') (inr x) = inr (inr (inl (N' .src x)))
  -- dst (⊕NFA N N') (inl x) = inr (inl (N .dst x))
  -- dst (⊕NFA N N') (inr x) = inr (inr (inl (N' .dst x)))
  -- label (⊕NFA N N') (inl x) = N .label x
  -- label (⊕NFA N N') (inr x) = N' .label x
  -- -- 4 ε-transitions + ones in subautomata
  -- fst (ε-transition (⊕NFA N N')) =
  --   Lift (Fin 4) ⊎ (N .ε-transition .fst ⊎ N' .ε-transition .fst)
  -- snd (ε-transition (⊕NFA N N')) =
  --   isFinSet⊎ {ℓ}
  --     (_ , isFinSetLift isFinSetFin)
  --     (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))
  -- -- init to N init
  -- ε-src (⊕NFA N N') (inl (lift fzero)) = (⊕NFA N N') .init
  -- ε-dst (⊕NFA N N') (inl (lift fzero)) = inr (inl (N .init))
  -- -- init to N init
  -- ε-src (⊕NFA N N') (inl (lift (fsuc fzero))) = (⊕NFA N N') .init
  -- ε-dst (⊕NFA N N') (inl (lift (fsuc fzero))) = inr (inr (inl (N' .init)))
  -- -- N acc to acc
  -- ε-src (⊕NFA N N') (inl (lift (fsuc (fsuc fzero)))) = inr (inl (N .acc))
  -- ε-dst (⊕NFA N N') (inl (lift (fsuc (fsuc fzero)))) = (⊕NFA N N') .acc
  -- -- N' acc to acc
  -- ε-src (⊕NFA N N') (inl (lift (fsuc (fsuc (fsuc fzero))))) =
  --   inr (inr (inl (N' .acc)))
  -- ε-dst (⊕NFA N N') (inl (lift (fsuc (fsuc (fsuc fzero))))) = (⊕NFA N N') .acc
  -- -- N ε-transitions
  -- ε-src (⊕NFA N N') (inr (inl x)) = inr (inl (N .ε-src x))
  -- ε-dst (⊕NFA N N') (inr (inl x)) = inr (inl (N .ε-dst x))
  -- -- N' ε-transitions
  -- ε-src (⊕NFA N N') (inr (inr x)) = inr (inr (inl (N' .ε-src x)))
  -- ε-dst (⊕NFA N N') (inr (inr x)) = inr (inr (inl (N' .ε-dst x)))

  -- KL*NFA : (N : NFA) → NFA
  -- fst (Q (KL*NFA N)) = ⊤ ⊎ (N .Q .fst ⊎ ⊤)
  -- snd (Q (KL*NFA N)) =
  --   isFinSet⊎
  --     (_ , isFinSetUnit)
  --     (_ , isFinSet⊎ (N .Q) (_ , isFinSetUnit))
  -- init (KL*NFA N) = inl _
  -- acc (KL*NFA N) = inr (inr _)
  -- transition (KL*NFA N) = N .transition
  -- src (KL*NFA N) x = inr (inl (N .src x))
  -- dst (KL*NFA N) x = inr (inl (N .dst x))
  -- label (KL*NFA N) x = N .label x
  -- -- 4 ε-transitions + ones in subautomata
  -- fst (ε-transition (KL*NFA N)) = Lift (Fin 4) ⊎ (N .ε-transition .fst)
  -- snd (ε-transition (KL*NFA N)) =
  --   isFinSet⊎ {ℓ}
  --     (_ , isFinSetLift isFinSetFin)
  --     (N .ε-transition)
  -- -- init to N init
  -- ε-src (KL*NFA N) (inl (lift fzero)) = KL*NFA N .init
  -- ε-dst (KL*NFA N) (inl (lift fzero)) = inr (inl (N .init))
  -- -- init to acc
  -- ε-src (KL*NFA N) (inl (lift (fsuc fzero))) = KL*NFA N .init
  -- ε-dst (KL*NFA N) (inl (lift (fsuc fzero))) = KL*NFA N .acc
  -- -- N acc to N init
  -- ε-src (KL*NFA N) (inl (lift (fsuc (fsuc fzero)))) = inr (inl (N .acc))
  -- ε-dst (KL*NFA N) (inl (lift (fsuc (fsuc fzero)))) = inr (inl (N .init))
  -- -- N acc to acc
  -- ε-src (KL*NFA N) (inl (lift (fsuc (fsuc (fsuc fzero))))) = inr (inl (N .acc))
  -- ε-dst (KL*NFA N) (inl (lift (fsuc (fsuc (fsuc fzero))))) = KL*NFA N .acc
  -- -- N ε-transitions
  -- ε-src (KL*NFA N) (inr x) = inr (inl (N .ε-src x))
  -- ε-dst (KL*NFA N) (inr x) = inr (inl (N .ε-dst x))

  -- open Iso
  -- flattenList : {A : Type ℓ} → List A → Type ℓ
  -- flattenList [] = ⊥*
  -- flattenList (x ∷ L) = singl x ⊎ flattenList L

  -- filterDec : {A : Type ℓ} → (P : A → DecProp ℓ) → List A → List (Σ[ a ∈ A ] P a .fst .fst)
  -- filterDec p [] = []
  -- filterDec p (x ∷ L) =
  --   decRec (λ y → (x , y) ∷ (filterDec p L)) (λ _ → (filterDec p L)) (p x .snd)

  -- -- This is the first step toward a correct-by-construction parser
  -- -- Want to get out exectuable code that runs an NFA
  -- -- implement with a lazy list
  -- module _
  --   (N : NFA)
  --   (decEq : Discrete (N .Q .fst))
  --   (decEqTr : Discrete (N .transition .fst))
  --   (decEqΣ : Discrete (Σ₀ .fst))
  --   (trListΣ : Σ[ L ∈ List (N .transition .fst) ] flattenList L ≃ N .transition .fst)
  --   (εtr-ListΣ : Σ[ L ∈ List (N .ε-transition .fst) ] flattenList L ≃ N .ε-transition .fst)
  --   where

  --   trL = trListΣ .fst
  --   εtr-L = εtr-ListΣ .fst

  --   run : (q : N .Q .fst) → (w : String) → Maybe (NFATrace N q w)
  --   run q [] =
  --     decRec
  --     (λ acc≡q → just (subst (λ x → NFATrace N x []) acc≡q nil))
  --     (λ acc≡q→⊥ → nothing) (decEq (N .acc) q)
  --   run q (c ∷ w) = {!!}
  --     where
  --     label≡c : List (Σ[ t ∈ N .transition .fst ] N .label t ≡ c )
  --     label≡c =
  --       filterDec (λ t → (_ , (Σ₀ .snd _ _)) , decEqΣ (N .label t) c) trL

  --     src≡q : List (Σ (Σ[ t ∈ N .transition .fst ] N .label t ≡ c)
  --                   (λ a → N .src (fst a) ≡ q))
  --     src≡q =
  --       filterDec (λ (t , p) →
  --         (_ , isFinSet→isSet (N .Q .snd) _ _) , (decEq (N .src t) q)) label≡c

  --     takeTransition :
  --       (a : Σ (Σ[ t ∈ N .transition .fst ] N .label t ≡ c)
  --         (λ a → N .src (fst a) ≡ q)) →
  --       Maybe (NFATrace N (N .src (a .fst .fst)) (N .label (fst (fst a)) ∷ w))
  --     takeTransition ((t , p) , q) =
  --       map-Maybe (λ tail → cons tail ) (run (N .dst t) w)
