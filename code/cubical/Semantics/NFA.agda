{-# OPTIONS --lossy-unification #-}
module Semantics.NFA where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
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
open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Grammar public
open import Semantics.DFA

private
  variable ℓ ℓ' : Level

module NFADefs ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)

  record NFA : Type (ℓ-suc ℓ) where
    constructor mkNFA
    field
      Q : FinSet ℓ
      init : Q .fst
      isAcc : Q .fst → DecProp ℓ
      transition : FinSet ℓ
      src : transition .fst → Q .fst
      dst : transition .fst → Q .fst
      label : transition .fst → Σ₀
      ε-transition : FinSet ℓ
      ε-src : ε-transition .fst → Q .fst
      ε-dst : ε-transition .fst → Q .fst

    decEqQ : Discrete (Q .fst)
    decEqQ = isFinSet→Discrete (Q .snd)

    acc? : Q .fst → Grammar
    acc? q = DecProp-grammar (isAcc q) ⊤-grammar ⊥-grammar

    rej? : Q .fst → Grammar
    rej? q = DecProp-grammar (negateDecProp (isAcc q)) ⊤-grammar ⊥-grammar

    data NFATrace
      (q : Q .fst)
      (q-end : Q .fst) : (w : String) → Type ℓ where
      nil : (q ≡ q-end) → ParseTransformer ε-grammar (NFATrace q q-end)
      cons : ∀ {t} →
        (src t ≡ q) →
        ParseTransformer
          (literal (label t) ⊗ NFATrace (dst t) q-end) (NFATrace q q-end)
      ε-cons : ∀ {t} →
        (ε-src t ≡ q) →
        ParseTransformer
          (NFATrace (ε-dst t) q-end) (NFATrace q q-end)

    NFAelim :
      (P : ∀ q q' w → (NFATrace q q' w) → Type ℓ) →
      (nil-case : ∀ {q}{q'}{w}{x}{p} → P q q' w (nil p x)) →
      (cons-case : ∀ {q}{q'}{w} → (t : transition .fst) →
        (p : src t ≡ q) →
        -- TODO there is something redundant here about having y and tr
        -- but it seems to make things easier to have them
        -- because it lets us handle arbitrary y
        (y : (literal (label t) ⊗ NFATrace (dst t) q') (label t ∷ w)) →
        (tr : NFATrace (dst t) q' w) →
        P (dst t) q' w tr →
        P q q' (label t ∷ w) (cons p y)) →
      (ε-cons-case : ∀ {q}{q'}{w} → (t : ε-transition .fst) →
        (p : ε-src t ≡ q) →
        (tr : NFATrace (ε-dst t) q' w) →
        P (ε-dst t) q' w tr →
        P q q' w (ε-cons p tr)) →
      (q q' : Q .fst) → (w : String) →
      (tr : NFATrace q q' w) →
      P q q' w tr
    NFAelim P nil-case cons-case ε-cons-case q q' w (nil p x) = nil-case
    NFAelim P nil-case cons-case ε-cons-case q q' w (cons {t} x y) =
      transport
        (cong₂ (λ a b → P q q' a (cons x b))
          the-string-path (symP (toPathP refl)))
        (cons-case t x the-parse (y .snd .snd)
          (NFAelim P nil-case cons-case ε-cons-case (dst t) q'
            (y .fst .fst .snd) (y .snd .snd)))
      where
      the-string-path : label t ∷ y .fst .fst .snd ≡ w
      the-string-path =
        sym (y .fst .snd ∙ cong (λ a → a ++ y .fst .fst .snd) (y .snd .fst))

      the-parse :
        (literal (label t) ⊗ NFATrace (dst t) q') (label t ∷ y .fst .fst .snd)
      the-parse =
        transport
        ( sym (cong (λ a → (_ ⊗ _) a) the-string-path) )
        y
    NFAelim P nil-case cons-case ε-cons-case q q' w (ε-cons {t} x tr) =
      ε-cons-case t x tr
        (NFAelim P nil-case cons-case ε-cons-case (ε-dst t) q' w tr)

    Parses : Grammar
    Parses =
      LinΣ[ q ∈ Σ[ q' ∈ Q .fst ] isAcc q' .fst .fst ] NFATrace init (q .fst)

    negate : NFA
    Q negate = Q
    init negate = init
    isAcc negate q = negateDecProp (isAcc q)
    transition negate = transition
    src negate = src
    dst negate = dst
    label negate = label
    ε-transition negate = ε-transition
    ε-src negate = ε-src
    ε-dst negate = ε-dst

  open NFA
  module _ (c : Σ₀) where
    literalNFA : NFA
    fst (Q literalNFA) = Lift (Fin 2)
    snd (Q literalNFA) = isFinSetLift isFinSetFin
    init literalNFA = lift (inl tt)
    fst (fst (isAcc literalNFA x)) = x ≡ lift (inr (inl tt))
    snd (fst (isAcc literalNFA x)) = isSetLift isSetFin _ _
    snd (isAcc literalNFA x) = discreteLift discreteFin _ _
    transition literalNFA = Lift Unit , isFinSetLift isFinSetUnit
    src literalNFA _ = lift (inl tt)
    dst literalNFA _ = lift (inr (inl tt))
    label literalNFA _ = c
    ε-transition literalNFA = Lift ⊥ , isFinSetLift isFinSetFin
    ε-src literalNFA x = ⊥.rec (lower x)
    ε-dst literalNFA x = ⊥.rec (lower x)

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

  module _ (N : NFA) where
    isDeterministic : Type ℓ
    isDeterministic =
      -- No ε-transitions
      (N .ε-transition .fst ≃ Fin 0) ×
      -- forall states
      (∀ (q : N .Q .fst) →
        -- there are only Σ₀-many transitions (may be redundant)
        (fiber (N .dst) q ≃ Σ₀) ×
        -- and there is exactly one for each label c
        (∀ (c : Σ₀) →
          isContr (Σ[ t ∈ fiber (N .dst) q ]
           (N .label (t .fst) ≡ c))))

    module _ (deter : isDeterministic) where
      open DFADefs ℓ (Σ₀ , isFinSetΣ₀)
      open DFADefs.DFA

      deterministicNFA : DFA
      Q deterministicNFA = N .Q
      init deterministicNFA = N .init
      isAcc deterministicNFA = N .isAcc
      δ deterministicNFA q c =
        N .dst (deter .snd q .snd c .fst .fst .fst)



  -- NFA Combinators
  module _ (N : NFA) where
    module _ (N' : NFA) where

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
                (PT.elim
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
                (PT.elim
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
  NFAfromRegularGrammar ε-Reg = emptyNFA
  NFAfromRegularGrammar (g ⊗Reg h) =
    ⊗NFA (NFAfromRegularGrammar g) (NFAfromRegularGrammar h)
  NFAfromRegularGrammar (literalReg c) = literalNFA c
  NFAfromRegularGrammar (g ⊕Reg h) =
    ⊕NFA (NFAfromRegularGrammar g) (NFAfromRegularGrammar h)
  NFAfromRegularGrammar (KL*Reg g) = KL*NFA (NFAfromRegularGrammar g)

  open Iso
  module regex-isos where
    εNFA-P : ∀ q q' w → NFATrace emptyNFA q q' w → Type ℓ
    εNFA-P q q' w tr = w ≡ []

    εNFA-nil-case : ∀ {q}{q'}{w}{x}{p} → εNFA-P q q' w (nil p x)
    εNFA-nil-case = {!!}

    εNFA-cons-case : ∀ {q}{q'}{w} →
      (t : emptyNFA .transition .fst) → (p : emptyNFA .src t ≡ q) →
      (y : {!!}) → (tr : NFATrace emptyNFA (emptyNFA .dst t) q' w) →
      {!!} → {!!}
    εNFA-cons-case = {!!}

    εNFA-ε-cons-case : ∀ {q}{q'}{w} →
      (t : emptyNFA .ε-transition .fst) → (p : emptyNFA .ε-src t ≡ q) →
      (tr : NFATrace emptyNFA (emptyNFA .ε-dst t) q' w) →
      {!!} → {!!}
    εNFA-ε-cons-case = {!!}

    elim-εNFA : (q q' : emptyNFA .Q .fst) → (w : String) →
      (tr : NFATrace emptyNFA q q' w) → εNFA-P q q' w tr
    elim-εNFA =
      NFAelim emptyNFA εNFA-P εNFA-nil-case εNFA-cons-case εNFA-ε-cons-case

    ε-regex-iso : isStronglyEquivalent ε-grammar (Parses emptyNFA)
    fun (ε-regex-iso w) p = {!!}
    inv (ε-regex-iso w) a =
      elim-εNFA (emptyNFA .init) (lift (fsuc fzero)) w
        (transport (cong (λ z → NFATrace _ _ z _) (a .fst .snd)) (a .snd))
    rightInv (ε-regex-iso w) = {!!}
    leftInv (ε-regex-iso w) = {!!}

  isStronglyEquivalent-NFA-Regex : (g : RegularGrammar) →
    isStronglyEquivalent
      (RegularGrammar→Grammar g)
      (Parses (NFAfromRegularGrammar g))
  isStronglyEquivalent-NFA-Regex GrammarDefs.ε-Reg = regex-isos.ε-regex-iso
  isStronglyEquivalent-NFA-Regex (GrammarDefs.literalReg x) w = {!!}
  isStronglyEquivalent-NFA-Regex (g GrammarDefs.⊗Reg g₁) w = {!!}
  isStronglyEquivalent-NFA-Regex (g GrammarDefs.⊕Reg g₁) w = {!!}
  isStronglyEquivalent-NFA-Regex (GrammarDefs.KL*Reg g) w = {!!}


open NFADefs
open NFA
open DFADefs
open DFA
module _ {ℓ} ((Σ₀ , isFinSetΣ₀) : FinSet ℓ)
  (N : NFA ℓ (Σ₀ , isFinSetΣ₀))
  where

  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)

  powersetNFA : NFA ℓ (Σ₀ , isFinSetΣ₀)
  fst (Q powersetNFA) = (N .Q .fst) → Bool
  snd (Q powersetNFA) = isFinSet→ (N .Q) (Bool , isFinSetBool)
  init powersetNFA q =
    if Dec→Bool (NFA.decEqQ N q (N .init)) then
      true else
      false
  fst (fst (isAcc powersetNFA f)) = ∃[ q ∈ N .Q .fst ] f q ≡ true
  snd (fst (isAcc powersetNFA f)) = isPropPropTrunc
  snd (isAcc powersetNFA f) =
    isFinSet→Dec∥∥ (isFinSetΣ (N .Q) λ z → (f z ≡ true) ,
      isDecProp→isFinSet (isSetBool (f z) true)
        (isFinSet→Discrete isFinSetBool (f z) true))
  fst (transition powersetNFA) =
    Σ[ f ∈ (N .Q .fst → Bool) ] Σ[ g ∈ (N .Q .fst → Bool) ]
      Σ[ c ∈ Σ₀ ]
      ∃[ t ∈ N .transition .fst ]
        ( f (N .src t) ≡ true ) × ( g (N .dst t) ≡ true ) × (N .label t ≡ c)
  snd (transition powersetNFA) =
    isFinSetΣ (powersetNFA .Q)
      λ x → _ , isFinSetΣ (powersetNFA .Q) λ x → _ ,
        isFinSetΣ (Σ₀ , isFinSetΣ₀) λ c → _ , isFinSet∥∥ (_ ,
          isFinSetΣ (N .transition) (λ t → _ , isFinSetΣ (_ ,
            isDecProp→isFinSet (isSetBool _ _) (DiscreteBool _ _)) λ _ → _ ,
              isFinSetΣ (_ , isDecProp→isFinSet (isSetBool _ _) (DiscreteBool _ _)) λ _ → _ ,
                isDecProp→isFinSet (isSetΣ₀ _ _) (DiscreteΣ₀ _ _)))
      where
      DiscreteBool : Discrete Bool
      DiscreteBool = isFinSet→Discrete isFinSetBool
  src powersetNFA t = t .fst
  dst powersetNFA t = t .snd .fst
  label powersetNFA t = t .snd .snd .fst
  fst (ε-transition powersetNFA) = ⊥*
  snd (ε-transition powersetNFA) = isFinSetLift isFinSetFin
  ε-src powersetNFA x = ⊥.rec (lower x)
  ε-dst powersetNFA x = ⊥.rec (lower x)

  isDeterministic-powersetNFA : isDeterministic _ _ (powersetNFA)
  fst isDeterministic-powersetNFA = uninhabEquiv (λ x → lower x) (λ x → x)
  fst (fst (snd isDeterministic-powersetNFA c)) x = x .fst .snd .snd .fst
  fst (fst (fst (equiv-proof (snd (fst (snd isDeterministic-powersetNFA f))) c))) =
    f , ({!!} , (c , ∣ {!!} , ({!!} , ({!!} , {!!})) ∣₁))
    where
    the-g : N .Q .fst → Bool
    the-g q = {!!}
  snd (fst (fst (equiv-proof (snd (fst (snd isDeterministic-powersetNFA f))) c))) = {!!}
  snd (fst (equiv-proof (snd (fst (snd isDeterministic-powersetNFA f))) c)) = {!!}
  snd (equiv-proof (snd (fst (snd isDeterministic-powersetNFA f))) c) = {!!}
  fst (snd (snd isDeterministic-powersetNFA f) c) = {!!}
  snd (snd (snd isDeterministic-powersetNFA f) c) = {!!}


  powersetDFA : DFA ℓ (Σ₀ , isFinSetΣ₀)
  Q powersetDFA = {!!}
  init powersetDFA = {!!}
  isAcc powersetDFA = {!!}
  δ powersetDFA = {!!}
