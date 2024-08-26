open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.NFA.Regex ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.More
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.SumFin
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Unit

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Equivalence (Σ₀ , isSetΣ₀)
open import Semantics.DFA
open import Semantics.NFA.Base (Σ₀ , isSetΣ₀)
open import Semantics.Helper
open import Semantics.Term (Σ₀ , isSetΣ₀)

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

open NFA

-- This file constructs NFAs that are strongly equivalent to
-- regular expressions.
--
-- For each constructor of a regular expression, we build
-- a corresponding NFA. And then we inductively combine smaller
-- NFAs into one machine that is equivalent to the regex

-- Literal
-- Accepts only a single character c, drawn from alphabet Σ₀
module _ (c : Σ₀) where
  -- an NFA with two states,
  -- one transition between them labeled with the character c,
  -- the source of the transition is the initial state,
  -- and the target of this transition is accepting
  literalNFA : NFA {ℓ-zero}
  Q literalNFA = Fin 2 , isFinSetFin
  init literalNFA = fzero
  isAcc literalNFA x =
    ((x ≡ fsuc fzero) , (isSetFin _ _)) , (discreteFin _ _)
  transition literalNFA = Fin 1 , isFinSetFin
  src literalNFA _ = fromℕ 0
  dst literalNFA _ = fromℕ 1
  label literalNFA _ = c
  ε-transition literalNFA = ⊥ , isFinSetFin
  ε-src literalNFA ()
  ε-dst literalNFA ()

  open Algebra
  open AlgebraHom
  private
    the-alg : Algebra literalNFA
    the-ℓs the-alg fzero = ℓ-zero
    the-ℓs the-alg (fsuc fzero) = ℓ-zero
    G the-alg fzero = literal c
    G the-alg (fsuc fzero) = ε-grammar
    nil-case the-alg {fzero} qAcc = ⊥.rec (fzero≠fone qAcc)
    nil-case the-alg {fsuc fzero} qAcc = id
    cons-case the-alg fzero = ⊗-unit-r
    ε-cons-case the-alg ()

    initial→the-alg :
      AlgebraHom literalNFA (initial literalNFA) the-alg
    initial→the-alg = ∃AlgebraHom literalNFA the-alg

    the-alg→initial :
      AlgebraHom literalNFA the-alg (initial literalNFA)
    f the-alg→initial fzero =
      ⊗-unit-r⁻ ⋆
      (⊗-intro id (nil refl) ⋆
      cons fzero)
    f the-alg→initial (fsuc fzero) = nil refl
    on-nil the-alg→initial {fzero} qAcc =
      ⊥.rec (fzero≠fone qAcc)
    on-nil the-alg→initial {fsuc fzero} qAcc =
      congS nil (isFinSet→isSet isFinSetFin _ _ refl qAcc)
    on-cons the-alg→initial fzero =
      funExt (λ w → funExt (λ p⊗ →
        cong (cons fzero w)
          (⊗≡ _ _
            (≡-×
              (p⊗ .fst .snd ∙
                  cong (p⊗ .fst .fst .fst ++_) (p⊗ .snd .snd) ∙
                  ++-unit-r (p⊗ .fst .fst .fst))
              (sym (p⊗ .snd .snd)))
          (ΣPathP
              (isProp→PathP (λ i → isSetString _ _) _ _ ,
              congP
                (λ i z →
                  nil {_}{literalNFA} (λ _ → fsuc fzero)
                  (p⊗ .snd .snd (~ i)) z)
                (isProp→PathP (λ i → isSetString _ _)
                  refl (p⊗ .snd .snd)))))))
    on-ε-cons the-alg→initial ()

  open Iso
  literalNFA-strong-equiv :
    isStronglyEquivalent
      (InitParse literalNFA)
      (literal c)
  fun (literalNFA-strong-equiv w) =
    initial→the-alg .f (literalNFA .init) w
  inv (literalNFA-strong-equiv w) =
    the-alg→initial .f (literalNFA .init) w
  rightInv (literalNFA-strong-equiv w) _ =
    isSetString _ _ _ _
  leftInv (literalNFA-strong-equiv w) p =
    cong (λ a → a w p)
      (initial→initial≡id literalNFA
        (AlgebraHom-seq literalNFA
          initial→the-alg the-alg→initial)
        (literalNFA .init))

-- Nullary Disjunction
module _ where
  emptyNFA : NFA {ℓ-zero}
  emptyNFA .Q = Unit , isFinSetUnit
  emptyNFA .init = tt
  emptyNFA .isAcc _ = (⊥ , isProp⊥) , no (λ z → z) -- todo: upstream this def
  emptyNFA .transition = ⊥ , isFinSet⊥
  emptyNFA .src = ⊥.elim
  emptyNFA .dst = ⊥.elim
  emptyNFA .label = ⊥.elim
  emptyNFA .ε-transition = ⊥ , isFinSet⊥
  emptyNFA .ε-src = ⊥.rec
  emptyNFA .ε-dst = ⊥.rec

  emptyNFA-strong-equiv :
    StrongEquivalence (InitParse emptyNFA) ⊥-grammar
  emptyNFA-strong-equiv = mkStrEq
    (recInit _ ⊥Alg)
    ⊥-elim
    (⊥-η _ _)
    (algebra-η _ (AlgebraHom-seq _ (∃AlgebraHom _ ⊥Alg)
      (record { f = λ _ → ⊥-elim
              ; on-nil = ⊥.elim
              ; on-cons = ⊥.elim
              ; on-ε-cons = ⊥.elim })))
    where
      open Algebra
      ⊥Alg : Algebra emptyNFA
      ⊥Alg .the-ℓs = _
      ⊥Alg .G _ = ⊥-grammar
      ⊥Alg .nil-case = ⊥.elim
      ⊥Alg .cons-case = ⊥.elim
      ⊥Alg .ε-cons-case = ⊥.elim

-- Binary Disjunction
-- Given two NFAs N and N', accepts a string if and only if
-- the string is accept by N or by N'
module _ (N : NFA {ℓN}) (N' : NFA {ℓN'}) where
  -- has the states from N, the states from N', and
  -- a single new state that is initial
  -- the new initial state has epsilon transitions to
  -- the initial states of the subautomata N and N'
  -- and the rest of the transitions are just those that occur
  -- in the subautomata
  ⊕NFA : NFA {ℓ-max ℓN ℓN'}
  NFA.Q ⊕NFA =
    (⊤ ⊎ (N .Q .fst ⊎ N' .Q .fst)) ,
    (isFinSet⊎
      (⊤ , isFinSetUnit)
      ((N .Q .fst ⊎ N' .Q .fst) , (isFinSet⊎ (N .Q) (N' .Q))))
  NFA.init ⊕NFA = inl _
  isAcc ⊕NFA (inl x) = (⊥* , isProp⊥*) , (no lower)
  isAcc ⊕NFA (inr (inl x)) = LiftDecProp {ℓN}{ℓN'}(N .isAcc x)
  isAcc ⊕NFA (inr (inr x)) = LiftDecProp {ℓN'}{ℓN}(N' .isAcc x)
  NFA.transition ⊕NFA =
    (N .transition .fst ⊎ N' .transition .fst) ,
    (isFinSet⊎ (N .transition) (N' .transition))
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

  open Algebra
  open AlgebraHom

  private
    the-N-alg : Algebra N
    the-ℓs the-N-alg _ = ℓ-max ℓN ℓN'
    G the-N-alg q = Parse ⊕NFA (inr (inl q))
    nil-case the-N-alg qAcc =
      nil (LiftDecPropWitness {ℓN}{ℓN'} (N .isAcc _) qAcc)
    cons-case the-N-alg tr = cons (inl tr)
    ε-cons-case the-N-alg εtr = ε-cons (inr (inl εtr))

    the-N'-alg : Algebra N'
    the-ℓs the-N'-alg _ = ℓ-max ℓN ℓN'
    G the-N'-alg q = Parse ⊕NFA (inr (inr q))
    nil-case the-N'-alg qAcc =
      nil (LiftDecPropWitness {ℓN'}{ℓN} (N' .isAcc _) qAcc)
    cons-case the-N'-alg tr = cons (inr tr)
    ε-cons-case the-N'-alg εtr = ε-cons (inr (inr εtr))

    the-⊕NFA-alg : Algebra ⊕NFA
    the-ℓs the-⊕NFA-alg (inl _) = ℓ-max ℓN ℓN'
    the-ℓs the-⊕NFA-alg (inr (inl q)) = ℓN
    the-ℓs the-⊕NFA-alg (inr (inr q)) = ℓN'
    G the-⊕NFA-alg (inl _) = Parse N (N .init) ⊕ Parse N' (N' .init)
    G the-⊕NFA-alg (inr (inl q)) = Parse N q
    G the-⊕NFA-alg (inr (inr q)) = Parse N' q
    nil-case the-⊕NFA-alg {inr (inl q)} qAcc =
      nil (LowerDecPropWitness {ℓN}{ℓN'} (N .isAcc q) qAcc)
    nil-case the-⊕NFA-alg {inr (inr q)} qAcc =
      nil (LowerDecPropWitness {ℓN'}{ℓN} (N' .isAcc q) qAcc)
    cons-case the-⊕NFA-alg (inl tr) = cons tr
    cons-case the-⊕NFA-alg (inr tr) = cons tr
    ε-cons-case the-⊕NFA-alg (inl (inl _)) = ⊕-inl
    ε-cons-case the-⊕NFA-alg (inl (inr (inl _))) = ⊕-inr
    ε-cons-case the-⊕NFA-alg (inr (inl εtr)) = ε-cons εtr
    ε-cons-case the-⊕NFA-alg (inr (inr εtr)) = ε-cons εtr

    initialN→the-N-alg : AlgebraHom N (initial N) the-N-alg
    initialN→the-N-alg = ∃AlgebraHom N the-N-alg

    initialN'→the-N'-alg : AlgebraHom N' (initial N') the-N'-alg
    initialN'→the-N'-alg = ∃AlgebraHom N' the-N'-alg

    initial⊕NFA→the-⊕NFA-alg : AlgebraHom ⊕NFA (initial ⊕NFA) the-⊕NFA-alg
    initial⊕NFA→the-⊕NFA-alg = ∃AlgebraHom ⊕NFA the-⊕NFA-alg

    the-N-alg→initialN : AlgebraHom N the-N-alg (initial N)
    f the-N-alg→initialN q = initial⊕NFA→the-⊕NFA-alg .f (inr (inl q))
    on-nil the-N-alg→initialN {q} qAcc =
      cong nil (LowerLiftWitness (N .isAcc q) qAcc)
    on-cons the-N-alg→initialN _ = refl
    on-ε-cons the-N-alg→initialN _ = refl

    the-N'-alg→initialN' : AlgebraHom N' the-N'-alg (initial N')
    f the-N'-alg→initialN' q = initial⊕NFA→the-⊕NFA-alg .f (inr (inr q))
    on-nil the-N'-alg→initialN' {q} qAcc =
      cong nil (LowerLiftWitness (N' .isAcc q) qAcc)
    on-cons the-N'-alg→initialN' _ = refl
    on-ε-cons the-N'-alg→initialN' _ = refl

    the-⊕NFA-alg→initial⊕NFA : AlgebraHom ⊕NFA the-⊕NFA-alg (initial ⊕NFA)
    f the-⊕NFA-alg→initial⊕NFA (inl _) =
      ⊕-elim
        (initialN→the-N-alg .f (N .init) ⋆ ε-cons (inl (inl _)))
        (initialN'→the-N'-alg .f (N' .init) ⋆ ε-cons (inl (inr (inl _))))
    f the-⊕NFA-alg→initial⊕NFA (inr (inl q)) = initialN→the-N-alg .f q
    f the-⊕NFA-alg→initial⊕NFA (inr (inr q)) = initialN'→the-N'-alg .f q
    on-nil the-⊕NFA-alg→initial⊕NFA {inr (inl q)} qAcc =
      cong nil (LiftLowerWitness (N .isAcc q) qAcc)
    on-nil the-⊕NFA-alg→initial⊕NFA {inr (inr q)} qAcc =
      cong nil (LiftLowerWitness (N' .isAcc q) qAcc)
    on-cons the-⊕NFA-alg→initial⊕NFA (inl tr) = refl
    on-cons the-⊕NFA-alg→initial⊕NFA (inr tr) = refl
    on-ε-cons the-⊕NFA-alg→initial⊕NFA (inl (inl _)) = refl
    on-ε-cons the-⊕NFA-alg→initial⊕NFA (inl (inr (inl _))) = refl
    on-ε-cons the-⊕NFA-alg→initial⊕NFA (inr (inl εtr)) = refl
    on-ε-cons the-⊕NFA-alg→initial⊕NFA (inr (inr εtr)) = refl

  open Iso
  ⊕NFA-strong-equiv :
    isStronglyEquivalent
      (Parse ⊕NFA (⊕NFA .init))
      (Parse N (N .init) ⊕ Parse N' (N' .init))
  fun (⊕NFA-strong-equiv w) = initial⊕NFA→the-⊕NFA-alg .f (⊕NFA .init) w
  inv (⊕NFA-strong-equiv w) = the-⊕NFA-alg→initial⊕NFA .f (inl _) w
  rightInv (⊕NFA-strong-equiv w) (inl pN) =
    cong inl (cong (λ a → a w pN)
      (initial→initial≡id N
        (AlgebraHom-seq N
          initialN→the-N-alg the-N-alg→initialN)
          (N .init)))
  rightInv (⊕NFA-strong-equiv w) (inr pN') =
    cong inr (cong (λ a → a w pN')
      (initial→initial≡id N'
        (AlgebraHom-seq N'
          initialN'→the-N'-alg the-N'-alg→initialN')
          (N' .init)))
  leftInv (⊕NFA-strong-equiv w) p =
    cong (λ a → a w p)
      (initial→initial≡id ⊕NFA
        (AlgebraHom-seq ⊕NFA
          initial⊕NFA→the-⊕NFA-alg
          the-⊕NFA-alg→initial⊕NFA)
        (⊕NFA .init))

-- Epsilon, the nullary sequencing
module _ where
  -- an NFA with one state,
  -- no transitions,
  -- and the single state is both initial and accepting
  εNFA : NFA {ℓ-zero}
  εNFA .Q = Unit , isFinSetUnit
  εNFA .init = tt
  εNFA .isAcc = λ x → (Unit , isPropUnit) , (yes _)
  εNFA .transition = ⊥ , isFinSet⊥
  εNFA .src = ⊥.rec
  εNFA .dst = ⊥.rec
  εNFA .label = ⊥.rec
  εNFA .ε-transition = ⊥ , isFinSet⊥
  εNFA .ε-src = ⊥.rec
  εNFA .ε-dst = ⊥.rec

  εNFA-strong-equiv :
    StrongEquivalence (InitParse εNFA) ε-grammar
  εNFA-strong-equiv = mkStrEq
    (recInit _ εAlg)
    (nil _)
    refl
    (algebra-η _ (AlgebraHom-seq _ (∃AlgebraHom _ εAlg) (record
      { f = λ _ → nil _
      ; on-nil = λ _ → refl
      ; on-cons = ⊥.elim
      ; on-ε-cons = ⊥.elim })))
    where
      open Algebra
      εAlg : Algebra εNFA
      εAlg .the-ℓs = _
      εAlg .G = λ _ → ε-grammar
      εAlg .nil-case = λ _ → id
      εAlg .cons-case = ⊥.elim
      εAlg .ε-cons-case = ⊥.elim

-- Concatenation
-- Given two NFAs N and N', accepts a string w if and only if
-- w ≡ w₁ ++ w₂ where w₁ is accepted by N and w₂ accepted by N'
module _ (N : NFA {ℓN}) (N' : NFA {ℓN'}) where
  -- Has the states from N and the states from N'
  -- the initial state of the subautomaton N is the initial state
  -- Every accepting state of N has an epsilon transiton to
  -- the initial state of N'
  -- The accepting states of the subautomaton N' are accepting
  ⊗NFA : NFA {ℓ-max ℓN ℓN'}
  Q ⊗NFA .fst = N .Q .fst ⊎ N' .Q .fst
  Q ⊗NFA .snd = isFinSet⊎ (N .Q) (N' .Q)
  init ⊗NFA = inl (N .init)
  isAcc ⊗NFA (inl x) =
    DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
  isAcc ⊗NFA (inr x) =
    LiftDecProp {ℓN'}{ℓN} (N' .isAcc x)
  transition ⊗NFA .fst = N .transition .fst ⊎ N' .transition .fst
  transition ⊗NFA .snd = isFinSet⊎ (N .transition) (N' .transition)
  -- transitions from subautomata
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
  -- ε-transition from accepting states of N to initial state of N'
  ε-src ⊗NFA (inl x) = inl (x .fst)
  ε-dst ⊗NFA (inl x) = inr (N' .init)
  -- ε-transitions from subautomata
  ε-src ⊗NFA (inr (inl x)) = inl (N .ε-src x)
  ε-dst ⊗NFA (inr (inl x)) = inl (N .ε-dst x)
  ε-src ⊗NFA (inr (inr x)) = inr (N' .ε-src x)
  ε-dst ⊗NFA (inr (inr x)) = inr (N' .ε-dst x)

  open Algebra
  open AlgebraHom

  private
    the-N'-alg : Algebra N'
    the-ℓs the-N'-alg _ = ℓ-max ℓN ℓN'
    G the-N'-alg q = Parse ⊗NFA (inr q)
    nil-case the-N'-alg qAcc =
      nil (LiftDecPropWitness (N' .isAcc _) qAcc)
    cons-case the-N'-alg tr = cons (inr tr)
    ε-cons-case the-N'-alg εtr = ε-cons (inr (inr εtr))

    initialN'→the-N'-alg : AlgebraHom N' (initial N') the-N'-alg
    initialN'→the-N'-alg = ∃AlgebraHom N' the-N'-alg

    the-N-alg : Algebra N
    the-ℓs the-N-alg _ = ℓ-max ℓN ℓN'
    G the-N-alg q = Parse ⊗NFA (inl q) ⊗- Parse N' (N' .init)
    nil-case the-N-alg {q} qAcc =
      ⊗--intro
        (⊗-unit-l ⋆
        (initialN'→the-N'-alg .f (N' .init) ⋆
        ε-cons (inl (q , qAcc))))
    cons-case the-N-alg tr =
      ⊗--assoc {h = Parse ⊗NFA (inl (N .dst tr))} ⋆
      (functoriality
        {g = literal (N .label tr) ⊗ Parse ⊗NFA (inl (N .dst tr))}
        {h = Parse ⊗NFA (inl (N .src tr))}
        (var ⊗-func Parse N' (N' .init))
        (cons (inl tr)))
    ε-cons-case the-N-alg εtr =
      (functoriality
        {g = Parse ⊗NFA (inl (N .ε-dst εtr))}
        {h = Parse ⊗NFA (inl (N .ε-src εtr))}
        (var ⊗-func Parse N' (N' .init))
        (ε-cons (inr (inl εtr))))

    initialN→the-N-alg : AlgebraHom N (initial N) the-N-alg
    initialN→the-N-alg = ∃AlgebraHom N the-N-alg

    the-⊗NFA-alg : Algebra ⊗NFA
    the-ℓs the-⊗NFA-alg (inl q) = ℓ-max ℓN ℓN'
    the-ℓs the-⊗NFA-alg (inr q) = ℓN'
    G the-⊗NFA-alg (inl q) = Parse N q ⊗ Parse N' (N' .init)
    G the-⊗NFA-alg (inr q) = Parse N' q
    nil-case the-⊗NFA-alg {inl q} qAcc = ⊥.rec (lower qAcc)
    nil-case the-⊗NFA-alg {inr q} qAcc =
      nil (LowerDecPropWitness (N' .isAcc q) qAcc)
    cons-case the-⊗NFA-alg (inl tr) =
      ⊗-assoc ⋆
      functoriality (var ⊗l Parse N' (N' .init))
        (cons tr)
    cons-case the-⊗NFA-alg (inr tr) = cons tr
    ε-cons-case the-⊗NFA-alg (inl N-acc) =
      ⊗-unit-l⁻ ⋆
      ⊗-intro (nil (N-acc .snd)) id
    ε-cons-case the-⊗NFA-alg (inr (inl εtr)) =
      functoriality (var ⊗l Parse N' (N' .init))
        (ε-cons εtr)
    ε-cons-case the-⊗NFA-alg (inr (inr εtr)) = ε-cons εtr

    initial⊗NFA→the-⊗NFA-alg :
      AlgebraHom ⊗NFA (initial ⊗NFA) the-⊗NFA-alg
    initial⊗NFA→the-⊗NFA-alg = ∃AlgebraHom ⊗NFA the-⊗NFA-alg

    the-N'-alg→initialN' : AlgebraHom N' the-N'-alg (initial N')
    f the-N'-alg→initialN' q = initial⊗NFA→the-⊗NFA-alg .f (inr q)
    on-nil the-N'-alg→initialN' {q} qAcc =
      cong nil (LowerLiftWitness (N' .isAcc q) qAcc)
    on-cons the-N'-alg→initialN' tr = refl
    on-ε-cons the-N'-alg→initialN' εtr = refl

    the-N-alg→initialN : AlgebraHom N the-N-alg (initial N)
    f the-N-alg→initialN q =
      -- {!!}
      -- functoriality (var ⊗-func Parse N' (N' .init))
      --   (initial⊗NFA→the-⊗NFA-alg .f (inl q)) ⋆
      -- {!!}
      {!initial⊗NFA→the-⊗NFA-alg .f (inl q)!}
    on-nil the-N-alg→initialN = {!!}
    on-cons the-N-alg→initialN = {!!}
    on-ε-cons the-N-alg→initialN = {!!}

    the-⊗NFA-alg→initial⊗NFA :
      AlgebraHom ⊗NFA the-⊗NFA-alg (initial ⊗NFA)
    f the-⊗NFA-alg→initial⊗NFA (inl q) =
      ⊗-intro
        (initialN→the-N-alg .f q) id ⋆
      ⊗--app
    f the-⊗NFA-alg→initial⊗NFA (inr q) = initialN'→the-N'-alg .f q
    on-nil the-⊗NFA-alg→initial⊗NFA {inr q} qAcc =
      cong nil (LiftLowerWitness (N' .isAcc q) qAcc)
-- Goal: seq
--       (the-⊗NFA-alg .Semantics.NFA.Base.NFA.Algebra.cons-case (inl tr))
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.src ⊗NFA (inl tr)))
--       ≡
--       seq
--       (⊗-intro id
--        (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--         (Semantics.NFA.Base.NFA.dst ⊗NFA (inl tr))))
--       (initial ⊗NFA .Semantics.NFA.Base.NFA.Algebra.cons-case (inl tr))
    on-cons the-⊗NFA-alg→initial⊗NFA (inl tr) = {!!}
    on-cons the-⊗NFA-alg→initial⊗NFA (inr tr) = refl
-- Goal: seq
--       (the-⊗NFA-alg .Semantics.NFA.Base.NFA.Algebra.ε-cons-case
--        (inl N-acc))
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.ε-src ⊗NFA (inl N-acc)))
--       ≡
--       seq
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.ε-dst ⊗NFA (inl N-acc)))
--       (initial ⊗NFA .Semantics.NFA.Base.NFA.Algebra.ε-cons-case
--        (inl N-acc))
    on-ε-cons the-⊗NFA-alg→initial⊗NFA (inl N-acc) = {!!}
-- Goal: seq
--       (the-⊗NFA-alg .Semantics.NFA.Base.NFA.Algebra.ε-cons-case
--        (fsuc (inl εtr)))
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.ε-src ⊗NFA (fsuc (inl εtr))))
--       ≡
--       seq
--       (Semantics.NFA.Base.NFA.AlgebraHom.f the-⊗NFA-alg→initial⊗NFA
--        (Semantics.NFA.Base.NFA.ε-dst ⊗NFA (fsuc (inl εtr))))
--       (initial ⊗NFA .Semantics.NFA.Base.NFA.Algebra.ε-cons-case
--        (fsuc (inl εtr)))
    on-ε-cons the-⊗NFA-alg→initial⊗NFA (inr (inl εtr)) = {!!}
    on-ε-cons the-⊗NFA-alg→initial⊗NFA (inr (inr εtr)) = refl

  open Iso
  ⊗NFA-strong-equiv :
    isStronglyEquivalent
      (Parse ⊗NFA (⊗NFA .init))
      ((Parse N (N .init)) ⊗ (Parse N' (N' .init)))
  fun (⊗NFA-strong-equiv w) = initial⊗NFA→the-⊗NFA-alg .f (⊗NFA .init) w
  inv (⊗NFA-strong-equiv w) = the-⊗NFA-alg→initial⊗NFA .f (inl (N .init)) w
  rightInv (⊗NFA-strong-equiv w) p⊗ =
    {!!}
  leftInv (⊗NFA-strong-equiv w) p =
    cong (λ a → a w p)
      (initial→initial≡id ⊗NFA
        (AlgebraHom-seq ⊗NFA
          initial⊗NFA→the-⊗NFA-alg
          the-⊗NFA-alg→initial⊗NFA)
        (inl (N .init)))

-- Kleene Star
module _ (N : NFA {ℓN}) where
  KL*NFA : NFA {ℓN}
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

  open Algebra
  open AlgebraHom

  private
    the-N-alg : Algebra N
    the-N-alg = {!!}

    initialN→the-N-alg : AlgebraHom N (initial N) the-N-alg
    initialN→the-N-alg = ∃AlgebraHom N the-N-alg

    the-KL*-alg : Algebra KL*NFA
    the-KL*-alg = {!!}

    initialKL*→the-KL*-alg : AlgebraHom KL*NFA (initial KL*NFA) the-KL*-alg
    initialKL*→the-KL*-alg = ∃AlgebraHom KL*NFA the-KL*-alg
