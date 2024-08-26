open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.NFA.Regex ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
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

-- Empty
-- Accepts only the empty string
module _ where
  -- an NFA with one state,
  -- no transitions,
  -- and the single state is both initial and accepting
  emptyNFA : NFA {ℓ-zero}
  Q emptyNFA = Fin 1 , isFinSetFin
  init emptyNFA = fzero
  isAcc emptyNFA x =
    ((x ≡ fzero) , (isSetFin _ _)) , (discreteFin _ _)
  transition emptyNFA = ⊥ , isFinSetFin
  src emptyNFA ()
  dst emptyNFA ()
  label emptyNFA ()
  ε-transition emptyNFA = ⊥ , isFinSetFin
  ε-src emptyNFA ()
  ε-dst emptyNFA ()

  open Algebra
  open AlgebraHom
  private
    the-alg : Algebra emptyNFA
    the-ℓs the-alg fzero = ℓ-zero
    G the-alg fzero = ε-grammar
    nil-case the-alg {fzero} qAcc = id
    cons-case the-alg ()
    ε-cons-case the-alg ()

    initial→the-alg :
      AlgebraHom emptyNFA (initial emptyNFA) the-alg
    initial→the-alg = ∃AlgebraHom emptyNFA the-alg

    the-alg→initial :
      AlgebraHom emptyNFA the-alg (initial emptyNFA)
    f the-alg→initial fzero = nil refl
    on-nil the-alg→initial {fzero} qAcc =
      congS nil (isFinSet→isSet isFinSetFin fzero fzero refl qAcc)
    on-cons the-alg→initial ()
    on-ε-cons the-alg→initial ()

  open Iso

  emptyNFA-strong-equiv :
    isStronglyEquivalent
      (Parse emptyNFA (emptyNFA .init))
      ε-grammar
  fun (emptyNFA-strong-equiv w) = initial→the-alg .f fzero w
  inv (emptyNFA-strong-equiv w) = the-alg→initial .f fzero w
  rightInv (emptyNFA-strong-equiv w) _ = refl
  leftInv (emptyNFA-strong-equiv w) p =
    cong (λ a → a w p)
    (initial→initial≡id emptyNFA
      (AlgebraHom-seq emptyNFA initial→the-alg the-alg→initial)
      fzero)

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
          (⊗PathP
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
      (Parse literalNFA (literalNFA .init))
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

-- Disjunction
-- Given two NFAs N and N', accepts a string if and only if
-- the string is accept by N or by N'
module _ (N : NFA {ℓN}) (N' : NFA {ℓN'}) where
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

-- -- Concatenation
-- module _ {ℓN} {Σ₀ : Type ℓ-zero}
--   (N : NFA ℓN Σ₀)
--   (N' : NFA ℓN Σ₀) where

--   open TraceSyntax Σ₀

--   ⊗NFA : NFA ℓN Σ₀
--   Q ⊗NFA .fst = N .Q .fst ⊎ N' .Q .fst
--   Q ⊗NFA .snd = isFinSet⊎ (N .Q) (N' .Q)
--   init ⊗NFA = inl (N .init)
--   isAcc ⊗NFA (inl x) =
--     DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
--   isAcc ⊗NFA (inr x) = N' .isAcc x
--   transition ⊗NFA .fst = N .transition .fst ⊎ N' .transition .fst
--   transition ⊗NFA .snd = isFinSet⊎ (N .transition) (N' .transition)
--   src ⊗NFA (inl x) = inl (N .src x)
--   dst ⊗NFA (inl x) = inl (N .dst x)
--   src ⊗NFA (inr x) = inr (N' .src x)
--   dst ⊗NFA (inr x) = inr (N' .dst x)
--   label ⊗NFA (inl x) = N .label x
--   label ⊗NFA (inr x) = N' .label x
--   ε-transition ⊗NFA .fst =
--     (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
--     (N .ε-transition .fst ⊎ N' .ε-transition .fst)
--   ε-transition ⊗NFA .snd =
--     isFinSet⊎
--       (_ , isFinSetΣ (N .Q)
--         λ x → _ ,
--           isDecProp→isFinSet
--             (N .isAcc x .fst .snd)
--             (N .isAcc x .snd))
--       ((_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
--   ε-src ⊗NFA (inl x) = inl (x .fst)
--   ε-dst ⊗NFA (inl x) = inr (N' .init)
--   ε-src ⊗NFA (inr (inl x)) = inl (N .ε-src x)
--   ε-dst ⊗NFA (inr (inl x)) = inl (N .ε-dst x)
--   ε-src ⊗NFA (inr (inr x)) = inr (N' .ε-src x)
--   ε-dst ⊗NFA (inr (inr x)) = inr (N' .ε-dst x)

--   open Algebra
--   open AlgebraHom

--   private
--     the-N-alg : Algebra N (N .init)
--     the-ℓs the-N-alg _ = ℓN
--     P the-N-alg q-end =
--       ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inl q-end ]
--     nil-case the-N-alg = nil
--     cons-case the-N-alg tr = cons (inl tr)
--     ε-cons-case the-N-alg εtr = ε-cons (inr (inl εtr))

--     initialN→the-N-alg :
--       AlgebraHom
--         N
--         (N .init)
--         (initial N (N .init))
--         (the-N-alg)
--     initialN→the-N-alg = ∃AlgebraHom N (N .init) the-N-alg


--     the-⊗NFA-alg : ∀ q-start → Algebra ⊗NFA q-start
--     the-ℓs (the-⊗NFA-alg (inl q-start)) _ = ℓN
--     the-ℓs (the-⊗NFA-alg (inr q-start)) _ = ℓN
--     P (the-⊗NFA-alg (inl q-start)) (inl q-end) =
--       ⟨ N ⟩[ q-start →* q-end ]
--     P (the-⊗NFA-alg (inl q-start)) (inr q-end) =
--       AcceptingFrom N q-start ⊗ ⟨ N' ⟩[ N' .init →* q-end ]
--     P (the-⊗NFA-alg (inr q-start)) (inl q-end) = ⊥-grammar
--     P (the-⊗NFA-alg (inr q-start)) (inr q-end) =
--       ⟨ N' ⟩[ q-start →* q-end ]
--     nil-case (the-⊗NFA-alg (inl q-start)) = nil
--     nil-case (the-⊗NFA-alg (inr q-start)) = nil
--     cons-case (the-⊗NFA-alg (inl q-start)) (inl tr) = cons tr
--     cons-case (the-⊗NFA-alg (inl q-start)) (inr tr) =
--       ⊗-assoc
--         {g = AcceptingFrom N q-start}
--         {h = ⟨ N' ⟩[ N' .init →* N' .src tr ]}
--         {k = literal (N' .label tr)}
--         {l = AcceptingFrom N q-start ⊗ ⟨ N' ⟩[ N' .init →* N' .dst tr ]}
--         (cut
--           {g = ⟨ N' ⟩[ N' .init →* N' .src tr ] ⊗
--             literal (N' .label tr)}
--           {h = ⟨ N' ⟩[ N' .init →* N' .dst tr ]}
--           (AcceptingFrom N q-start ⊗r var)
--           (cons tr))
--     cons-case (the-⊗NFA-alg (inr q-start)) (inl tr) ()
--     cons-case (the-⊗NFA-alg (inr q-start)) (inr tr) = cons tr
--     ε-cons-case (the-⊗NFA-alg (inl q-start))
--       (inl (q-end , q-endIsAcc)) trace =
--         ((_ , []) , (sym (++-unit-r _))) ,
--         (((q-end , q-endIsAcc) , trace) ,
--         nil refl)
--     ε-cons-case (the-⊗NFA-alg (inl q-start))
--       (inr (inl εtr)) = ε-cons εtr
--     ε-cons-case (the-⊗NFA-alg (inl q-start))
--       (inr (inr εtr)) =
--         cut
--           {g = ⟨ N' ⟩[ N' .init →* N' .ε-src εtr ]}
--           {h = ⟨ N' ⟩[ N' .init →* N' .ε-dst εtr ]}
--           (AcceptingFrom N q-start ⊗r var)
--           (ε-cons εtr)
--     ε-cons-case (the-⊗NFA-alg (inr q-start))
--       (inl (q-end , q-endIsAcc)) ()
--     ε-cons-case (the-⊗NFA-alg (inr q-start))
--       (inr (inl εtr)) ()
--     ε-cons-case (the-⊗NFA-alg (inr q-start))
--       (inr (inr εtr)) = ε-cons εtr

--     initial⊗NFA→the-⊗NFA-alg : ∀ q-start →
--       AlgebraHom
--         ⊗NFA
--         q-start
--         (initial ⊗NFA q-start)
--         (the-⊗NFA-alg q-start)
--     initial⊗NFA→the-⊗NFA-alg q-start =
--       ∃AlgebraHom ⊗NFA q-start (the-⊗NFA-alg q-start)

--     the-N-alg→initialN :
--       AlgebraHom
--         N
--         (N .init)
--         (the-N-alg)
--         (initial N (N .init))
--     f the-N-alg→initialN q-end =
--       initial⊗NFA→the-⊗NFA-alg (inl (N .init)) .f (inl q-end)
--     on-nil the-N-alg→initialN _ = refl
--     on-cons the-N-alg→initialN _ _ = refl
--     on-ε-cons the-N-alg→initialN _ _ = refl

--     the-N'-alg : Algebra N' (N' .init)
--     the-ℓs the-N'-alg _ = ℓN
--     P the-N'-alg q-end =
--       Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ]
--     nil-case the-N'-alg =
--       -⊗-intro
--         {g = Parses N} {h = ε-grammar}
--         {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .init) ]}
--         (ε-extension-r
--           {g = ε-grammar}
--           {h = Parses N}
--           {k = ⟨ ⊗NFA ⟩[ inl (N .init) →* inr (N' .init) ]}
--           (id {g = ε-grammar})
--           (λ (acceptN , traceN) →
--             ε-cons (inl acceptN)
--               (initialN→the-N-alg .f (acceptN .fst) traceN)))
--     cons-case the-N'-alg tr =
--       -⊗-intro
--         {g = Parses N}
--         {h = (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ])
--           ⊗ literal (N' .label tr)}
--         {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .dst tr) ]}
--         (⊗-assoc-inv
--           {g = Parses N}
--         {h = Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]}
--         {k = literal (N' .label tr)}
--         {l = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .dst tr) ]}
--         (trans
--           {g = (Parses N ⊗
--             (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]))
--             ⊗ literal (N' .label tr)}
--           {h = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]
--             ⊗ literal (N' .label tr)}
--           {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .dst tr) ]}
--             (cut
--             {g = Parses N ⊗
--               (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ])}
--             {h = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]}
--             (var ⊗l literal (N' .label tr))
--             (-⊗-elim
--               {g = Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]}
--               {h = Parses N}
--               {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]}
--               {l = Parses N}
--               (id {g = Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]})
--               (id {g = Parses N})))
--             (cons (inr tr))))
--     ε-cons-case the-N'-alg εtr =
--       cut
--         {g = ⟨ ⊗NFA ⟩[ inl (N .init) →* inr (N' .ε-src εtr) ]}
--         {h = ⟨ ⊗NFA ⟩[ inl (N .init) →* inr (N' .ε-dst εtr) ]}
--         (Parses N -⊗OH var)
--         (ε-cons (inr (inr εtr)))

--     initialN'→the-N'-alg :
--       AlgebraHom
--         N'
--         (N' .init)
--         (initial N' (N' .init))
--         (the-N'-alg)
--     initialN'→the-N'-alg = ∃AlgebraHom N' (N' .init) the-N'-alg

--   --   the-N'-alg→initialN' :
--   --     AlgebraHom
--   --       N'
--   --       (N' .init)
--   --       (the-N'-alg)
--   --       (initial N' (N' .init))
--   --   f the-N'-alg→initialN' q-end =
--   --     initial⊗NFA→the-⊗NFA-alg (inr (N' .init)) .f (inr q-end)
--   --   on-nil the-N'-alg→initialN' _ = refl
--   --   on-cons the-N'-alg→initialN' _ _ = refl
--   --   on-ε-cons the-N'-alg→initialN' _ _ = refl

--   --   pls :
--   --     AlgebraHom
--   --       ⊗NFA
--   --       (inr (N' .init))
--   --       (the-⊗NFA-alg (inr (N' .init)))
--   --       (initial ⊗NFA (inr (N' .init)))
--   --   f pls (inr q-end) = initialN'→the-N'-alg .f q-end
--   --   on-nil pls _ = refl
--   --   on-cons pls (inl tr) ()
--   --   on-cons pls (inr tr) p = refl
--   --   on-ε-cons pls (inl _) ()
--   --   on-ε-cons pls (inr (inl ε-tr)) ()
--   --   on-ε-cons pls (inr (inr ε-tr)) _ = refl

--     the-⊗NFA-alg→initial⊗NFA :
--       AlgebraHom
--         ⊗NFA
--         (⊗NFA .init)
--         (the-⊗NFA-alg (⊗NFA .init))
--         (initial ⊗NFA (⊗NFA .init))
--     f the-⊗NFA-alg→initial⊗NFA (inl q-end) =
--       initialN→the-N-alg .f q-end
--     f the-⊗NFA-alg→initial⊗NFA (inr q-end) =
--       trans
--         {g = Parses N ⊗ ⟨ N' ⟩[ N' .init →* q-end ]}
--         {h = Parses N ⊗ (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ])}
--         {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ]}
--         (cut
--           {g = ⟨ N' ⟩[ N' .init →* q-end ]}
--           {h = (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ])}
--           (Parses N ⊗r var)
--           (initialN'→the-N'-alg .f q-end))
--         (-⊗-elim
--           {g = (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ])}
--           {h = Parses N}
--           {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ]}
--           {l = Parses N}
--           (id {g = (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ])})
--           (id {g = Parses N})
--         )
--     on-nil the-⊗NFA-alg→initial⊗NFA _ = refl
--     on-cons the-⊗NFA-alg→initial⊗NFA (inl tr) p = refl
--     on-cons the-⊗NFA-alg→initial⊗NFA (inr tr) =
--       funExt⁻ {!refl!}
--       -- Term≡-cong (initialN'→the-N'-alg .on-cons tr)
--       --   {!!}
--       --   {!!}
--       -- ((s , (s' , (acceptN , traceN) , traceN') , lit)) =
--       -- {!initialN'→the-N'-alg .on-cons tr (? , traceN' , lit)!}
--     on-ε-cons the-⊗NFA-alg→initial⊗NFA
--       (inl (q-endN , isAccq-endN)) p = {!!}
--     on-ε-cons the-⊗NFA-alg→initial⊗NFA (inr (inl εtr)) p = refl
--     on-ε-cons the-⊗NFA-alg→initial⊗NFA (inr (inr εtr)) p = {!!}

--     parse⊗NFA→parseN⊗parseN' :
--       (Parses ⊗NFA)
--       ⊢
--       (Parses N ⊗ Parses N')
--     parse⊗NFA→parseN⊗parseN' ((inr q-end , q-endIsAcc) , trace) =
--       trans
--         {g = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ]}
--         {h = the-⊗NFA-alg (⊗NFA .init) .P (inr q-end)}
--         {k = Parses N ⊗ Parses N'}
--         (initial⊗NFA→the-⊗NFA-alg (⊗NFA .init) .f (inr q-end))
--         (λ (s , parseN , traceN') →
--           s ,
--           (parseN ,
--           ((q-end , q-endIsAcc) , traceN')))
--         trace

--     parseN⊗parseN'→parse⊗NFA :
--       (Parses N ⊗ Parses N')
--       ⊢
--       (Parses ⊗NFA)
--     parseN⊗parseN'→parse⊗NFA
--       (s , (acceptN , traceN) , (acceptN' , traceN')) =
--       ((inr (acceptN' .fst)) , (acceptN' .snd)) ,
--       the-⊗NFA-alg→initial⊗NFA .f (inr (acceptN' .fst))
--         (s , ((acceptN , traceN) , traceN'))

--   open Iso
--   parse⊗NFA≡parseN⊗parseN' :
--     isStronglyEquivalent
--       (Parses ⊗NFA)
--       (Parses N ⊗ Parses N')
--   fun (parse⊗NFA≡parseN⊗parseN' w) = parse⊗NFA→parseN⊗parseN'
--   inv (parse⊗NFA≡parseN⊗parseN' w) = parseN⊗parseN'→parse⊗NFA
--   rightInv (parse⊗NFA≡parseN⊗parseN' w)
--     (s , (acceptN , traceN) , (acceptN' , parseN')) =
--     {!initial→initial≡id ? ? ? ? ?!}
--   leftInv (parse⊗NFA≡parseN⊗parseN' w)
--     (accept⊗NFA , trace⊗NFA) =
--     {!!}

-- -- Kleene Star
-- module _ {ℓN} {Σ₀ : Type ℓ-zero}
--   (N : NFA ℓN Σ₀) where

--   open TraceSyntax Σ₀
--   KL*NFA : NFA ℓN Σ₀
--   Q KL*NFA .fst = N .Q .fst ⊎ ⊤
--   Q KL*NFA .snd = isFinSet⊎ (N .Q) (_ , isFinSetUnit)
--   init KL*NFA = inl (N .init)
--   isAcc KL*NFA (inl x) =
--     DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
--   isAcc KL*NFA (inr x) =
--     DecPropIso .Iso.inv (Unit* , (true , (invEquiv LiftEquiv)))
--   transition KL*NFA = N .transition
--   src KL*NFA x = inl (N .src x)
--   dst KL*NFA x = inl (N .dst x)
--   label KL*NFA = N .label
--   ε-transition KL*NFA .fst =
--     ⊤ ⊎
--     ((Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
--       (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst))
--   ε-transition KL*NFA .snd =
--     isFinSet⊎
--       (_ , isFinSetUnit)
--       (_ , isFinSet⊎
--         (_ , isFinSetAccΣ)
--         (_ , isFinSetAccΣ))
--     where
--     isFinSetAccΣ :
--       isFinSet
--         (Σ-syntax (N .Q .fst) (λ q → N .isAcc q .fst .fst))
--     isFinSetAccΣ =
--       isFinSetΣ (N .Q)
--         (λ x → _ ,
--           isDecProp→isFinSet
--             (N .isAcc x .fst .snd)
--             (N .isAcc x .snd))
--   ε-src KL*NFA (inl x) = inl (N .init)
--   ε-dst KL*NFA (inl x) = inr _
--   ε-src KL*NFA (inr (inl x)) = inl (x .fst)
--   ε-dst KL*NFA (inr (inl x)) = inl (N .init)
--   ε-src KL*NFA (inr (inr x)) = inl (x .fst)
--   ε-dst KL*NFA (inr (inr x)) = inr _

--   open Algebra
--   open AlgebraHom

--   private
--     the-N-alg : Algebra N (N .init)
--     the-ℓs the-N-alg = {!!}
--     P the-N-alg q-end =
--       KL* (Parses N) -⊗ ⟨ KL*NFA ⟩[ inl (N .init) →* inl q-end ]
--     nil-case the-N-alg =
--       {!-⊗-intro {g = KL* (Parses N)}
--         {h = ε-grammar}
--         {k = ⟨ KL*NFA ⟩[ inl (N .init) →* inl (N .init) ]}
--         ?!}
--     cons-case the-N-alg = {!!}
--     ε-cons-case the-N-alg = {!!}
