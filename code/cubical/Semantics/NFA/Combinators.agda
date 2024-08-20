{-# OPTIONS -WnoUnsupportedIndexedMatch --lossy-unification #-}
module Semantics.NFA.Combinators where

open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
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
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Grammar
open import Semantics.DFA
open import Semantics.NFA.Base
open import Semantics.Helper
open import Semantics.Term
open import Semantics.String

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

open NFADefs
open NFA

-- NFA Combinators
-- Empty
module _ {Σ₀ : Type ℓ-zero} where
  open TraceSyntax Σ₀

  emptyNFA : NFA ℓ-zero Σ₀
  Q emptyNFA = Fin 1 , isFinSetFin
  init emptyNFA = fzero
  isAcc emptyNFA x = ((x ≡ fzero) , (isSetFin _ _)) , (discreteFin _ _)
  transition emptyNFA = ⊥ , isFinSetFin
  src emptyNFA ()
  dst emptyNFA ()
  label emptyNFA ()
  ε-transition emptyNFA = ⊥ , isFinSetFin
  ε-src emptyNFA ()
  ε-dst emptyNFA ()

  ε→parse :
    ε-grammar
    ⊢
    Parses emptyNFA
  ε→parse pε = (fzero , refl) , (nil pε)

  open Algebra
  open AlgebraHom
  private
    the-alg : (q-end : emptyNFA .Q .fst) → Algebra emptyNFA q-end
    the-ℓs (the-alg fzero) fzero = ℓ-zero
    P (the-alg fzero) fzero = ε-grammar
    nil-case (the-alg fzero) = id {g = ε-grammar}
    cons-case (the-alg fzero) ()
    ε-cons-case (the-alg fzero) ()

  trace→ε : ∀ q-start q-end →
    ⟨ emptyNFA ⟩[ q-start →* q-end ]
    ⊢
    ε-grammar
  trace→ε fzero fzero =
    recTrace emptyNFA fzero (the-alg fzero) {fzero}

  initial→the-alg : ∀ q-start →
    AlgebraHom emptyNFA q-start
      (initial emptyNFA q-start)
      (the-alg q-start)
  f (initial→the-alg fzero) fzero =
    trace→ε fzero fzero
  on-nil (initial→the-alg fzero) _ = refl
  on-cons (initial→the-alg fzero) ()
  on-ε-cons (initial→the-alg fzero) ()

  parse→ε :
    Parses emptyNFA
    ⊢
    ε-grammar
  parse→ε ((fzero , isAcc-fzero) , trace) =
    trace→ε fzero fzero trace

  nil∘rec :
    ⟨ emptyNFA ⟩[ fzero →* fzero ]
    ⊢
    ⟨ emptyNFA ⟩[ fzero →* fzero ]
  nil∘rec =
    trans {g = ⟨ emptyNFA ⟩[ fzero →* fzero ]}
      {h = ε-grammar}
      {k = ⟨ emptyNFA ⟩[ fzero →* fzero ]}
      (trace→ε fzero fzero)
      nil

  nil∘rec-AlgebraHom :
    AlgebraHom emptyNFA fzero
      (initial emptyNFA fzero)
      (initial emptyNFA fzero)
  f nil∘rec-AlgebraHom fzero = nil∘rec
  on-nil nil∘rec-AlgebraHom p = refl
  on-cons nil∘rec-AlgebraHom ()
  on-ε-cons nil∘rec-AlgebraHom ()

  nil∘rec≡id : Term≡ {g = ⟨ emptyNFA ⟩[ fzero →* fzero ]}
    nil∘rec
    (id {g = ⟨ emptyNFA ⟩[ fzero →* fzero ]})
  nil∘rec≡id p =
    initial→initial≡id emptyNFA fzero
      nil∘rec-AlgebraHom
      fzero p

  open Iso

  parseEmptyNFA≡ε-grammar :
    isStronglyEquivalent
      (Parses emptyNFA)
      ε-grammar
  fun (parseEmptyNFA≡ε-grammar w) = parse→ε
  inv (parseEmptyNFA≡ε-grammar w) = ε→parse
  rightInv (parseEmptyNFA≡ε-grammar w) b = refl
  leftInv (parseEmptyNFA≡ε-grammar w)
    ((fzero , isAcc-q-end) , trace) =
    ΣPathP ((Σ≡Prop (λ x → isSetFin _ _) refl) ,
      nil∘rec≡id trace)

-- Literal
module _ {Σ₀ : Type ℓ-zero}
  (c : Σ₀)
  (isSetΣ₀ : isSet Σ₀) where
  open TraceSyntax Σ₀

  literalNFA : NFA ℓ-zero Σ₀
  Q literalNFA = Fin 2 , isFinSetFin
  init literalNFA = fzero
  isAcc literalNFA x = ((x ≡ fsuc fzero) , (isSetFin _ _)) , (discreteFin _ _)
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
    the-alg : (q-start : literalNFA .Q .fst) →
      Algebra literalNFA q-start
    the-ℓs (the-alg fzero) _ = ℓ-zero
    the-ℓs (the-alg (fsuc fzero)) _ = ℓ-zero
    P (the-alg fzero) fzero = ε-grammar
    P (the-alg fzero) (fsuc fzero) = literal c
    P (the-alg (fsuc fzero)) fzero = ⊥-grammar
    P (the-alg (fsuc fzero)) (fsuc fzero) = ε-grammar
    nil-case (the-alg fzero) = id {g = ε-grammar}
    nil-case (the-alg (fsuc fzero)) = id {g = ε-grammar}
    cons-case (the-alg fzero) fzero =
      ε-extension-l {g = ε-grammar} {h = literal c} {k = literal c}
        (id {g = ε-grammar})
        (id {g = literal c})
    cons-case (the-alg (fsuc fzero)) _ ()
    ε-cons-case (the-alg fzero) ()
    ε-cons-case (the-alg (fsuc fzero)) ()

  c→trace :
    literal c
    ⊢
    ⟨ literalNFA ⟩[ fromℕ 0 →* fromℕ 1 ]
  c→trace =
    ε-contraction-l
      {g = ⟨ literalNFA ⟩[ fromℕ 0 →* fromℕ 0 ]}
      {h = literal c}
      {k = ⟨ literalNFA ⟩[ fromℕ 0 →* fromℕ 1 ]}
      nil
      (cons fzero)

  c→parse :
    literal c
    ⊢
    Parses literalNFA
  c→parse pc = (_ , refl) , (c→trace pc)

  c→trace-AlgebraHom : ∀ q-start →
    AlgebraHom
      literalNFA
      q-start
      (the-alg q-start)
      (initial literalNFA q-start)
  f (c→trace-AlgebraHom fzero) fzero = nil
  f (c→trace-AlgebraHom fzero) (fsuc fzero) =
    ε-contraction-l
      {g = ⟨ literalNFA ⟩[ fromℕ 0 →* fromℕ 0 ]}
      {h = literal c}
      {k = ⟨ literalNFA ⟩[ fromℕ 0 →* fromℕ 1 ]}
      nil
      (cons fzero)
  f (c→trace-AlgebraHom (fsuc fzero)) fzero ()
  f (c→trace-AlgebraHom (fsuc fzero)) (fsuc fzero) = nil
  on-nil (c→trace-AlgebraHom fzero) _ = refl
  on-nil (c→trace-AlgebraHom (fsuc fzero)) _ = refl
  on-cons (c→trace-AlgebraHom fzero) fzero {w} (s , pε , lit) =
    cong (Trace.cons fzero)
      (ΣPathP ((Σ≡Prop (λ _ → isSetString isSetΣ₀ _ _)
        (≡-×
          (sym pε)
          w≡s₁₂)) ,
        ΣPathPProp
          (λ trace → isSetString isSetΣ₀ _ _)
          -- There's gotta be a better way to show this
          (congP (λ i z → NFA.Trace.nil {_}{_}{literalNFA}{fzero}{pε (~ i)} z)
            (isProp→PathP (λ i → isSetString isSetΣ₀ _ _) refl pε))))
      where
      w≡s₁₂ : w ≡ s .fst .snd
      w≡s₁₂ = s .snd ∙ cong (_++ s. fst .snd) pε
  on-cons (c→trace-AlgebraHom (fsuc fzero)) fzero ()
  on-ε-cons (c→trace-AlgebraHom fzero) ()
  on-ε-cons (c→trace-AlgebraHom (fsuc fzero)) ()

  trace→c-AlgebraHom : ∀ q-start →
    AlgebraHom
      literalNFA
      q-start
      (initial literalNFA q-start)
      (the-alg q-start)
  trace→c-AlgebraHom q-start = ∃AlgebraHom literalNFA q-start (the-alg q-start)

  parse→c :
    Parses literalNFA
    ⊢
    literal c
  parse→c ((fzero , q-endIsAcc) , trace) =
    ⊥.rec (fzero≠fone q-endIsAcc)
  parse→c ((fsuc fzero , q-endIsAcc) , trace) =
    trace→c-AlgebraHom fzero .f (fsuc fzero) trace

  c→trace∘trace→c :
    ⟨ literalNFA ⟩[ fzero →* fsuc fzero ]
    ⊢
    ⟨ literalNFA ⟩[ fzero →* fsuc fzero ]
  c→trace∘trace→c =
    (trans
      {g = ⟨ literalNFA ⟩[ fzero →* fsuc fzero ]}
      {h = literal c}
      {k = ⟨ literalNFA ⟩[ fzero →* fsuc fzero ]}
      (trace→c-AlgebraHom fzero .f (fsuc fzero))
      c→trace
    )

  c→trace∘trace→c-AlgebraHom :
    AlgebraHom literalNFA fzero
      (initial literalNFA fzero)
      (initial literalNFA fzero)
  c→trace∘trace→c-AlgebraHom =
    AlgebraHom-seq literalNFA
      fzero
      (trace→c-AlgebraHom fzero)
      (c→trace-AlgebraHom fzero)

  c→trace∘trace→c≡id :
    Term≡ {g = ⟨ literalNFA ⟩[ fzero →* fsuc fzero ]}
      c→trace∘trace→c
      (id {g = ⟨ literalNFA ⟩[ fzero →* fsuc fzero ]})
  c→trace∘trace→c≡id p =
    initial→initial≡id literalNFA fzero
      c→trace∘trace→c-AlgebraHom (fsuc fzero) p

  open Iso

  parse≡c :
    isStronglyEquivalent
      (Parses literalNFA)
      (literal c)
  fun (parse≡c w) = parse→c
  inv (parse≡c w) = c→parse
  rightInv (parse≡c w) b = isSetString isSetΣ₀ _ _ _ _
  leftInv (parse≡c w) ((fzero , q-endIsAcc) , trace) =
    ⊥.rec (fzero≠fone q-endIsAcc)
  leftInv (parse≡c w) ((fsuc fzero , q-endIsAcc) , trace) =
    ΣPathP ((Σ≡Prop (λ x → isSetFin _ _) refl) ,
      c→trace∘trace→c≡id trace)

-- Disjunction
module _ {ℓN} {Σ₀ : Type ℓ-zero}
  (N : NFA ℓN Σ₀)
  (N' : NFA ℓN Σ₀) where

  open TraceSyntax Σ₀

  ⊕NFA : NFA ℓN Σ₀
  NFA.Q ⊕NFA =
    (⊤ ⊎ (N .Q .fst ⊎ N' .Q .fst)) ,
    (isFinSet⊎
      (⊤ , isFinSetUnit)
      ((N .Q .fst ⊎ N' .Q .fst) , (isFinSet⊎ (N .Q) (N' .Q))))
  NFA.init ⊕NFA = inl _
  isAcc ⊕NFA (inl x) = (⊥* , isProp⊥*) , (no lower)
  isAcc ⊕NFA (inr (inl x)) = N .isAcc x
  isAcc ⊕NFA (inr (inr x)) = N' .isAcc x
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
    the-N-alg : Algebra N (N .init)
    the-ℓs the-N-alg _ = ℓN
    P the-N-alg q-end =
      ⟨ ⊕NFA ⟩[ fzero →* inr (inl q-end) ]
    nil-case the-N-alg =
      trans {g = ε-grammar}
        {h = ⟨ ⊕NFA ⟩[ fzero →* fzero ]}
        {k = ⟨ ⊕NFA ⟩[ fzero →* (inr (inl (N .init))) ]}
        nil
        (ε-cons (inl fzero))
    cons-case the-N-alg tr = cons (inl tr)
    ε-cons-case the-N-alg εtr = ε-cons (inr (inl εtr))

    the-N'-alg : Algebra N' (N' .init)
    the-ℓs the-N'-alg _ = ℓN
    P the-N'-alg q-end =
      ⟨ ⊕NFA ⟩[ fzero →* inr (inr q-end) ]
    nil-case the-N'-alg =
      trans {g = ε-grammar}
        {h = ⟨ ⊕NFA ⟩[ fzero →* fzero ]}
        {k = ⟨ ⊕NFA ⟩[ fzero →* (inr (inr (N' .init))) ]}
        nil
        (ε-cons (inl (fsuc fzero)))
    cons-case the-N'-alg tr = cons (inr tr)
    ε-cons-case the-N'-alg εtr = ε-cons (inr (inr εtr))

    the-⊕NFA-alg : (q-start : ⊕NFA .Q .fst) → Algebra ⊕NFA q-start
    the-ℓs (the-⊕NFA-alg fzero) fzero = ℓ-zero
    the-ℓs (the-⊕NFA-alg fzero) (inr (inl q-start)) = ℓN
    the-ℓs (the-⊕NFA-alg fzero) (inr (inr q-start)) = ℓN
    the-ℓs (the-⊕NFA-alg (inr (inl q-start))) _ = ℓN
    the-ℓs (the-⊕NFA-alg (inr (inr q-start))) _ = ℓN
    P (the-⊕NFA-alg fzero) fzero = ε-grammar
    P (the-⊕NFA-alg fzero) (inr (inl (q-end))) =
      ⟨ N ⟩[ N .init →* q-end ]
    P (the-⊕NFA-alg fzero) (inr (inr (q-end))) =
      ⟨ N' ⟩[ N' .init →* q-end ]
    P (the-⊕NFA-alg (inr (inl q-start))) fzero = ⊥-grammar
    P (the-⊕NFA-alg (inr (inl q-start))) (inr (inl (q-end))) =
      ⟨ N ⟩[ q-start →* q-end ]
    P (the-⊕NFA-alg (inr (inl q-start))) (inr (inr (q-end))) = ⊥-grammar
    P (the-⊕NFA-alg (inr (inr q-start))) fzero = ⊥-grammar
    P (the-⊕NFA-alg (inr (inr q-start))) (inr (inl (q-end))) = ⊥-grammar
    P (the-⊕NFA-alg (inr (inr q-start))) (inr (inr (q-end))) =
      ⟨ N' ⟩[ q-start →* q-end ]
    nil-case (the-⊕NFA-alg fzero) = id {g = ε-grammar}
    nil-case (the-⊕NFA-alg (inr (inl q-start))) = nil
    nil-case (the-⊕NFA-alg (inr (inr q-start))) = nil
    cons-case (the-⊕NFA-alg fzero) (inl tr) = cons tr
    cons-case (the-⊕NFA-alg fzero) (inr tr) = cons tr
    cons-case (the-⊕NFA-alg (inr (inl q-start))) (inl tr) = cons tr
    cons-case (the-⊕NFA-alg (inr (inl q-start))) (inr tr) ()
    cons-case (the-⊕NFA-alg (inr (inr q-start))) (inl tr) ()
    cons-case (the-⊕NFA-alg (inr (inr q-start))) (inr tr) = cons tr
    ε-cons-case (the-⊕NFA-alg fzero) (inl fzero) = nil
    ε-cons-case (the-⊕NFA-alg fzero) (inl (inr fzero)) = nil
    ε-cons-case (the-⊕NFA-alg fzero) (inr (inl ε-tr)) = ε-cons ε-tr
    ε-cons-case (the-⊕NFA-alg fzero) (inr (inr ε-tr)) = ε-cons ε-tr
    ε-cons-case (the-⊕NFA-alg (inr (inl q-start))) (inl fzero) ()
    ε-cons-case (the-⊕NFA-alg (inr (inl q-start))) (inl (inr fzero)) ()
    ε-cons-case (the-⊕NFA-alg (inr (inl q-start))) (inr (inl ε-tr)) = ε-cons ε-tr
    ε-cons-case (the-⊕NFA-alg (inr (inl q-start))) (inr (inr ε-tr)) ()
    ε-cons-case (the-⊕NFA-alg (inr (inr q-start))) (inl fzero) ()
    ε-cons-case (the-⊕NFA-alg (inr (inr q-start))) (inl (inr fzero)) ()
    ε-cons-case (the-⊕NFA-alg (inr (inr q-start))) (inr (inl ε-tr)) ()
    ε-cons-case (the-⊕NFA-alg (inr (inr q-start))) (inr (inr ε-tr)) = ε-cons ε-tr

    trace⊕NFA→traceN⊕traceN' : ∀ q-start →
      AlgebraHom
        ⊕NFA
        q-start
        (initial ⊕NFA q-start)
        (the-⊕NFA-alg q-start)
    trace⊕NFA→traceN⊕traceN' q-start =
      ∃AlgebraHom ⊕NFA q-start (the-⊕NFA-alg q-start)

    initialN→the-N-alg :
      AlgebraHom
        N
        (N .init)
        (initial N (N .init))
        (the-N-alg)
    initialN→the-N-alg = ∃AlgebraHom N (N .init) (the-N-alg)

    initialN'→the-N'-alg :
      AlgebraHom
        N'
        (N' .init)
        (initial N' (N' .init))
        (the-N'-alg)
    initialN'→the-N'-alg =
      ∃AlgebraHom N' (N' .init) (the-N'-alg)

    the-N-alg→initialN :
      AlgebraHom
        N
        (N .init)
        (the-N-alg)
        (initial N (N .init))
    f the-N-alg→initialN q-end =
      trace⊕NFA→traceN⊕traceN' fzero .f (inr (inl q-end))
    on-nil the-N-alg→initialN _ = refl
    on-cons the-N-alg→initialN _ _ = refl
    on-ε-cons the-N-alg→initialN _ _ = refl

    the-N'-alg→initialN' :
      AlgebraHom
        N'
        (N' .init)
        (the-N'-alg)
        (initial N' (N' .init))
    f the-N'-alg→initialN' q-end =
      trace⊕NFA→traceN⊕traceN' fzero .f (inr (inr q-end))
    on-nil the-N'-alg→initialN' _ = refl
    on-cons the-N'-alg→initialN' _ _ = refl
    on-ε-cons the-N'-alg→initialN' _ _ = refl

    the-⊕NFA-alg→initial⊕NFA :
      AlgebraHom
        ⊕NFA
        fzero
        (the-⊕NFA-alg fzero)
        (initial ⊕NFA fzero)
    f the-⊕NFA-alg→initial⊕NFA fzero = nil
    f the-⊕NFA-alg→initial⊕NFA (inr (inl q-end)) =
      initialN→the-N-alg .f q-end
    f the-⊕NFA-alg→initial⊕NFA (inr (inr q-end)) =
      initialN'→the-N'-alg .f q-end
    on-nil the-⊕NFA-alg→initial⊕NFA _ = refl
    on-cons the-⊕NFA-alg→initial⊕NFA (inl tr) p = refl
    on-cons the-⊕NFA-alg→initial⊕NFA (inr tr) p = refl
    on-ε-cons the-⊕NFA-alg→initial⊕NFA (inl fzero) p = refl
    on-ε-cons the-⊕NFA-alg→initial⊕NFA (inl (fsuc fzero)) p = refl
    on-ε-cons the-⊕NFA-alg→initial⊕NFA (inr (inl εtr)) p = refl
    on-ε-cons the-⊕NFA-alg→initial⊕NFA (inr (inr εtr)) p = refl

    parseN⊕parseN'→parse⊕NFA :
      Parses N ⊕ Parses N'
      ⊢
      Parses ⊕NFA
    parseN⊕parseN'→parse⊕NFA =
      ⊕-elim
        {g = Parses N} {h = Parses ⊕NFA} {k = Parses N'}
        (λ ((q-end , q-endIsAcc) , trace) →
          ((inr (inl q-end)) , q-endIsAcc) ,
            the-⊕NFA-alg→initial⊕NFA .f (inr (inl q-end)) trace)
        (λ ((q-end , q-endIsAcc) , trace) →
          ((inr (inr q-end)) , q-endIsAcc) ,
            the-⊕NFA-alg→initial⊕NFA .f (inr (inr q-end)) trace)

    parse⊕NFA→parseN⊕parseN' :
      Parses ⊕NFA
      ⊢
      Parses N ⊕ Parses N'
    parse⊕NFA→parseN⊕parseN' ((inr (inl x) , q-endIsAcc) , trace) =
      inl ((x , q-endIsAcc) ,
        trace⊕NFA→traceN⊕traceN' (init ⊕NFA) .f (inr (inl x)) trace
      )
    parse⊕NFA→parseN⊕parseN' ((inr (inr x) , q-endIsAcc) , trace) =
      inr ((x , q-endIsAcc) ,
        trace⊕NFA→traceN⊕traceN' (init ⊕NFA) .f (inr (inr x)) trace
      )

  open Iso
  parse⊕NFA≡parseN⊕parseN' :
    isStronglyEquivalent
      (Parses ⊕NFA)
      (Parses N ⊕ Parses N')
  fun (parse⊕NFA≡parseN⊕parseN' w) =
    parse⊕NFA→parseN⊕parseN'
  inv (parse⊕NFA≡parseN⊕parseN' w) =
    parseN⊕parseN'→parse⊕NFA
  rightInv (parse⊕NFA≡parseN⊕parseN' w)
    (inl ((q-end , q-endIsAcc) , trace)) =
      cong inl (ΣPathP (refl ,
        initial→initial≡id N
          (N .init)
          (AlgebraHom-seq N (N .init)
            initialN→the-N-alg
            the-N-alg→initialN)
          q-end
          trace))
  rightInv (parse⊕NFA≡parseN⊕parseN' w)
    (inr ((q-end , q-endIsAcc) , trace)) =
      cong inr (ΣPathP (refl ,
        initial→initial≡id N'
          (N' .init)
          (AlgebraHom-seq N' (N' .init)
            initialN'→the-N'-alg
            the-N'-alg→initialN')
          q-end
          trace))
  leftInv (parse⊕NFA≡parseN⊕parseN' w)
    ((inr (inl x) , q-endIsAcc) , trace) =
    ΣPathP (refl ,
      initial→initial≡id ⊕NFA
        (init ⊕NFA)
        (AlgebraHom-seq ⊕NFA (init ⊕NFA)
          (trace⊕NFA→traceN⊕traceN' (init ⊕NFA))
          the-⊕NFA-alg→initial⊕NFA)
        (inr (inl x))
        trace)
  leftInv (parse⊕NFA≡parseN⊕parseN' w)
    ((inr (inr x) , q-endIsAcc) , trace) =
    ΣPathP (refl ,
      initial→initial≡id ⊕NFA
        (init ⊕NFA)
        (AlgebraHom-seq ⊕NFA (init ⊕NFA)
          (trace⊕NFA→traceN⊕traceN' (init ⊕NFA))
          the-⊕NFA-alg→initial⊕NFA)
        (inr (inr x))
        trace)

-- Concatenation
module _ {ℓN} {Σ₀ : Type ℓ-zero}
  (N : NFA ℓN Σ₀)
  (N' : NFA ℓN Σ₀) where

  open TraceSyntax Σ₀

  ⊗NFA : NFA ℓN Σ₀
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

  open Algebra
  open AlgebraHom

  private
    the-N-alg : Algebra N (N .init)
    the-ℓs the-N-alg _ = ℓN
    P the-N-alg q-end =
      ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inl q-end ]
    nil-case the-N-alg = nil
    cons-case the-N-alg tr = cons (inl tr)
    ε-cons-case the-N-alg εtr = ε-cons (inr (inl εtr))

    initialN→the-N-alg :
      AlgebraHom
        N
        (N .init)
        (initial N (N .init))
        (the-N-alg)
    initialN→the-N-alg = ∃AlgebraHom N (N .init) the-N-alg


    the-⊗NFA-alg : ∀ q-start → Algebra ⊗NFA q-start
    the-ℓs (the-⊗NFA-alg (inl q-start)) _ = ℓN
    the-ℓs (the-⊗NFA-alg (inr q-start)) _ = ℓN
    P (the-⊗NFA-alg (inl q-start)) (inl q-end) =
      ⟨ N ⟩[ q-start →* q-end ]
    P (the-⊗NFA-alg (inl q-start)) (inr q-end) =
      AcceptingFrom N q-start ⊗ ⟨ N' ⟩[ N' .init →* q-end ]
    P (the-⊗NFA-alg (inr q-start)) (inl q-end) = ⊥-grammar
    P (the-⊗NFA-alg (inr q-start)) (inr q-end) =
      ⟨ N' ⟩[ q-start →* q-end ]
    nil-case (the-⊗NFA-alg (inl q-start)) = nil
    nil-case (the-⊗NFA-alg (inr q-start)) = nil
    cons-case (the-⊗NFA-alg (inl q-start)) (inl tr) = cons tr
    cons-case (the-⊗NFA-alg (inl q-start)) (inr tr) =
      ⊗-assoc
        {g = AcceptingFrom N q-start}
        {h = ⟨ N' ⟩[ N' .init →* N' .src tr ]}
        {k = literal (N' .label tr)}
        {l = AcceptingFrom N q-start ⊗ ⟨ N' ⟩[ N' .init →* N' .dst tr ]}
        (cut
          {g = ⟨ N' ⟩[ N' .init →* N' .src tr ] ⊗
            literal (N' .label tr)}
          {h = ⟨ N' ⟩[ N' .init →* N' .dst tr ]}
          (AcceptingFrom N q-start ⊗r var)
          (cons tr))
    cons-case (the-⊗NFA-alg (inr q-start)) (inl tr) ()
    cons-case (the-⊗NFA-alg (inr q-start)) (inr tr) = cons tr
    ε-cons-case (the-⊗NFA-alg (inl q-start))
      (inl (q-end , q-endIsAcc)) trace =
        ((_ , []) , (sym (++-unit-r _))) ,
        (((q-end , q-endIsAcc) , trace) ,
        nil refl)
    ε-cons-case (the-⊗NFA-alg (inl q-start))
      (inr (inl εtr)) = ε-cons εtr
    ε-cons-case (the-⊗NFA-alg (inl q-start))
      (inr (inr εtr)) =
        cut
          {g = ⟨ N' ⟩[ N' .init →* N' .ε-src εtr ]}
          {h = ⟨ N' ⟩[ N' .init →* N' .ε-dst εtr ]}
          (AcceptingFrom N q-start ⊗r var)
          (ε-cons εtr)
    ε-cons-case (the-⊗NFA-alg (inr q-start))
      (inl (q-end , q-endIsAcc)) ()
    ε-cons-case (the-⊗NFA-alg (inr q-start))
      (inr (inl εtr)) ()
    ε-cons-case (the-⊗NFA-alg (inr q-start))
      (inr (inr εtr)) = ε-cons εtr

    initial⊗NFA→the-⊗NFA-alg : ∀ q-start →
      AlgebraHom
        ⊗NFA
        q-start
        (initial ⊗NFA q-start)
        (the-⊗NFA-alg q-start)
    initial⊗NFA→the-⊗NFA-alg q-start =
      ∃AlgebraHom ⊗NFA q-start (the-⊗NFA-alg q-start)

    the-N-alg→initialN :
      AlgebraHom
        N
        (N .init)
        (the-N-alg)
        (initial N (N .init))
    f the-N-alg→initialN q-end =
      initial⊗NFA→the-⊗NFA-alg (inl (N .init)) .f (inl q-end)
    on-nil the-N-alg→initialN _ = refl
    on-cons the-N-alg→initialN _ _ = refl
    on-ε-cons the-N-alg→initialN _ _ = refl

    the-N'-alg : Algebra N' (N' .init)
    the-ℓs the-N'-alg _ = ℓN
    P the-N'-alg q-end =
      Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ]
    nil-case the-N'-alg =
      -⊗-intro
        {g = Parses N} {h = ε-grammar}
        {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .init) ]}
        (ε-extension-r
          {g = ε-grammar}
          {h = Parses N}
          {k = ⟨ ⊗NFA ⟩[ inl (N .init) →* inr (N' .init) ]}
          (id {g = ε-grammar})
          (λ (acceptN , traceN) →
            ε-cons (inl acceptN)
              (initialN→the-N-alg .f (acceptN .fst) traceN)))
    cons-case the-N'-alg tr =
      -⊗-intro
        {g = Parses N}
        {h = (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ])
          ⊗ literal (N' .label tr)}
        {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .dst tr) ]}
        (⊗-assoc-inv
          {g = Parses N}
        {h = Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]}
        {k = literal (N' .label tr)}
        {l = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .dst tr) ]}
        (trans
          {g = (Parses N ⊗
            (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]))
            ⊗ literal (N' .label tr)}
          {h = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]
            ⊗ literal (N' .label tr)}
          {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .dst tr) ]}
            (cut
            {g = Parses N ⊗
              (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ])}
            {h = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]}
            (var ⊗l literal (N' .label tr))
            (-⊗-elim
              {g = Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]}
              {h = Parses N}
              {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]}
              {l = Parses N}
              (id {g = Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr (N' .src tr) ]})
              (id {g = Parses N})))
            (cons (inr tr))))
    ε-cons-case the-N'-alg εtr =
      cut
        {g = ⟨ ⊗NFA ⟩[ inl (N .init) →* inr (N' .ε-src εtr) ]}
        {h = ⟨ ⊗NFA ⟩[ inl (N .init) →* inr (N' .ε-dst εtr) ]}
        (Parses N -⊗OH var)
        (ε-cons (inr (inr εtr)))

    initialN'→the-N'-alg :
      AlgebraHom
        N'
        (N' .init)
        (initial N' (N' .init))
        (the-N'-alg)
    initialN'→the-N'-alg = ∃AlgebraHom N' (N' .init) the-N'-alg

  --   the-N'-alg→initialN' :
  --     AlgebraHom
  --       N'
  --       (N' .init)
  --       (the-N'-alg)
  --       (initial N' (N' .init))
  --   f the-N'-alg→initialN' q-end =
  --     initial⊗NFA→the-⊗NFA-alg (inr (N' .init)) .f (inr q-end)
  --   on-nil the-N'-alg→initialN' _ = refl
  --   on-cons the-N'-alg→initialN' _ _ = refl
  --   on-ε-cons the-N'-alg→initialN' _ _ = refl

  --   pls :
  --     AlgebraHom
  --       ⊗NFA
  --       (inr (N' .init))
  --       (the-⊗NFA-alg (inr (N' .init)))
  --       (initial ⊗NFA (inr (N' .init)))
  --   f pls (inr q-end) = initialN'→the-N'-alg .f q-end
  --   on-nil pls _ = refl
  --   on-cons pls (inl tr) ()
  --   on-cons pls (inr tr) p = refl
  --   on-ε-cons pls (inl _) ()
  --   on-ε-cons pls (inr (inl ε-tr)) ()
  --   on-ε-cons pls (inr (inr ε-tr)) _ = refl

    the-⊗NFA-alg→initial⊗NFA :
      AlgebraHom
        ⊗NFA
        (⊗NFA .init)
        (the-⊗NFA-alg (⊗NFA .init))
        (initial ⊗NFA (⊗NFA .init))
    f the-⊗NFA-alg→initial⊗NFA (inl q-end) =
      initialN→the-N-alg .f q-end
    f the-⊗NFA-alg→initial⊗NFA (inr q-end) =
      trans
        {g = Parses N ⊗ ⟨ N' ⟩[ N' .init →* q-end ]}
        {h = Parses N ⊗ (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ])}
        {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ]}
        (cut
          {g = ⟨ N' ⟩[ N' .init →* q-end ]}
          {h = (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ])}
          (Parses N ⊗r var)
          (initialN'→the-N'-alg .f q-end))
        (-⊗-elim
          {g = (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ])}
          {h = Parses N}
          {k = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ]}
          {l = Parses N}
          (id {g = (Parses N -⊗ ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ])})
          (id {g = Parses N})
        )
    on-nil the-⊗NFA-alg→initial⊗NFA _ = refl
    on-cons the-⊗NFA-alg→initial⊗NFA (inl tr) p = refl
    on-cons the-⊗NFA-alg→initial⊗NFA (inr tr) =
      funExt⁻ {!refl!}
      -- Term≡-cong (initialN'→the-N'-alg .on-cons tr)
      --   {!!}
      --   {!!}
      -- ((s , (s' , (acceptN , traceN) , traceN') , lit)) =
      -- {!initialN'→the-N'-alg .on-cons tr (? , traceN' , lit)!}
    on-ε-cons the-⊗NFA-alg→initial⊗NFA
      (inl (q-endN , isAccq-endN)) p = {!!}
    on-ε-cons the-⊗NFA-alg→initial⊗NFA (inr (inl εtr)) p = refl
    on-ε-cons the-⊗NFA-alg→initial⊗NFA (inr (inr εtr)) p = {!!}

    parse⊗NFA→parseN⊗parseN' :
      (Parses ⊗NFA)
      ⊢
      (Parses N ⊗ Parses N')
    parse⊗NFA→parseN⊗parseN' ((inr q-end , q-endIsAcc) , trace) =
      trans
        {g = ⟨ ⊗NFA ⟩[ ⊗NFA .init →* inr q-end ]}
        {h = the-⊗NFA-alg (⊗NFA .init) .P (inr q-end)}
        {k = Parses N ⊗ Parses N'}
        (initial⊗NFA→the-⊗NFA-alg (⊗NFA .init) .f (inr q-end))
        (λ (s , parseN , traceN') →
          s ,
          (parseN ,
          ((q-end , q-endIsAcc) , traceN')))
        trace

    parseN⊗parseN'→parse⊗NFA :
      (Parses N ⊗ Parses N')
      ⊢
      (Parses ⊗NFA)
    parseN⊗parseN'→parse⊗NFA
      (s , (acceptN , traceN) , (acceptN' , traceN')) =
      ((inr (acceptN' .fst)) , (acceptN' .snd)) ,
      the-⊗NFA-alg→initial⊗NFA .f (inr (acceptN' .fst))
        (s , ((acceptN , traceN) , traceN'))

  open Iso
  parse⊗NFA≡parseN⊗parseN' :
    isStronglyEquivalent
      (Parses ⊗NFA)
      (Parses N ⊗ Parses N')
  fun (parse⊗NFA≡parseN⊗parseN' w) = parse⊗NFA→parseN⊗parseN'
  inv (parse⊗NFA≡parseN⊗parseN' w) = parseN⊗parseN'→parse⊗NFA
  rightInv (parse⊗NFA≡parseN⊗parseN' w)
    (s , (acceptN , traceN) , (acceptN' , parseN')) =
    {!initial→initial≡id ? ? ? ? ?!}
  leftInv (parse⊗NFA≡parseN⊗parseN' w)
    (accept⊗NFA , trace⊗NFA) =
    {!!}

-- Kleene Star
module _ {ℓN} {Σ₀ : Type ℓ-zero}
  (N : NFA ℓN Σ₀) where

  open TraceSyntax Σ₀
  KL*NFA : NFA ℓN Σ₀
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
    the-N-alg : Algebra N (N .init)
    the-ℓs the-N-alg = {!!}
    P the-N-alg q-end =
      KL* (Parses N) -⊗ ⟨ KL*NFA ⟩[ inl (N .init) →* inl q-end ]
    nil-case the-N-alg =
      {!-⊗-intro {g = KL* (Parses N)}
        {h = ε-grammar}
        {k = ⟨ KL*NFA ⟩[ inl (N .init) →* inl (N .init) ]}
        ?!}
    cons-case the-N-alg = {!!}
    ε-cons-case the-N-alg = {!!}
