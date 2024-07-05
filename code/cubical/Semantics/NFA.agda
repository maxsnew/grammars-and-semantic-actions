{-# OPTIONS -WnoUnsupportedIndexedMatch --lossy-unification #-}
module Semantics.NFA where

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
open import Semantics.Helper
open import Semantics.Term
open import Semantics.String

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

module NFADefs ℓN (Σ₀ : Type ℓ-zero) where
  record NFA : Type (ℓ-suc ℓN) where
    field
      Q : FinSet ℓN
      init : Q .fst
      isAcc : Q .fst → DecProp ℓN
      transition : FinSet ℓN
      src : transition .fst → Q .fst
      dst : transition .fst → Q .fst
      label : transition .fst → Σ₀
      ε-transition : FinSet ℓN
      ε-src : ε-transition .fst → Q .fst
      ε-dst : ε-transition .fst → Q .fst

    decEqQ : Discrete (Q .fst)
    decEqQ = isFinSet→Discrete (Q .snd)

    acc? : Q .fst → Grammar {Σ₀} ℓN
    acc? q = DecProp-grammar' {ℓG = ℓN} (isAcc q)

    rej? : Q .fst → Grammar {Σ₀} ℓN
    rej? q = DecProp-grammar' {ℓG = ℓN} (negateDecProp (isAcc q))

    module _ (q-start : Q .fst) where
      data Trace : (q-end : Q .fst) → Grammar ℓN where
        nil : ε-grammar ⊢ Trace q-start
        cons : ∀ tr →
          Trace (src tr) ⊗ literal (label tr) ⊢ Trace (dst tr)
        ε-cons : ∀ εtr →
          Trace (ε-src εtr) ⊢ Trace (ε-dst εtr)

      record Algebra : Typeω where
        field
          the-ℓs : Q .fst → Level
          P : (q-end : Q .fst) → Grammar {Σ₀} (the-ℓs q-end)
          nil-case : ε-grammar ⊢ P q-start
          cons-case : ∀ tr →
            P (src tr) ⊗ literal (label tr) ⊢ P (dst tr)
          ε-cons-case : ∀ εtr →
            P (ε-src εtr) ⊢ P (ε-dst εtr)

      open Algebra

      record AlgebraHom (alg alg' : Algebra) : Typeω where
        field
          f : (q-end : Q .fst) → alg .P q-end ⊢ alg' .P q-end
          on-nil :
            Term≡ {g = ε-grammar}
              (trans {g = ε-grammar}
                (alg .nil-case)
                (f q-start))
              (alg' .nil-case)
          on-cons : (tr : transition .fst) →
            Term≡ {g = alg .P (src tr) ⊗ literal (label tr)}
              (trans {g = alg .P (src tr) ⊗ literal (label tr)}
                (alg .cons-case tr)
                (f (dst tr)))
              (trans {g = alg .P (src tr) ⊗ literal (label tr)}
                (cut {g = alg .P (src tr)} {h = alg' .P (src tr)}
                  (var ⊗l literal (label tr))
                  (f (src tr)))
                (alg' .cons-case tr))
          on-ε-cons : (εtr : ε-transition .fst) →
            Term≡ {g = alg .P (ε-src εtr)}
              (trans {g = alg .P (ε-src εtr)}
                (alg .ε-cons-case εtr)
                (f (ε-dst εtr)))
              (trans {g = alg .P (ε-src εtr)}
                (f (ε-src εtr))
                (alg' .ε-cons-case εtr))

      open AlgebraHom

      idAlgebraHom : (alg : Algebra) →
        AlgebraHom alg alg
      f (idAlgebraHom alg) q-start =
        id {g = alg .P q-start}
      on-nil (idAlgebraHom alg) _ = refl
      on-cons (idAlgebraHom alg) _ _ = refl
      on-ε-cons (idAlgebraHom alg) _ _ = refl

      AlgebraHom-seq : {alg alg' alg'' : Algebra} →
        AlgebraHom alg alg' → AlgebraHom alg' alg'' →
        AlgebraHom alg alg''
      f (AlgebraHom-seq ϕ ψ) q-end x =
        ψ .f q-end (ϕ .f q-end x)
      on-nil (AlgebraHom-seq ϕ ψ) p =
        cong (ψ .f q-start) (ϕ .on-nil p) ∙
        (ψ .on-nil p)
      on-cons (AlgebraHom-seq ϕ ψ) tr (s , p , lit) =
        cong (ψ .f (dst tr)) (ϕ .on-cons tr (s , p , lit)) ∙
        (ψ .on-cons tr (s , (ϕ .f (src tr) p) , lit))
      on-ε-cons (AlgebraHom-seq ϕ ψ) εtr p =
        cong (ψ .f (ε-dst εtr)) (ϕ .on-ε-cons εtr p) ∙
        ψ .on-ε-cons εtr (ϕ .f (ε-src εtr) p)

      initial : Algebra
      the-ℓs initial _ = ℓN
      P initial = Trace
      nil-case initial = nil
      cons-case initial = cons
      ε-cons-case initial = ε-cons

      module _
        (the-alg : Algebra)
        where
        recTrace : ∀ {q-end} → Trace q-end ⊢ the-alg .P q-end
        recTrace (nil x) = the-alg .nil-case x
        recTrace (cons tr x) =
          the-alg .cons-case tr ((x .fst) ,
            ((recTrace (x .snd .fst)) , (x .snd .snd)))
        recTrace (ε-cons εtr x) = the-alg .ε-cons-case εtr (recTrace x)
        -- the-alg .ε-cons εtr (recTrace x)

        ∃AlgebraHom : AlgebraHom initial the-alg
        f ∃AlgebraHom q-end = recTrace {q-end}
        on-nil ∃AlgebraHom p = refl
        on-cons ∃AlgebraHom tr p = refl
        on-ε-cons ∃AlgebraHom εtr p = refl

        !AlgebraHom :
          (e : AlgebraHom initial the-alg) →
          (q-end : Q .fst) →
          Term≡ {g = Trace q-end} (e .f q-end) recTrace
        !AlgebraHom e q-start (nil x) = e .on-nil x
        !AlgebraHom e .(dst tr) (cons tr x) =
          e .on-cons tr x ∙
            cong (λ a → the-alg .cons-case tr (x .fst , a , x .snd .snd))
              (!AlgebraHom e (src tr) (x .snd .fst))
        !AlgebraHom e .(ε-dst εtr) (ε-cons εtr p) =
          e .on-ε-cons εtr p ∙
          cong (λ a → the-alg .ε-cons-case εtr a)
            (!AlgebraHom e (ε-src εtr) p)

      initial→initial≡id :
        (e : AlgebraHom initial initial) →
        (q-end : Q .fst) →
        Term≡ {g = Trace q-end}
          (e .f q-end)
          (idAlgebraHom initial .f q-end)
      initial→initial≡id e q-end p =
        !AlgebraHom initial e q-end p ∙
        sym
          (!AlgebraHom initial (idAlgebraHom initial) q-end p)

    Trace-syntax : Q .fst → Q .fst → Grammar ℓN
    Trace-syntax q-start q-end = Trace q-start q-end
    syntax Trace-syntax q-start q-end = [ q-start →* q-end ]

    module _ (q-start q-mid : Q .fst) where
      open Algebra
      the-concat-alg : Algebra q-mid
      the-ℓs the-concat-alg _ = ℓN
      P the-concat-alg q-end = [ q-start →* q-mid ] -⊗ [ q-start →* q-end ]
      nil-case the-concat-alg =
        -⊗-intro {g = [ q-start →* q-mid ]} {h = ε-grammar}
          {k = [ q-start →* q-mid ]}
          (ε-extension-r {g = ε-grammar} {h = [ q-start →* q-mid ]}
            {k = [ q-start →* q-mid ]}
            (id {g = ε-grammar})
            (id {g = [ q-start →* q-mid ]}))
      cons-case the-concat-alg tr =
        -⊗-intro {g = [ q-start →* q-mid ]}
          {h = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ]) ⊗ literal (label tr)}
          {k = [ q-start →* dst tr ]}
          (⊗-assoc-inv {g = [ q-start →* q-mid ]}
            {h = [ q-start →* q-mid ] -⊗ [ q-start →* src tr ]}
            {k = literal (label tr)}
            {l = [ q-start →* dst tr ]}
            (trans
              {g = ([ q-start →* q-mid ] ⊗
                ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ]))
                ⊗ literal (label tr)}
              {h = [ q-start →* src tr ] ⊗ literal (label tr)}
              {k = [ q-start →* dst tr ]}
              (cut
                {g = [ q-start →* q-mid ] ⊗
                  ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])}
                {h = [ q-start →* src tr ]}
                (var ⊗l literal (label tr))
                (-⊗-elim {g = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])}
                  {h = [ q-start →* q-mid ]} {k = [ q-start →* src tr ]}
                  {l = [ q-start →* q-mid ]}
                  (id {g = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])} )
                  (id {g = [ q-start →* q-mid ]})))
              (cons tr)))
      ε-cons-case the-concat-alg εtr =
        cut {g = [ q-start →* ε-src εtr ]}
          {h = [ q-start →* ε-dst εtr ]}
          ([ q-start →* q-mid ] -⊗OH var)
          (ε-cons εtr)

    open AlgebraHom
    concatTrace : ∀ {q-start}{q-mid}{q-end} →
      [ q-start →* q-mid ] ⊗ [ q-mid →* q-end ] ⊢ [ q-start →* q-end ]
    concatTrace {q-start}{q-mid}{q-end} =
      -⊗-elim
       {g = [ q-mid →* q-end ]}
       {h = [ q-start →* q-mid ]} {k = [ q-start →* q-end ]}
       {l = [ q-start →* q-mid ]}
       (∃AlgebraHom q-mid (the-concat-alg q-start q-mid) .f q-end)
       (id {g = [ q-start →* q-mid ]})

    module _ (q-start : Q .fst) where
      TraceFrom : Grammar ℓN
      TraceFrom = LinearΣ (λ (q-end : Q .fst) → [ q-start →* q-end ])

      AcceptingFrom : Grammar ℓN
      AcceptingFrom =
        LinearΣ
          (λ ((q-end , isAcc-q-end ): Σ[ q ∈ Q .fst ] isAcc q .fst .fst) →
             [ q-start →* q-end ])

    Parses : Grammar ℓN
    Parses = AcceptingFrom init

open NFADefs
open NFA

module TraceSyntax (Σ₀ : Type ℓ-zero) where

  Trace-syntax' : ∀ {ℓN} →
    (N : NFA ℓN Σ₀) →
    Q N .fst → Q N .fst → Grammar ℓN
  Trace-syntax' N = Trace N
  syntax Trace-syntax' N q-start q-end = ⟨ N ⟩[ q-start →* q-end ]

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
    the-N-alg : (q-start : N .Q .fst) → Algebra N q-start
    the-ℓs (the-N-alg q-start) _ = ℓN
    P (the-N-alg q-start) q-end =
      ⟨ ⊕NFA ⟩[ inr (inl q-start) →* inr (inl q-end) ]
    nil-case (the-N-alg q-start) = nil
    cons-case (the-N-alg q-start) tr = cons (inl tr)
    ε-cons-case (the-N-alg q-start) εtr = ε-cons (inr (inl εtr))

    the-N'-alg : (q-start : N' .Q .fst) → Algebra N' q-start
    the-ℓs (the-N'-alg q-start) _ = ℓN
    P (the-N'-alg q-start) q-end =
      ⟨ ⊕NFA ⟩[ inr (inr q-start) →* inr (inr q-end) ]
    nil-case (the-N'-alg q-start) = nil
    cons-case (the-N'-alg q-start) tr = cons (inr tr)
    ε-cons-case (the-N'-alg q-start) εtr = ε-cons (inr (inr εtr))

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
  trace⊕NFA→traceN⊕traceN' q-start = ∃AlgebraHom ⊕NFA q-start (the-⊕NFA-alg q-start)

  initialN→the-N-alg : ∀ q-start →
    AlgebraHom
      N
      q-start
      (initial N q-start)
      (the-N-alg q-start)
  initialN→the-N-alg q-start = ∃AlgebraHom N q-start (the-N-alg q-start)

  initialN'→the-N'-alg : ∀ q-start →
    AlgebraHom
      N'
      q-start
      (initial N' q-start)
      (the-N'-alg q-start)
  initialN'→the-N'-alg q-start = ∃AlgebraHom N' q-start (the-N'-alg q-start)

  the-N-alg→initialN : ∀ q-start →
    AlgebraHom
      N
      q-start
      (the-N-alg q-start)
      (initial N q-start)
  f (the-N-alg→initialN q-start) q-end =
    trace⊕NFA→traceN⊕traceN'
      (inr (inl q-start)) .f (inr (inl q-end))
  on-nil (the-N-alg→initialN q-start) _ = refl
  on-cons (the-N-alg→initialN q-start) _ _ = refl
  on-ε-cons (the-N-alg→initialN q-start) _ _ = refl

  the-N'-alg→initialN' : ∀ q-start →
    AlgebraHom
      N'
      q-start
      (the-N'-alg q-start)
      (initial N' q-start)
  f (the-N'-alg→initialN' q-start) q-end =
    trace⊕NFA→traceN⊕traceN'
      (inr (inr q-start)) .f (inr (inr q-end))
  on-nil (the-N'-alg→initialN' q-start) _ = refl
  on-cons (the-N'-alg→initialN' q-start) _ _ = refl
  on-ε-cons (the-N'-alg→initialN' q-start) _ _ = refl

  the-⊕NFA-alg→initial⊕NFA : ∀ q-start →
    AlgebraHom
      ⊕NFA
      q-start
      (the-⊕NFA-alg q-start)
      (initial ⊕NFA q-start)
  f (the-⊕NFA-alg→initial⊕NFA fzero) fzero = nil
  f (the-⊕NFA-alg→initial⊕NFA fzero) (inr (inl q-end)) =
    trans
     {g = ⟨ N ⟩[ N .init →* q-end ]}
     {h = ⟨ ⊕NFA ⟩[ inr (inl (N .init)) →* inr (inl q-end) ]}
     {k = ⟨ ⊕NFA ⟩[ ⊕NFA .init →* inr (inl q-end) ]}
     (initialN→the-N-alg (N .init) .f q-end)
     (ε-contraction-l {g = ⟨ ⊕NFA ⟩[ fzero →* fzero ]}
       {h = ⟨ ⊕NFA ⟩[ inr (inl (N .init)) →* inr (inl q-end) ]}
       {k = ⟨ ⊕NFA ⟩[ fzero →* inr (inl q-end) ]}
       nil
       (trans
         {g = ⟨ ⊕NFA ⟩[ fzero →* fzero ] ⊗
          ⟨ ⊕NFA ⟩[ inr (inl (N .init)) →* inr (inl q-end) ]}
         {h = ⟨ ⊕NFA ⟩[ fzero →* (inr (inl (N .init))) ] ⊗
          ⟨ ⊕NFA ⟩[ inr (inl (N .init)) →* inr (inl q-end) ]}
         {k = ⟨ ⊕NFA ⟩[ fzero →* (inr (inl q-end)) ]}
         (cut
           {g = ⟨ ⊕NFA ⟩[ fzero →* fzero ]}
           {h = ⟨ ⊕NFA ⟩[ fzero →* (inr (inl (N .init))) ]}
           (var ⊗l ⟨ ⊕NFA ⟩[ inr (inl (N .init)) →* inr (inl q-end)])
           (ε-cons (inl fzero))
           )
         (concatTrace ⊕NFA {fzero} {inr (inl (N .init))} {inr (inl q-end)})
          )
       )
  f (the-⊕NFA-alg→initial⊕NFA fzero) (inr (inr q-end)) =
    trans
     {g = ⟨ N' ⟩[ N' .init →* q-end ]}
     {h = ⟨ ⊕NFA ⟩[ inr (inr (N' .init)) →* inr (inr q-end) ]}
     {k = ⟨ ⊕NFA ⟩[ ⊕NFA .init →* inr (inr q-end) ]}
     (initialN'→the-N'-alg (N' .init) .f q-end)
     (ε-contraction-l {g = ⟨ ⊕NFA ⟩[ fzero →* fzero ]}
       {h = ⟨ ⊕NFA ⟩[ inr (inr (N' .init)) →* inr (inr q-end) ]}
       {k = ⟨ ⊕NFA ⟩[ fzero →* inr (inr q-end) ]}
       nil
       (trans
         {g = ⟨ ⊕NFA ⟩[ fzero →* fzero ] ⊗
          ⟨ ⊕NFA ⟩[ inr (inr (N' .init)) →* inr (inr q-end) ]}
         {h = ⟨ ⊕NFA ⟩[ fzero →* (inr (inr (N' .init))) ] ⊗
          ⟨ ⊕NFA ⟩[ inr (inr (N' .init)) →* inr (inr q-end) ]}
         {k = ⟨ ⊕NFA ⟩[ fzero →* (inr (inr q-end)) ]}
         (cut
           {g = ⟨ ⊕NFA ⟩[ fzero →* fzero ]}
           {h = ⟨ ⊕NFA ⟩[ fzero →* (inr (inr (N' .init))) ]}
           (var ⊗l ⟨ ⊕NFA ⟩[ inr (inr (N' .init)) →* inr (inr q-end)])
           (ε-cons (inl (fsuc fzero)))
           )
         (concatTrace ⊕NFA {fzero} {inr (inr (N' .init))} {inr (inr q-end)})
          )
       )
  f (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) fzero ()
  f (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) (inr (inl q-end)) =
    initialN→the-N-alg q-start .f q-end
  f (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) (inr (inr q-end)) ()
  f (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) fzero ()
  f (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) (inr (inl q-end)) ()
  f (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) (inr (inr q-end)) =
    initialN'→the-N'-alg q-start .f q-end
  on-nil (the-⊕NFA-alg→initial⊕NFA fzero) _ = refl
  on-nil (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) p = refl
  on-nil (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) p = refl
  on-cons (the-⊕NFA-alg→initial⊕NFA fzero) (inl tr) p = {!!}
  on-cons (the-⊕NFA-alg→initial⊕NFA fzero) (inr tr) p = {!!}
  on-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) (inl tr) p = refl
  on-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) (inr tr) p = {!!}
  on-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) (inl tr) p = {!!}
  on-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) (inr tr) p = refl
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA fzero) (inl fzero) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA fzero) (inl (fsuc fzero)) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA fzero) (inr (inl εtr)) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA fzero) (inr (inr εtr)) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) (inl fzero) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) (inl (fsuc fzero)) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) (inr (inl εtr)) p = refl
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (inl q-start))) (inr (inr εtr)) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) (inl fzero) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) (inl (fsuc fzero)) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) (inr (inl εtr)) p = {!!}
  on-ε-cons (the-⊕NFA-alg→initial⊕NFA (fsuc (fsuc q-start))) (inr (inr εtr)) p = refl


--   parseN⊕parseN'→parse⊕NFA :
--     Parses N ⊕ Parses N'
--     ⊢
--     Parses ⊕NFA
--   parseN⊕parseN'→parse⊕NFA =
--     ⊕-elim
--       {g = Parses N} {h = Parses ⊕NFA} {k = Parses N'}
--       (λ ((q-end , q-endIsAcc) , trace) →
--         ((inr (inl q-end)) , q-endIsAcc) ,
--         (ε-cons (inl fzero)
--           (traceN→trace⊕NFA (N .init) q-end trace)))
--       (λ ((q-end , q-endIsAcc) , trace) →
--         ((inr (inr q-end)) , q-endIsAcc) ,
--         ε-cons (inl (inr fzero))
--           (traceN'→trace⊕NFA (N' .init) q-end trace)
--       )

--   parse⊕NFA→parseN⊕parseN' :
--     Parses ⊕NFA
--     ⊢
--     Parses N ⊕ Parses N'
--   parse⊕NFA→parseN⊕parseN' ((inr (inl x) , q-endIsAcc) , trace) =
--     inl ((x , q-endIsAcc) ,
--       (trace⊕NFA→traceN⊕traceN' fzero ((inr (inl x))) trace))
--   parse⊕NFA→parseN⊕parseN' ((inr (inr x) , q-endIsAcc) , trace) =
--     inr ((x , q-endIsAcc) ,
--       (trace⊕NFA→traceN⊕traceN' fzero ((inr (inr x))) trace))

-- -- Goal: ε-cons (inl (fsuc fzero))
-- --       (elimNFA N' x (the-N'-alg x)
-- --        (elimNFA ⊕NFA (fsuc (fsuc x)) (the-alg (fsuc (fsuc x))) trace))
-- --       ≡ trace

-- -- Goal: ε-cons (inl fzero)
-- --       (elimNFA N x (the-N-alg x)
-- --        (elimNFA ⊕NFA (fsuc (inl x)) (the-alg (fsuc (inl x))) trace))
-- --       ≡ trace

--   initial⊕NFA→initial⊕NFA : ∀ q-end →
--     NFATrace-AlgHom ⊕NFA (inr (inl q-end))
--       (initialAlg ⊕NFA (inr (inl q-end)))
--       (initialAlg ⊕NFA (inr (inl q-end)))
--   f (initial⊕NFA→initial⊕NFA q-end) fzero =
--     id {g = ⟨ ⊕NFA ⟩[ ⊕NFA .init →* inr (inl q-end) ]}
--   f (initial⊕NFA→initial⊕NFA q-end) (inr (inl q-start)) =
--     {!!}
--     -- id {g = ⟨ ⊕NFA ⟩[ inr (inl q-start) →* inr (inl q-end) ]}
--   f (initial⊕NFA→initial⊕NFA q-end) (inr (inr q-start)) = {!!}
--   on-nil (initial⊕NFA→initial⊕NFA q-end) = {!!}
--   on-cons (initial⊕NFA→initial⊕NFA q-end) = {!!}
--   on-ε-cons (initial⊕NFA→initial⊕NFA q-end) = {!!}

--   N-Alg-⊕NFA' : ∀ q-end → NFATrace-Alg ⊕NFA (inr (inl q-end))
--   the-ℓs (N-Alg-⊕NFA' q-end) fzero = ℓN
--   the-ℓs (N-Alg-⊕NFA' q-end) (inr (inl q-start)) = ℓN
--   the-ℓs (N-Alg-⊕NFA' q-end) (inr (inr q-start)) = ℓN
--   P (N-Alg-⊕NFA' q-end) fzero = ⟨ N ⟩[ N .init →* q-end ]
--   P (N-Alg-⊕NFA' q-end) (inr (inl q-start)) = ⟨ N ⟩[ q-start →* q-end ]
--   P (N-Alg-⊕NFA' q-end) (inr (inr q-start)) = ⊥-grammar
--   nil-case (N-Alg-⊕NFA' q-end) = nil
--   cons-case (N-Alg-⊕NFA' q-end) (inl tr) = cons tr
--   cons-case (N-Alg-⊕NFA' q-end) (inr tr) ()
--   ε-cons-case (N-Alg-⊕NFA' q-end) (inl fzero) =
--     id {g = ⟨ N ⟩[ N .init →* q-end ]}
--   ε-cons-case (N-Alg-⊕NFA' q-end) (inl (fsuc fzero)) ()
--   ε-cons-case (N-Alg-⊕NFA' q-end) (inr (inl εtr)) = ε-cons εtr
--   ε-cons-case (N-Alg-⊕NFA' q-end) (inr (inr εtr)) ()

--   initial⊕NFA→N-Alg-⊕NFA' : ∀ q-end →
--     NFATrace-AlgHom ⊕NFA (inr (inl q-end))
--       (initialAlg ⊕NFA (inr (inl q-end)))
--       (N-Alg-⊕NFA' q-end)
--   initial⊕NFA→N-Alg-⊕NFA' q-end =
--     ∃AlgHom ⊕NFA (inr (inl q-end)) (N-Alg-⊕NFA' q-end)

--   -- TODO need to refactor this so that i use ε-cons and get a
--   -- trace beginning at ⊕NFA .init
--   N-Alg-⊕NFA'→initial⊕NFA : ∀ q-end →
--     NFATrace-AlgHom ⊕NFA (inr (inl q-end))
--       (N-Alg-⊕NFA' q-end)
--       (initialAlg ⊕NFA (inr (inl q-end)))
--   f (N-Alg-⊕NFA'→initial⊕NFA q-end) fzero =
--     trans {g = ⟨ N ⟩[ N .init →* q-end ]}
--       {h = ⟨ ⊕NFA ⟩[ inr (inl (N .init)) →* inr (inl q-end) ]}
--       {k = ⟨ ⊕NFA ⟩[ ⊕NFA .init →* inr (inl q-end) ]}
--       (traceN→trace⊕NFA (N .init) q-end)
--       (ε-cons (inl fzero))
--   f (N-Alg-⊕NFA'→initial⊕NFA q-end) (inr (inl q-start)) =
--     traceN→trace⊕NFA q-start q-end
--   f (N-Alg-⊕NFA'→initial⊕NFA q-end) (inr (inr q-start)) ()
--   on-nil (N-Alg-⊕NFA'→initial⊕NFA q-end) _ = refl
--   on-cons (N-Alg-⊕NFA'→initial⊕NFA q-end) tr (s , lit , p) = {!!}
--   on-ε-cons (N-Alg-⊕NFA'→initial⊕NFA q-end) εtr p = {!!}

--   initial⊕NFA→initial⊕NFA-N : ∀ q-end →
--     NFATrace-AlgHom ⊕NFA (inr (inl q-end))
--       (initialAlg ⊕NFA (inr (inl q-end)))
--       (initialAlg ⊕NFA (inr (inl q-end)))
--   initial⊕NFA→initial⊕NFA-N q-end =
--     NFATrace-AlgHom-seq ⊕NFA (inr (inl q-end))
--       (initial⊕NFA→N-Alg-⊕NFA' q-end)
--       (N-Alg-⊕NFA'→initial⊕NFA q-end)

--   initial⊕NFA→initial⊕NFA-N≡id : ∀ q-start q-end →
--     Term≡ {g = ⟨ ⊕NFA ⟩[ inr (inl q-start) →* inr (inl q-end) ]}
--       (initial⊕NFA→initial⊕NFA q-end .f (inr (inl q-start)))
--       (id {g = ⟨ ⊕NFA ⟩[ inr (inl q-start) →* inr (inl q-end) ]})
--   initial⊕NFA→initial⊕NFA-N≡id q-start q-end =
--     initialAlg→initialAlg≡id ⊕NFA (inr (inl q-end))
--       (initial⊕NFA→initial⊕NFA q-end) (inr (inl q-start))

--   parse⊕NFA≡parseN⊕parseN' :
--     isStronglyEquivalent
--       (Parses ⊕NFA)
--       (Parses N ⊕ Parses N')
--   Iso.fun (parse⊕NFA≡parseN⊕parseN' w) = parse⊕NFA→parseN⊕parseN'
--   Iso.inv (parse⊕NFA≡parseN⊕parseN' w) = parseN⊕parseN'→parse⊕NFA
--   Iso.rightInv (parse⊕NFA≡parseN⊕parseN' w)
--     (inl ((q-end , q-endIsAcc) , trace)) =
--       cong inl
--         (ΣPathP (refl , (initialN→initialN≡id (init N) q-end trace)))
--   Iso.rightInv (parse⊕NFA≡parseN⊕parseN' w)
--     (inr ((q-end , q-endIsAcc) , trace)) =
--       cong inr
--         (ΣPathP (refl , (initialN'→initialN'≡id (init N') q-end trace)))
--   Iso.leftInv (parse⊕NFA≡parseN⊕parseN' w)
--     ((inr (inl x) , q-endIsAcc) , trace) =
--       ΣPathP (refl ,
--         {!initial⊕NFA→initial⊕NFA-N≡id (N .init) x!})
--   Iso.leftInv (parse⊕NFA≡parseN⊕parseN' w)
--     ((inr (inr x) , q-endIsAcc) , trace) =
--       ΣPathP (refl , {!!})

-- -- -- --   pN⊕pN'→p⊕NFA :
-- -- -- --     (Parses N ⊕ Parses N')
-- -- -- --     ⊢
-- -- -- --     Parses ⊕NFA
-- -- -- --   pN⊕pN'→p⊕NFA =
-- -- -- --     ⊕-elim {g = Parses N} {h = Parses ⊕NFA} {k = Parses N'}
-- -- -- --       (λ ((q-end , isAcc-q-end) , traceN) →
-- -- -- --         (inr (inl q-end) ,
-- -- -- --         LiftDecPropWitness (N .isAcc q-end) isAcc-q-end) ,
-- -- -- --         ε-cons (inl (inl _)) (traceN→trace⊕NFA (N .init) q-end traceN))
-- -- -- --       (λ ((q-end , isAcc-q-end) , traceN') →
-- -- -- --         (inr (inr q-end) ,
-- -- -- --         LiftDecPropWitness (N' .isAcc q-end) isAcc-q-end) ,
-- -- -- --         ε-cons (inl (inr (inl _))) (traceN'→trace⊕NFA (N' .init) q-end traceN'))

-- -- -- -- --   private
-- -- -- -- --   -- TODO there shouldn't need to be lifts here
-- -- -- -- --     the-P : ⊕NFA .Q .fst → Grammar (ℓ-max ℓΣ₀ (ℓ-max (ℓ-suc ℓN) (ℓ-suc ℓN'))) {Σ₀}
-- -- -- -- --     the-P (inl x) =
-- -- -- -- --       ε-grammar {ℓG = ℓ-max (ℓ-max ℓΣ₀ (ℓ-suc ℓN)) (ℓ-suc ℓN')}
-- -- -- -- --     the-P (inr (inl x)) =
-- -- -- -- --       LiftGrammar {ℓG = ℓ-max ℓΣ₀ (ℓ-suc ℓN)}{ℓ-max ℓΣ₀ (ℓ-max (ℓ-suc ℓN) (ℓ-suc ℓN'))}
-- -- -- -- --       ⟨ N ⟩Cons[ N .init →* x ]
-- -- -- -- --     the-P (inr (inr x)) =
-- -- -- -- --       LiftGrammar {ℓG = ℓ-max ℓΣ₀ (ℓ-suc ℓN')}{ℓ-max ℓΣ₀ (ℓ-max (ℓ-suc ℓN) (ℓ-suc ℓN'))}
-- -- -- -- --       ⟨ N' ⟩Cons[ N' .init →* x ]

-- -- -- -- --     the-cons-case : (tr : ⊕NFA .transition .fst) →
-- -- -- -- --       the-P (src ⊕NFA tr) ⊗ literal {ℓG = ℓ-max ℓN (ℓ-max ℓN' ℓΣ₀)} (label ⊕NFA tr)
-- -- -- -- --       ⊢
-- -- -- -- --       the-P (dst ⊕NFA tr)
-- -- -- -- --     the-cons-case (inl x) =
-- -- -- -- --       trans
-- -- -- -- --        {g =
-- -- -- -- --         LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) (N .src x)) ⊗
-- -- -- -- --         literal (N .label x)}
-- -- -- -- --        {h =
-- -- -- -- --         ConsNFATrace-syntax-rebind N (N .init) (N .src x) ⊗ literal {ℓG = ℓ-max ℓN (ℓ-max ℓN' ℓΣ₀)} (N .label x)}
-- -- -- -- --        {k =
-- -- -- -- --         LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) (N .dst x))}
-- -- -- -- --        (cut
-- -- -- -- --          {g =
-- -- -- -- --           LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) (N .src x))}
-- -- -- -- --          {h = ConsNFATrace-syntax-rebind N (N .init) (N .src x)}
-- -- -- -- --          (var ⊗l literal (N .label x))
-- -- -- -- --          (LowerGrammarTerm {g = (ConsNFATrace-syntax-rebind N (N .init) (N .src x))}))
-- -- -- -- --        (trans
-- -- -- -- --          {g =
-- -- -- -- --           ConsNFATrace-syntax-rebind N (N .init) (N .src x) ⊗
-- -- -- -- --           literal {ℓG = ℓ-max ℓN (ℓ-max ℓN' ℓΣ₀)} (N .label x)}
-- -- -- -- --          {h = (ConsNFATrace-syntax-rebind N (N .init) (N .dst x))}
-- -- -- -- --          {k =
-- -- -- -- --           LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) (N .dst x))}
-- -- -- -- --          (λ p → cons x ((p .fst) , ((p .snd .fst) , (lift (lower (p .snd .snd))))))
-- -- -- -- --          (LiftGrammarTerm {g = (ConsNFATrace-syntax-rebind N (N .init) (N .dst x))}))
-- -- -- -- --     the-cons-case (inr x) =
-- -- -- -- --       trans
-- -- -- -- --        {g =
-- -- -- -- --         LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) (N' .src x)) ⊗
-- -- -- -- --         literal (N' .label x)}
-- -- -- -- --        {h =
-- -- -- -- --         ConsNFATrace-syntax-rebind N' (N' .init) (N' .src x) ⊗ literal {ℓG = ℓ-max ℓN (ℓ-max ℓN' ℓΣ₀)} (N' .label x)}
-- -- -- -- --        {k =
-- -- -- -- --         LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) (N' .dst x))}
-- -- -- -- --        (cut
-- -- -- -- --          {g =
-- -- -- -- --           LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) (N' .src x))}
-- -- -- -- --          {h = ConsNFATrace-syntax-rebind N' (N' .init) (N' .src x)}
-- -- -- -- --          (var ⊗l literal (N' .label x))
-- -- -- -- --          (LowerGrammarTerm {g = (ConsNFATrace-syntax-rebind N' (N' .init) (N' .src x))}))
-- -- -- -- --        (trans
-- -- -- -- --          {g =
-- -- -- -- --           ConsNFATrace-syntax-rebind N' (N' .init) (N' .src x) ⊗
-- -- -- -- --           literal {ℓG = ℓ-max ℓN (ℓ-max ℓN' ℓΣ₀)} (N' .label x)}
-- -- -- -- --          {h = (ConsNFATrace-syntax-rebind N' (N' .init) (N' .dst x))}
-- -- -- -- --          {k =
-- -- -- -- --           LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) (N' .dst x))}
-- -- -- -- --          (λ p → cons x ((p .fst) , ((p .snd .fst) , (lift (lower (p .snd .snd))))))
-- -- -- -- --          (LiftGrammarTerm {g = (ConsNFATrace-syntax-rebind N' (N' .init) (N' .dst x))}))

-- -- -- -- --     the-ε-cons-case : (εtr : ⊕NFA .ε-transition .fst) →
-- -- -- -- --       the-P (ε-src ⊕NFA εtr)
-- -- -- -- --       ⊢
-- -- -- -- --       the-P (ε-dst ⊕NFA εtr)
-- -- -- -- --     the-ε-cons-case (inl fzero) =
-- -- -- -- --       trans {g = ε-grammar}
-- -- -- -- --        {h = ConsNFATrace-syntax-rebind N (N .init) (N .init)}
-- -- -- -- --        {k =
-- -- -- -- --         LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) (N .init))}
-- -- -- -- --        (λ p → nil (lift (lower p)))
-- -- -- -- --        (LiftGrammarTerm {g = (ConsNFATrace-syntax-rebind N (N .init) (N .init))})
-- -- -- -- --     the-ε-cons-case (inl (inr fzero)) =
-- -- -- -- --       trans {g = ε-grammar}
-- -- -- -- --        {h = ConsNFATrace-syntax-rebind N' (N' .init) (N' .init)}
-- -- -- -- --        {k =
-- -- -- -- --         LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) (N' .init))}
-- -- -- -- --        (λ p → nil (lift (lower p)))
-- -- -- -- --        (LiftGrammarTerm {g = (ConsNFATrace-syntax-rebind N' (N' .init) (N' .init))})
-- -- -- -- --     the-ε-cons-case (inr (inl x)) =
-- -- -- -- --       trans
-- -- -- -- --       {g = LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) (N .ε-src x))}
-- -- -- -- --       {h = (ConsNFATrace-syntax-rebind N (N .init) (N .ε-src x))}
-- -- -- -- --       {k = LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) (N .ε-dst x))}
-- -- -- -- --       (LowerGrammarTerm {g = (ConsNFATrace-syntax-rebind N (N .init) (N .ε-src x))})
-- -- -- -- --       (trans {g = ConsNFATrace-syntax-rebind N (N .init) (N .ε-src x)}
-- -- -- -- --         {h = ConsNFATrace-syntax-rebind N (N .init) (N .ε-dst x)}
-- -- -- -- --         {k =
-- -- -- -- --          LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) (N .ε-dst x))}
-- -- -- -- --         (ε-cons x)
-- -- -- -- --         (LiftGrammarTerm {g = (ConsNFATrace-syntax-rebind N (N .init) (N .ε-dst x))}))
-- -- -- -- --     the-ε-cons-case (inr (inr x)) =
-- -- -- -- --       trans
-- -- -- -- --       {g = LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) (N' .ε-src x))}
-- -- -- -- --       {h = (ConsNFATrace-syntax-rebind N' (N' .init) (N' .ε-src x))}
-- -- -- -- --       {k = LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) (N' .ε-dst x))}
-- -- -- -- --       (LowerGrammarTerm {g = (ConsNFATrace-syntax-rebind N' (N' .init) (N' .ε-src x))})
-- -- -- -- --       (trans {g = ConsNFATrace-syntax-rebind N' (N' .init) (N' .ε-src x)}
-- -- -- -- --         {h = ConsNFATrace-syntax-rebind N' (N' .init) (N' .ε-dst x)}
-- -- -- -- --         {k =
-- -- -- -- --          LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) (N' .ε-dst x))}
-- -- -- -- --         (ε-cons x)
-- -- -- -- --         (LiftGrammarTerm {g = (ConsNFATrace-syntax-rebind N' (N' .init) (N' .ε-dst x))}))

-- -- -- -- --   the-P→constraceN⊕snoctraceN' : ∀ q-end →
-- -- -- -- --     the-P q-end
-- -- -- -- --     ⊢
-- -- -- -- --     (ConsTraceFrom N (N .init) ⊕ SnocTraceFrom N' (N' .init))
-- -- -- -- --   the-P→constraceN⊕snoctraceN' (inl x) =
-- -- -- -- --     ⊕-intro₁
-- -- -- -- --       {g = ε-grammar}
-- -- -- -- --       {h = ConsTraceFrom N (N .init)}
-- -- -- -- --       {k = ConsTraceFrom N' (N' .init)}
-- -- -- -- --       (λ pε → (N .init) , (nil (lift (lower pε))))
-- -- -- -- --   the-P→constraceN⊕snoctraceN' (inr (inl x)) =
-- -- -- -- --     ⊕-intro₁
-- -- -- -- --       {g = LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) x)}
-- -- -- -- --       {h = ConsTraceFrom N (N .init)}
-- -- -- -- --       {k = ConsTraceFrom N' (N' .init)}
-- -- -- -- --       (trans {g = (LiftGrammar (ConsNFATrace-syntax-rebind N (N .init) x))}
-- -- -- -- --       {h = (ConsNFATrace-syntax-rebind N (N .init) x)}
-- -- -- -- --       {k = (ConsTraceFrom N (N .init))}
-- -- -- -- --       (LowerGrammarTerm {g = (ConsNFATrace-syntax-rebind N (N .init) x)})
-- -- -- -- --       (λ trace → x , trace))
-- -- -- -- --   the-P→constraceN⊕snoctraceN' (inr (inr x)) =
-- -- -- -- --     ⊕-intro₂
-- -- -- -- --       {g = LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) x)}
-- -- -- -- --       {h = ConsTraceFrom N' (N' .init)}
-- -- -- -- --       {k = ConsTraceFrom N (N .init)}
-- -- -- -- --       (trans {g = (LiftGrammar (ConsNFATrace-syntax-rebind N' (N' .init) x))}
-- -- -- -- --       {h = (ConsNFATrace-syntax-rebind N' (N' .init) x)}
-- -- -- -- --       {k = (ConsTraceFrom N' (N' .init))}
-- -- -- -- --       (LowerGrammarTerm {g = (ConsNFATrace-syntax-rebind N' (N' .init) x)})
-- -- -- -- --       (λ trace → x , trace))

-- -- -- -- --   constrace⊕NFA→snoctraceN⊕snoctraceN' : ∀ q-end →
-- -- -- -- --     ⟨ ⊕NFA ⟩Cons[ ⊕NFA .init →* q-end ]
-- -- -- -- --     ⊢
-- -- -- -- --     (ConsTraceFrom N (N .init) ⊕ SnocTraceFrom N' (N' .init))
-- -- -- -- --   constrace⊕NFA→snoctraceN⊕snoctraceN' q-end =
-- -- -- -- --     trans {g = ⟨ ⊕NFA ⟩Cons[ ⊕NFA .init →* q-end ]} {h = the-P q-end}
-- -- -- -- --       {k = (ConsTraceFrom N (N .init) ⊕ SnocTraceFrom N' (N' .init))}
-- -- -- -- --       (elimConsNFA ⊕NFA (⊕NFA .init) the-P
-- -- -- -- --         (λ pε → lift (lower pε))
-- -- -- -- --         (λ {tr} → the-cons-case tr)
-- -- -- -- --         (λ {εtr} → the-ε-cons-case εtr))
-- -- -- -- --       (the-P→constraceN⊕snoctraceN' q-end )

-- -- -- -- --   trace⊕NFA→traceN⊕traceN' : ∀ q-end →
-- -- -- -- --     ⟨ ⊕NFA ⟩[ ⊕NFA .init →* q-end ]
-- -- -- -- --     ⊢
-- -- -- -- --     (TraceFrom N (N .init) ⊕ TraceFrom N' (N' .init))
-- -- -- -- --   trace⊕NFA→traceN⊕traceN' q-end =
-- -- -- -- --     trans {g = NFATrace-syntax-rebind ⊕NFA q-end (⊕NFA .init)}
-- -- -- -- --      {h = ConsNFATrace-syntax-rebind ⊕NFA (⊕NFA .init) q-end}
-- -- -- -- --      {k = TraceFrom N (N .init) ⊕ TraceFrom N' (N' .init)}
-- -- -- -- --      (NFATrace→ConsNFATrace ⊕NFA (⊕NFA .init) q-end)
-- -- -- -- --      (trans {g = ConsNFATrace-syntax-rebind ⊕NFA (⊕NFA .init) q-end}
-- -- -- -- --        {h = ConsTraceFrom N (N .init) ⊕ SnocTraceFrom N' (N' .init)}
-- -- -- -- --        {k = TraceFrom N (N .init) ⊕ TraceFrom N' (N' .init)}
-- -- -- -- --        (constrace⊕NFA→snoctraceN⊕snoctraceN' q-end )
-- -- -- -- --        (⊕-elim {g = ConsTraceFrom N (N .init)}
-- -- -- -- --          {h = TraceFrom N (N .init) ⊕ TraceFrom N' (N' .init)}
-- -- -- -- --          {k = ConsTraceFrom N' (N' .init)}
-- -- -- -- --          (λ (q-end' , consTrace) →
-- -- -- -- --            ⊕-intro₁ {g = ⟨ N ⟩Cons[ N .init →* q-end' ]}
-- -- -- -- --              {h = TraceFrom N (N .init)}
-- -- -- -- --              {k = TraceFrom N' (N' .init)}
-- -- -- -- --              (λ consTrace' → q-end' , (SnocNFATrace→NFATrace N (N .init) q-end' snocTrace'))
-- -- -- -- --              consTrace
-- -- -- -- --              )
-- -- -- -- --          (λ (q-end' , consTrace) →
-- -- -- -- --            ⊕-intro₂ {g = ⟨ N' ⟩Cons[ N' .init →* q-end' ]}
-- -- -- -- --              {h = TraceFrom N' (N' .init)}
-- -- -- -- --              {k = TraceFrom N (N .init)}
-- -- -- -- --              (λ consTrace' → q-end' , (SnocNFATrace→NFATrace N' (N' .init) q-end' snocTrace'))
-- -- -- -- --              consTrace
-- -- -- -- --              )
-- -- -- -- --          ))

-- -- -- -- --   traceFrom⊕NFA→traceFromN⊕traceFromN' :
-- -- -- -- --     TraceFrom ⊕NFA (⊕NFA .init)
-- -- -- -- --     ⊢
-- -- -- -- --     (TraceFrom N (N .init) ⊕ TraceFrom N' (N' .init))
-- -- -- -- --   traceFrom⊕NFA→traceFromN⊕traceFromN' (q-end , trace) =
-- -- -- -- --     trace⊕NFA→traceN⊕traceN' q-end trace

-- -- -- -- -- --     -- TODO make sure I don't include traces through states that i've already seen
-- -- -- -- -- --     data ε-reachable (q-end : Q .fst) : Q .fst → Type ℓ where
-- -- -- -- -- --       ε-reach-nil : ε-reachable q-end q-end
-- -- -- -- -- --       ε-reach-cons : ∀ (εtr : ε-transition .fst) →
-- -- -- -- -- --         ε-reachable q-end (ε-dst εtr) →
-- -- -- -- -- --         ε-reachable q-end (ε-src εtr)

-- -- -- -- -- --     ε-reachDecProp :
-- -- -- -- -- --       ∀ q-start q-end → DecProp ℓ
-- -- -- -- -- --     fst (fst (ε-reachDecProp q-start q-end)) = ∥ ε-reachable q-end q-start ∥₁
-- -- -- -- -- --     snd (fst (ε-reachDecProp q-start q-end)) = isPropPropTrunc
-- -- -- -- -- --     snd (ε-reachDecProp q-start q-end) =
-- -- -- -- -- --       decRec
-- -- -- -- -- --         (λ q-start≡q-end →
-- -- -- -- -- --           yes ∣ transport (cong (λ a → ε-reachable q-end a) (sym (q-start≡q-end))) ε-reach-nil ∣₁)
-- -- -- -- -- --         (λ ¬q-start≡q-end → {!!})
-- -- -- -- -- --         (decEqQ q-start q-end)

-- -- -- -- -- --     -- ε-reach : Q .fst → FinSetDecℙ Q .fst
-- -- -- -- -- --     -- ε-reach q-start q-end =
-- -- -- -- -- --     --   DecProp∃ {!!} {!!}

-- -- -- -- -- -- module _ ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
-- -- -- -- -- --   open NFADefs ℓ (Σ₀ , isFinSetΣ₀)
-- -- -- -- -- --   open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
-- -- -- -- -- --   open DFADefs (ℓ-suc ℓ) (Lift Σ₀ , isFinSetLift isFinSetΣ₀)
-- -- -- -- -- --   -- open GrammarDefs
-- -- -- -- -- --   open TermDefs
-- -- -- -- -- --   open NFA
-- -- -- -- -- --   open DFA
-- -- -- -- -- --   open Iso

-- -- -- -- -- --   module _
-- -- -- -- -- --     (N : NFA)
-- -- -- -- -- --     (isPropDFATrace : ∀ D q w →
-- -- -- -- -- --       isProp (Σ[ q' ∈ (D .Q .fst) ] (DFATrace D q q' w))) where

-- -- -- -- -- --     ℙDFA : DFA
-- -- -- -- -- --     DFA.Q ℙDFA = FinSetDecℙ (N .Q)
-- -- -- -- -- --     DFA.init ℙDFA = SingletonDecℙ {A = N .Q} (N .init)
-- -- -- -- -- --     DFA.isAcc ℙDFA X =
-- -- -- -- -- --       DecProp'→DecProp
-- -- -- -- -- --       (_ , (isDecProp∃ (N .Q)
-- -- -- -- -- --       λ q →
-- -- -- -- -- --         LiftDecℙ' {ℓ}{ℓ-suc ℓ} (N .Q .fst)
-- -- -- -- -- --         (DecℙIso (N .Q .fst) .fun X) (lift q)))
-- -- -- -- -- --     DFA.δ ℙDFA X c q =
-- -- -- -- -- --       DecProp'→DecProp (_ ,
-- -- -- -- -- --         (isDecProp∃ (N .transition)
-- -- -- -- -- --         (λ tr →
-- -- -- -- -- --           {!!} , (isDecProp∃ (∥ ε-grammar ⊢ {!!} ∥₁ , {!!}) {!!}))))
-- -- -- -- -- --       where
-- -- -- -- -- --       open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)
-- -- -- -- -- --       open TermDefs ℓ (Σ₀ , isFinSetΣ₀)

-- -- -- -- -- -- --       -- DecProp'→DecProp
-- -- -- -- -- -- --       --   (_ , isDecProp∃ (N .transition)
-- -- -- -- -- -- --       --   (λ t →
-- -- -- -- -- -- --       --     DecProp→DecProp'
-- -- -- -- -- -- --       --     (DecProp×
-- -- -- -- -- -- --       --       (eqDecProp N (N .dst t) q)
-- -- -- -- -- -- --       --       (DecProp×
-- -- -- -- -- -- --       --         (X (N .src t))
-- -- -- -- -- -- --       --         (((N .label t ≡ lower c) ,
-- -- -- -- -- -- --       --         isFinSet→isSet isFinSetΣ₀ (N .NFADefs.NFA.label t) (lower c)) ,
-- -- -- -- -- -- --       --         isFinSet→Discrete isFinSetΣ₀ (N .NFADefs.NFA.label t) (lower c)))
-- -- -- -- -- -- --       --     )))

-- -- -- -- -- --     -- N→ℙDFA : ∀ w →
-- -- -- -- -- -- --     --   (tr : Σ[ (q , q') ∈ (N .Q .fst × N .Q .fst) ]
-- -- -- -- -- -- --     --      NFATrace N q q' w
-- -- -- -- -- -- --     --   )
-- -- -- -- -- -- --     --   →
-- -- -- -- -- -- --     --   (dfaq : Σ[ dq ∈ ℙDFA .DFA.Q .fst ]
-- -- -- -- -- -- --     --      dq (tr .fst .fst) .fst .fst)
-- -- -- -- -- -- --     --   →
-- -- -- -- -- -- --     --   Σ[ dq' ∈ ℙDFA .DFA.Q .fst ] DFATrace ℙDFA (dfaq .fst) dq' (LiftList w)
-- -- -- -- -- --     -- N→ℙDFA :
-- -- -- -- -- --     --    LinΣ[ (q-start , q-end) ∈ (Lift (N .Q .fst) × Lift (N .Q .fst)) ]
-- -- -- -- -- --     --      {!LiftGrammar (NFATrace N (lower q-end) (lower q-start))!}
-- -- -- -- -- --     --    ⊢
-- -- -- -- -- --     --   {!!}
-- -- -- -- -- --     -- N→ℙDFA = {!!}
-- -- -- -- -- -- -- --     N→ℙDFA w ((q , q') , NFADefs.NFA.nil a b) (dq , q∈dq) =
-- -- -- -- -- -- -- --       dq , (nil refl (λ i → LiftList (b i)))
-- -- -- -- -- -- -- --     N→ℙDFA [] ((q , q') , NFADefs.NFA.cons {t} a (s , lit , b)) (dq , q∈dq) =
-- -- -- -- -- -- -- --       ⊥.rec (¬cons≡nil (sym (s .snd ∙ cong (_++ s .fst .snd) lit)))
-- -- -- -- -- -- -- --     N→ℙDFA (x ∷ w) ((q , q') , NFADefs.NFA.cons {t} a (s , lit , b)) (dq , q∈dq) =
-- -- -- -- -- -- -- --       let
-- -- -- -- -- -- -- --       recur =
-- -- -- -- -- -- -- --         -- this transport is just to convince the typechecker about termination
-- -- -- -- -- -- -- --         N→ℙDFA w ((dst N t , q') , transport (cong (λ a → NFATrace N (dst N t) q' a) (sym w≡s₁₂)) b)
-- -- -- -- -- -- -- --           (ℙDFA .δ dq (lift (N .label t)) ,
-- -- -- -- -- -- -- --             ∣ t ,
-- -- -- -- -- -- -- --              (DecPropWitness→DecPropWitness'
-- -- -- -- -- -- -- --               (_ , _) (refl , ((transport (cong (λ z → dq z .fst .fst) (sym a)) q∈dq) , refl ))) ∣₁
-- -- -- -- -- -- -- --           ) in
-- -- -- -- -- -- -- --       recur .fst ,
-- -- -- -- -- -- -- --       (cons (lift (N .label t))
-- -- -- -- -- -- -- --         (((LiftList (s .fst .fst) , LiftList (w)) ,
-- -- -- -- -- -- -- --         cong LiftList (s .snd) ∙
-- -- -- -- -- -- -- --         LiftListDist (s .fst .fst) (s .fst .snd) ∙
-- -- -- -- -- -- -- --         cong (LiftList (s .fst .fst) ++_) (cong LiftList (sym w≡s₁₂))
-- -- -- -- -- -- -- --         ) ,
-- -- -- -- -- -- -- --         ((λ i → LiftList (lit i)) ,
-- -- -- -- -- -- -- --         recur .snd
-- -- -- -- -- -- -- --         )))
-- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- --       w≡s₁₂ : w ≡ s .fst .snd
-- -- -- -- -- -- -- --       w≡s₁₂ = cons-inj₂ (s .snd ∙ cong (_++ s .fst .snd) lit)
-- -- -- -- -- -- -- --     N→ℙDFA w ((q , q') , NFADefs.NFA.ε-cons {t} x tr) (dq , q∈dq) =
-- -- -- -- -- -- -- --       ⊥.rec (no-ε t)

-- -- -- -- -- -- -- --     ∃N→ℙDFA : ∀ w →
-- -- -- -- -- -- -- --       ∥ (Σ[ q ∈ N .Q .fst ]
-- -- -- -- -- -- -- --             NFATrace N (N .init) q w)  ∥₁
-- -- -- -- -- -- -- --       →
-- -- -- -- -- -- -- --       (Σ[ q ∈ ℙDFA .DFA.Q .fst ]
-- -- -- -- -- -- -- --            DFATrace ℙDFA (ℙDFA .DFA.init) q (LiftList w))
-- -- -- -- -- -- -- --     ∃N→ℙDFA w ∃pN =
-- -- -- -- -- -- -- --       PT.rec
-- -- -- -- -- -- -- --         (isPropDFATrace ℙDFA (ℙDFA .DFADefs.DFA.init) (LiftList w))
-- -- -- -- -- -- -- --         (λ x → N→ℙDFA w (((N .init) , x .fst) , x .snd) ((ℙDFA .DFA.init) , refl))
-- -- -- -- -- -- -- --         ∃pN

-- -- -- -- -- -- -- --     ℙDFA→∃N' : ∀ w → (q : N .Q .fst) →
-- -- -- -- -- -- -- --       ((dq' , pD) : Σ[ dq' ∈ ℙDFA .DFA.Q .fst ]
-- -- -- -- -- -- -- --            DFATrace ℙDFA (SingletonDecℙ {A = N .Q} q) dq' (LiftList w))
-- -- -- -- -- -- -- --       →
-- -- -- -- -- -- -- --       (∀ ((q' , q'∈dq') : Σ[ q' ∈ N .Q .fst ] dq' q' .fst .fst) → ∥ NFATrace N q q' w ∥₁)
-- -- -- -- -- -- -- --     ℙDFA→∃N' w q (dq' , pD) =
-- -- -- -- -- -- -- --       consfun w (snocView w) q (dq' , DFATrace→SnocDFATrace ℙDFA (SingletonDecℙ q) dq' pD)
-- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- --       consfun :
-- -- -- -- -- -- -- --         ∀ w → ConsView w → (q : N .Q .fst) →
-- -- -- -- -- -- -- --         ((dq' , pD) : Σ[ dq' ∈ ℙDFA .DFA.Q .fst ]
-- -- -- -- -- -- -- --               ConsDFATrace ℙDFA (SingletonDecℙ {A = N .Q} q) dq' (LiftList w))
-- -- -- -- -- -- -- --         →
-- -- -- -- -- -- -- --         (∀ ((q' , q'∈dq') : Σ[ q' ∈ N .Q .fst ] dq' q' .fst .fst) → ∥ NFATrace N q q' w ∥₁)
-- -- -- -- -- -- -- --       consfun .[] nil q (.(SingletonDecℙ q) , DFADefs.DFA.nil .(SingletonDecℙ q) x) (q' , q'∈dq') =
-- -- -- -- -- -- -- --         ∣ nil (sym q'∈dq') refl ∣₁
-- -- -- -- -- -- -- --       consfun .(xs ∷ʳ x₁) (snoc x₁ xs sw) q (.(SingletonDecℙ q) , DFADefs.DFA.nil .(SingletonDecℙ q) x) =
-- -- -- -- -- -- -- --         ⊥.rec (¬cons≡nil (sym (LiftListDist _ _) ∙ x))
-- -- -- -- -- -- -- --       consfun .[] nil q (.(DFADefs.DFA.δ ℙDFA X c) , DFADefs.DFA.snoc .(SingletonDecℙ q) X c x) =
-- -- -- -- -- -- -- --         ⊥.rec (¬nil≡cons ((x .fst .snd) ∙ (cong (x .fst .fst .fst ++_) (x .snd .snd))))
-- -- -- -- -- -- -- --       consfun .(xs ∷ʳ x₁) (snoc x₁ xs sw) q (.(DFADefs.DFA.δ ℙDFA X c) ,
-- -- -- -- -- -- -- --         DFADefs.DFA.cons .(SingletonDecℙ q) X c (s , x , lit)) (q' , q'∈dq') =
-- -- -- -- -- -- -- --         let recur =  consfun xs sw q (X , subst (SnocDFATrace ℙDFA (SingletonDecℙ q) X) s₁₁≡LLxs x) in
-- -- -- -- -- -- -- --         decRec
-- -- -- -- -- -- -- --           (λ |tr| →
-- -- -- -- -- -- -- --             PT.rec
-- -- -- -- -- -- -- --               isPropPropTrunc
-- -- -- -- -- -- -- --               (λ (tr , (dst≡q' , (src∈X , lbl≡x₁))) →
-- -- -- -- -- -- -- --                 let |pN| = recur ((N .src tr) , src∈X) in
-- -- -- -- -- -- -- --                 PT.rec
-- -- -- -- -- -- -- --                   isPropPropTrunc
-- -- -- -- -- -- -- --                   (λ pN →
-- -- -- -- -- -- -- --                     ∣ concatTrace N (((xs , [ x₁ ]) , refl) ,
-- -- -- -- -- -- -- --                       (pN ,
-- -- -- -- -- -- -- --                       cons refl (((label N tr ∷ [] , []) , cong (_∷ []) (sym lbl≡x₁)) ,
-- -- -- -- -- -- -- --                         (refl , (nil dst≡q' refl))))) ∣₁
-- -- -- -- -- -- -- --                   )
-- -- -- -- -- -- -- --                   |pN|
-- -- -- -- -- -- -- --               )
-- -- -- -- -- -- -- --           |tr|)
-- -- -- -- -- -- -- --           (λ ¬∃tr → {!!})
-- -- -- -- -- -- -- --           (DecProp∃ (N .transition)
-- -- -- -- -- -- -- --             (λ tr →
-- -- -- -- -- -- -- --               DecProp×
-- -- -- -- -- -- -- --                 (((N .dst tr ≡ q') , (isFinSet→isSet (N .Q .snd) _ _)) , (NFA.decEqQ N _ _))
-- -- -- -- -- -- -- --                 (DecProp×
-- -- -- -- -- -- -- --                   (X (N .src tr))
-- -- -- -- -- -- -- --                   (((N .label tr ≡ x₁) , (isFinSet→isSet isFinSetΣ₀ _ _)) , (isFinSet→Discrete isFinSetΣ₀ _ _))
-- -- -- -- -- -- -- --                 )
-- -- -- -- -- -- -- --               ) .snd)
-- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- --         s₁₁≡LLxs : s .fst .fst ≡ LiftList xs
-- -- -- -- -- -- -- --         s₁₁≡LLxs = cons-inj₁ (cong (s .fst .fst ++_) (sym lit) ∙ sym (s .snd) ∙ LiftListDist _ _)

-- -- -- -- -- -- -- -- --     ℙDFA→∃N : ∀ w →
-- -- -- -- -- -- -- -- --       (Σ[ q ∈ ℙDFA .DFA.Q .fst ]
-- -- -- -- -- -- -- -- --            DFATrace ℙDFA (ℙDFA .DFA.init) q (LiftList w))
-- -- -- -- -- -- -- -- --       →
-- -- -- -- -- -- -- -- --       ∥ (Σ[ q ∈ N .Q .fst ]
-- -- -- -- -- -- -- -- --             NFATrace N (N .init) q w) ∥₁
-- -- -- -- -- -- -- -- --     ℙDFA→∃N [] (q , DFADefs.DFA.nil srcp p) =
-- -- -- -- -- -- -- -- --       ∣ (N .init) , (nil refl refl) ∣₁
-- -- -- -- -- -- -- -- --     ℙDFA→∃N [] (q , DFADefs.DFA.cons c (s , lit , b)) =
-- -- -- -- -- -- -- -- --       ⊥.rec (¬cons≡nil (sym (s .snd ∙ cong (_++ s .fst .snd) lit)))
-- -- -- -- -- -- -- -- --     ℙDFA→∃N (x ∷ w) (q , DFADefs.DFA.nil srcp p) =
-- -- -- -- -- -- -- -- --       ⊥.rec (¬cons≡nil p)
-- -- -- -- -- -- -- -- --     ℙDFA→∃N (x ∷ w) (q , DFADefs.DFA.cons c (s , lit , p)) = {!p!}

-- -- -- -- -- -- -- -- --     ℙEquiv :
-- -- -- -- -- -- -- -- --     -- TODO this is the def of weak equiv up to universe issues
-- -- -- -- -- -- -- -- --       Iso
-- -- -- -- -- -- -- -- --         (Σ[ w ∈ String ]
-- -- -- -- -- -- -- -- --           ∥ Lift {ℓ}{ℓ-suc ℓ}
-- -- -- -- -- -- -- -- --             (Σ[ q ∈ N .Q .fst ]
-- -- -- -- -- -- -- -- --               NFATrace N (N .init) q w)  ∥₁)
-- -- -- -- -- -- -- -- --         (Σ[ w ∈ String ]
-- -- -- -- -- -- -- -- --           Σ[ q ∈ ℙDFA .DFA.Q .fst ]
-- -- -- -- -- -- -- -- --             DFATrace ℙDFA (ℙDFA .DFA.init) q (LiftList w))
-- -- -- -- -- -- -- -- --     fun ℙEquiv (w , ∃pN) =
-- -- -- -- -- -- -- -- --       w ,
-- -- -- -- -- -- -- -- --       (PT.rec
-- -- -- -- -- -- -- -- --         (isPropDFATrace ℙDFA (ℙDFA .DFADefs.DFA.init) (LiftList w))
-- -- -- -- -- -- -- -- --         (λ ↑pN →
-- -- -- -- -- -- -- -- --           let
-- -- -- -- -- -- -- -- --           x =
-- -- -- -- -- -- -- -- --             run
-- -- -- -- -- -- -- -- --               ℙDFA
-- -- -- -- -- -- -- -- --               (liftKL* (NFA.StringOfTrace N (N .NFADefs.NFA.init) (fst (lower ↑pN)) (lower ↑pN .snd))) in
-- -- -- -- -- -- -- -- --           x .fst , x .snd .fst
-- -- -- -- -- -- -- -- --         )
-- -- -- -- -- -- -- -- --         ∃pN)
-- -- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- -- --         liftKL* : ∀ {w} → KL* ℓ (Σ₀ , isFinSetΣ₀) (⊕Σ₀ ℓ (Σ₀ , isFinSetΣ₀)) w  →
-- -- -- -- -- -- -- -- --           KL* (ℓ-suc ℓ) (Lift Σ₀ , isFinSetLift isFinSetΣ₀) (⊕Σ₀ (ℓ-suc ℓ) (Lift Σ₀ , isFinSetLift isFinSetΣ₀))
-- -- -- -- -- -- -- -- --             (LiftList w)
-- -- -- -- -- -- -- -- --         liftKL* (nil x) = nil (λ i → LiftList (x i))
-- -- -- -- -- -- -- -- --         liftKL* (cons x) =
-- -- -- -- -- -- -- -- --           cons ((((LiftList (x .fst .fst .fst)) , (LiftList (x .fst .fst .snd))) ,
-- -- -- -- -- -- -- -- --             cong LiftList (x .fst .snd) ∙ LiftListDist (fst (fst (x .fst))) (snd (fst (x .fst)))) ,
-- -- -- -- -- -- -- -- --           ((lift (x .snd .fst .fst)) , (λ i → LiftList (x .snd .fst .snd i))) , liftKL* (x .snd .snd))

-- -- -- -- -- -- -- -- --       -- w , (consfun w (snocView w) ∃pN)
-- -- -- -- -- -- -- -- --       -- where
-- -- -- -- -- -- -- -- --       -- consfun : (w : String) → SnocView w →
-- -- -- -- -- -- -- -- --       --   (∥ Lift {ℓ}{ℓ-suc ℓ}
-- -- -- -- -- -- -- -- --       --       (Σ[ q ∈ N .Q .fst ]
-- -- -- -- -- -- -- -- --       --         NFATrace N (N .init) q w)  ∥₁)
-- -- -- -- -- -- -- -- --       --   →
-- -- -- -- -- -- -- -- --       --   (Σ[ q ∈ ℙDFA .DFA.Q .fst ]
-- -- -- -- -- -- -- -- --       --         DFATrace ℙDFA (ℙDFA .DFA.init) q (LiftList w))
-- -- -- -- -- -- -- -- --       -- consfun .[] nil ∃pN = (ℙDFA .DFA.init) , (nil refl refl)
-- -- -- -- -- -- -- -- --       -- consfun .(xs ∷ʳ x) (snoc x xs sv) ∃pN =
-- -- -- -- -- -- -- -- --       --   (run ℙDFA (String→KL* (ℓ-suc ℓ) (Lift Σ₀ , isFinSetLift isFinSetΣ₀) (LiftList (xs ∷ʳ x))) .fst) ,
-- -- -- -- -- -- -- -- --       --   {!!}
-- -- -- -- -- -- -- -- --       --
-- -- -- -- -- -- -- -- --         -- PT.rec
-- -- -- -- -- -- -- -- --         --   {!!}
-- -- -- -- -- -- -- -- --         --   (λ pN → help pN)
-- -- -- -- -- -- -- -- --         --   ∃pN
-- -- -- -- -- -- -- -- --         -- where
-- -- -- -- -- -- -- -- --         -- help : Lift
-- -- -- -- -- -- -- -- --         --         (Σ-syntax (N .NFADefs.NFA.Q .fst)
-- -- -- -- -- -- -- -- --         --          (λ q → NFATrace N (N .NFADefs.NFA.init) q (xs ∷ʳ x))) → DFATrace ℙDFA (ℙDFA .DFADefs.DFA.init)
-- -- -- -- -- -- -- -- --         --                                                                   (run ℙDFA
-- -- -- -- -- -- -- -- --         --                                                                    (String→KL* (ℓ-suc ℓ) (Lift Σ₀ , isFinSetLift isFinSetΣ₀)
-- -- -- -- -- -- -- -- --         --                                                                     (LiftList (xs ∷ʳ x)))
-- -- -- -- -- -- -- -- --         --                                                                    .fst)
-- -- -- -- -- -- -- -- --         --                                                                   (LiftList (xs ∷ʳ x))
-- -- -- -- -- -- -- -- --         -- help (lift (q , NFADefs.NFA.nil x a)) = nil {!!} {!a!}
-- -- -- -- -- -- -- -- --         -- help (lift (q , NFADefs.NFA.cons x b)) = {!!}
-- -- -- -- -- -- -- -- --         -- help (lift (q , NFADefs.NFA.ε-cons x tr)) = {!!}
-- -- -- -- -- -- -- -- --     inv ℙEquiv (w , ∃pN) =
-- -- -- -- -- -- -- -- --       w , {!!}
-- -- -- -- -- -- -- -- --     -- fun ℙEquiv ([] , ∃pN) =
-- -- -- -- -- -- -- -- --     --   [] ,
-- -- -- -- -- -- -- -- --     --   (ℙDFA .DFA.init) , (nil refl refl)
-- -- -- -- -- -- -- -- --     -- fun ℙEquiv (x ∷ w , ∃pN) = {!!}
-- -- -- -- -- -- -- -- --     --   -- (x ∷ w) , ({!!} , {!!})
-- -- -- -- -- -- -- -- --     -- inv ℙEquiv ([] , pD) =
-- -- -- -- -- -- -- -- --     --   [] ,
-- -- -- -- -- -- -- -- --     --   ∣ lift ((N .init) , (nil refl refl)) ∣₁
-- -- -- -- -- -- -- -- --     -- inv ℙEquiv (x ∷ w , pD) = {!!}
-- -- -- -- -- -- -- -- --     rightInv ℙEquiv = {!!}
-- -- -- -- -- -- -- -- --     leftInv ℙEquiv = {!!}

-- -- -- -- -- -- -- -- --     -- TODO universe polymorphism for grammar defs
-- -- -- -- -- -- -- -- --     -- ℙEquiv :
-- -- -- -- -- -- -- -- --     -- -- TODO this is the def of weak equiv up to universe issues
-- -- -- -- -- -- -- -- --     --   Iso
-- -- -- -- -- -- -- -- --     --     (Σ[ w ∈ String ]
-- -- -- -- -- -- -- -- --     --       ∥ Lift {ℓ}{ℓ-suc ℓ}
-- -- -- -- -- -- -- -- --     --         (Σ[ q ∈ NFA.Accepting N ]
-- -- -- -- -- -- -- -- --     --           NFATrace N (N .init) (q .fst) w)  ∥₁)
-- -- -- -- -- -- -- -- --     --     (Σ[ w ∈ String ]
-- -- -- -- -- -- -- -- --     --       Σ[ q ∈ DFA.Accepting ℙDFA ]
-- -- -- -- -- -- -- -- --     --         DFATrace ℙDFA (ℙDFA .DFA.init) (q .fst) (LiftList w))
-- -- -- -- -- -- -- -- --     -- fun ℙEquiv ([] , ∃pN) =
-- -- -- -- -- -- -- -- --     --   [] ,
-- -- -- -- -- -- -- -- --     --   ((ℙDFA .DFA.init) ,
-- -- -- -- -- -- -- -- --     --     PT.rec
-- -- -- -- -- -- -- -- --     --       (ℙDFA .DFA.isAcc (ℙDFA .DFADefs.DFA.init) .fst .snd)
-- -- -- -- -- -- -- -- --     --       (λ x → ∣ N .init , LiftDecProp'Witness _ (DecPropWitness→DecPropWitness' _ refl) ∣₁)
-- -- -- -- -- -- -- -- --     --       ∃pN
-- -- -- -- -- -- -- -- --     --   )
-- -- -- -- -- -- -- -- --     --   ,
-- -- -- -- -- -- -- -- --     --   nil refl refl
-- -- -- -- -- -- -- -- --     -- fun ℙEquiv (x ∷ w , ∃pN) = (x ∷ w) , {!!}
-- -- -- -- -- -- -- -- --     -- inv ℙEquiv ([] , pD) = {!!}
-- -- -- -- -- -- -- -- --     --   -- [] ,
-- -- -- -- -- -- -- -- --     --   -- ∣ lift (((N .init) , PT.rec (N .isAcc _ .fst .snd)
-- -- -- -- -- -- -- -- --     --   --   (λ x → transport (cong (λ a → fst (N .isAcc a .fst)) {!!})
-- -- -- -- -- -- -- -- --     --   --     (DecPropWitness→DecPropWitness' _ (LowerDecProp'Witness _ (x .snd))))
-- -- -- -- -- -- -- -- --     --   --     (pD .fst .snd)) , nil refl refl) ∣₁
-- -- -- -- -- -- -- -- --     -- inv ℙEquiv (x ∷ w , pD) =
-- -- -- -- -- -- -- -- --     --   {!!} , {!!}
-- -- -- -- -- -- -- -- --     -- rightInv ℙEquiv = {!!}
-- -- -- -- -- -- -- -- --     -- leftInv ℙEquiv = {!!}

-- -- -- -- -- -- -- -- -- -- module _ where
-- -- -- -- -- -- -- -- -- --   open NFADefs ℓ-zero (Fin 2 , isFinSetFin)
-- -- -- -- -- -- -- -- -- --   open GrammarDefs ℓ-zero (Fin 2 , isFinSetFin)
-- -- -- -- -- -- -- -- -- --   open StringDefs ℓ-zero (Fin 2 , isFinSetFin)

-- -- -- -- -- -- -- -- -- --   open NFA
-- -- -- -- -- -- -- -- -- --   N : N
-- -- -- -- -- -- -- -- -- --   Q N = (Fin 6) , isFinSetFin
-- -- -- -- -- -- -- -- -- --   init N = fromℕ 0
-- -- -- -- -- -- -- -- -- --   isAcc N x =
-- -- -- -- -- -- -- -- -- --     ((x ≡ fromℕ 5) ,
-- -- -- -- -- -- -- -- -- --      (isSetFin _ _)) ,
-- -- -- -- -- -- -- -- -- --     (isFinSet→Discrete isFinSetFin _ _)
-- -- -- -- -- -- -- -- -- --   transition N = Fin 4 , isFinSetFin
-- -- -- -- -- -- -- -- -- --   src N fzero = fromℕ 1
-- -- -- -- -- -- -- -- -- --   dst N fzero = fromℕ 2
-- -- -- -- -- -- -- -- -- --   src N (fsuc fzero) = fromℕ 2
-- -- -- -- -- -- -- -- -- --   dst N (fsuc fzero) = fromℕ 4
-- -- -- -- -- -- -- -- -- --   src N (fsuc (fsuc fzero)) = fromℕ 1
-- -- -- -- -- -- -- -- -- --   dst N (fsuc (fsuc fzero)) = fromℕ 3
-- -- -- -- -- -- -- -- -- --   src N (fsuc (fsuc (fsuc fzero))) = fromℕ 4
-- -- -- -- -- -- -- -- -- --   dst N (fsuc (fsuc (fsuc fzero))) = fromℕ 3
-- -- -- -- -- -- -- -- -- --   label N fzero = fromℕ 0
-- -- -- -- -- -- -- -- -- --   label N (fsuc fzero) = fromℕ 0
-- -- -- -- -- -- -- -- -- --   label N (fsuc (fsuc fzero)) = fromℕ 1
-- -- -- -- -- -- -- -- -- --   label N (fsuc (fsuc (fsuc fzero))) = fromℕ 1
-- -- -- -- -- -- -- -- -- --   ε-transition N = Fin 5 , isFinSetFin
-- -- -- -- -- -- -- -- -- --   ε-src N fzero = fromℕ 0
-- -- -- -- -- -- -- -- -- --   ε-dst N fzero = fromℕ 1
-- -- -- -- -- -- -- -- -- --   ε-src N (fsuc fzero) = fromℕ 3
-- -- -- -- -- -- -- -- -- --   ε-dst N (fsuc fzero) = fromℕ 2
-- -- -- -- -- -- -- -- -- --   ε-src N (fsuc (fsuc fzero)) = fromℕ 2
-- -- -- -- -- -- -- -- -- --   ε-dst N (fsuc (fsuc fzero)) = fromℕ 3
-- -- -- -- -- -- -- -- -- --   ε-src N (fsuc (fsuc (fsuc fzero))) = fromℕ 4
-- -- -- -- -- -- -- -- -- --   ε-dst N (fsuc (fsuc (fsuc fzero))) = fromℕ 5
-- -- -- -- -- -- -- -- -- --   ε-src N (fsuc (fsuc (fsuc (fsuc fzero)))) = fromℕ 5
-- -- -- -- -- -- -- -- -- --   ε-dst N (fsuc (fsuc (fsuc (fsuc fzero)))) = fromℕ 6

-- -- -- -- -- -- -- -- --   -- N' : NFA
-- -- -- -- -- -- -- -- --   -- N' = ε-closure 5 N isFinOrdFin





-- -- -- -- -- -- -- -- --     -- Determinize :
-- -- -- -- -- -- -- -- --     --   (D : DFA) →
-- -- -- -- -- -- -- -- --     --   Term Parses (DFA.Parses D) →
-- -- -- -- -- -- -- -- --     --   Term ∥ Parses ∥grammar (DFA.Parses D)
-- -- -- -- -- -- -- -- --     -- Determinize = {!!}

-- -- -- -- -- -- -- -- -- --     negate : NFA
-- -- -- -- -- -- -- -- -- --     Q negate = Q
-- -- -- -- -- -- -- -- -- --     init negate = init
-- -- -- -- -- -- -- -- -- --     isAcc negate q = negateDecProp (isAcc q)
-- -- -- -- -- -- -- -- -- --     transition negate = transition
-- -- -- -- -- -- -- -- -- --     src negate = src
-- -- -- -- -- -- -- -- -- --     dst negate = dst
-- -- -- -- -- -- -- -- -- --     label negate = label
-- -- -- -- -- -- -- -- -- --     ε-transition negate = ε-transition
-- -- -- -- -- -- -- -- -- --     ε-src negate = ε-src
-- -- -- -- -- -- -- -- -- --     ε-dst negate = ε-dst

-- -- -- -- -- -- -- -- -- --   open NFA
-- -- -- -- -- -- -- -- -- --   module _ (c : Σ₀) where
-- -- -- -- -- -- -- -- -- --     literalNFA : NFA
-- -- -- -- -- -- -- -- -- --     fst (Q literalNFA) = Lift (Fin 2)
-- -- -- -- -- -- -- -- -- --     snd (Q literalNFA) = isFinSetLift isFinSetFin
-- -- -- -- -- -- -- -- -- --     init literalNFA = lift (inl tt)
-- -- -- -- -- -- -- -- -- --     fst (fst (isAcc literalNFA x)) = x ≡ lift (inr (inl tt))
-- -- -- -- -- -- -- -- -- --     snd (fst (isAcc literalNFA x)) = isSetLift isSetFin _ _
-- -- -- -- -- -- -- -- -- --     snd (isAcc literalNFA x) = discreteLift discreteFin _ _
-- -- -- -- -- -- -- -- -- --     transition literalNFA = Lift Unit , isFinSetLift isFinSetUnit
-- -- -- -- -- -- -- -- -- --     src literalNFA _ = lift (inl tt)
-- -- -- -- -- -- -- -- -- --     dst literalNFA _ = lift (inr (inl tt))
-- -- -- -- -- -- -- -- -- --     label literalNFA _ = c
-- -- -- -- -- -- -- -- -- --     ε-transition literalNFA = Lift ⊥ , isFinSetLift isFinSetFin
-- -- -- -- -- -- -- -- -- --     ε-src literalNFA x = ⊥.rec (lower x)
-- -- -- -- -- -- -- -- -- --     ε-dst literalNFA x = ⊥.rec (lower x)

-- -- -- -- -- -- -- -- -- --   emptyNFA : NFA
-- -- -- -- -- -- -- -- -- --   Q emptyNFA = Lift (Fin 2) , isFinSetLift isFinSetFin
-- -- -- -- -- -- -- -- -- --   init emptyNFA = lift fzero
-- -- -- -- -- -- -- -- -- --   isAcc emptyNFA x =
-- -- -- -- -- -- -- -- -- --     ((x ≡ lift (fsuc fzero)) , isSetLift isSetFin _ _) ,
-- -- -- -- -- -- -- -- -- --     discreteLift discreteFin x (lift (fsuc fzero))
-- -- -- -- -- -- -- -- -- --   transition emptyNFA = Lift ⊥ , isFinSetLift isFinSetFin
-- -- -- -- -- -- -- -- -- --   src emptyNFA (lift x) = ⊥.rec x
-- -- -- -- -- -- -- -- -- --   dst emptyNFA (lift x) = ⊥.rec x
-- -- -- -- -- -- -- -- -- --   label emptyNFA (lift x) = ⊥.rec x
-- -- -- -- -- -- -- -- -- --   ε-transition emptyNFA = Lift Unit , isFinSetLift isFinSetUnit
-- -- -- -- -- -- -- -- -- --   ε-src emptyNFA _ = emptyNFA .init
-- -- -- -- -- -- -- -- -- --   ε-dst emptyNFA _ = lift (fsuc fzero)

-- -- -- -- -- -- -- -- -- --   module _ (N : NFA) where
-- -- -- -- -- -- -- -- -- --     isDeterministic : Type ℓ
-- -- -- -- -- -- -- -- -- --     isDeterministic =
-- -- -- -- -- -- -- -- -- --       -- No ε-transitions
-- -- -- -- -- -- -- -- -- --       (N .ε-transition .fst ≃ Fin 0) ×
-- -- -- -- -- -- -- -- -- --       -- forall states
-- -- -- -- -- -- -- -- -- --       (∀ (q : N .Q .fst) →
-- -- -- -- -- -- -- -- -- --         -- there are only Σ₀-many transitions (may be redundant)
-- -- -- -- -- -- -- -- -- --         (fiber (N .dst) q ≃ Σ₀) ×
-- -- -- -- -- -- -- -- -- --         -- and there is exactly one for each label c
-- -- -- -- -- -- -- -- -- --         (∀ (c : Σ₀) →
-- -- -- -- -- -- -- -- -- --           isContr (Σ[ t ∈ fiber (N .dst) q ]
-- -- -- -- -- -- -- -- -- --            (N .label (t .fst) ≡ c))))

-- -- -- -- -- -- -- -- -- --     module _ (deter : isDeterministic) where
-- -- -- -- -- -- -- -- -- --       open DFADefs ℓ (Σ₀ , isFinSetΣ₀)
-- -- -- -- -- -- -- -- -- --       open DFADefs.DFA

-- -- -- -- -- -- -- -- -- --       deterministicNFA : DFA
-- -- -- -- -- -- -- -- -- --       Q deterministicNFA = N .Q
-- -- -- -- -- -- -- -- -- --       init deterministicNFA = N .init
-- -- -- -- -- -- -- -- -- --       isAcc deterministicNFA = N .isAcc
-- -- -- -- -- -- -- -- -- --       δ deterministicNFA q c =
-- -- -- -- -- -- -- -- -- --         N .dst (deter .snd q .snd c .fst .fst .fst)

-- -- -- -- -- -- -- -- -- --   module _ (N : NFA) where
-- -- -- -- -- -- -- -- -- --     h =
-- -- -- -- -- -- -- -- -- --       LinΣ[ q ∈ N .Q .fst ]
-- -- -- -- -- -- -- -- -- --         (NFATrace N (N .init) q
-- -- -- -- -- -- -- -- -- --           & (acc? N q ⊕ rej? N q))
-- -- -- -- -- -- -- -- -- --     h' = h ⊕ ⊤-grammar

-- -- -- -- -- -- -- -- -- --     run' : ParseTransformer (KL* ⊕Σ₀) h'
-- -- -- -- -- -- -- -- -- --     run' =
-- -- -- -- -- -- -- -- -- --       fold*l
-- -- -- -- -- -- -- -- -- --         ⊕Σ₀
-- -- -- -- -- -- -- -- -- --         h'
-- -- -- -- -- -- -- -- -- --         mt-case
-- -- -- -- -- -- -- -- -- --         cons-case
-- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- --       mt-case : ParseTransformer ε-grammar h'
-- -- -- -- -- -- -- -- -- --       mt-case {w} p =
-- -- -- -- -- -- -- -- -- --         inl ((N .init) , ((nil refl p) ,
-- -- -- -- -- -- -- -- -- --           (decRec
-- -- -- -- -- -- -- -- -- --             (λ acc → inl
-- -- -- -- -- -- -- -- -- --               (DecProp-grammar-yes (N .isAcc (N .init)) _ _ acc _ _))
-- -- -- -- -- -- -- -- -- --             (λ ¬acc → inr (DecProp-grammar-yes
-- -- -- -- -- -- -- -- -- --               (negateDecProp (N .isAcc (N .init))) _ _ ¬acc _ _))
-- -- -- -- -- -- -- -- -- --             (N .isAcc (N .init) .snd))))

-- -- -- -- -- -- -- -- -- --       cons-case : ParseTransformer (h' ⊗ ⊕Σ₀) h'
-- -- -- -- -- -- -- -- -- --       cons-case {w} (split , inl (q , nil x x₁ , z) , char) = {!!}
-- -- -- -- -- -- -- -- -- --       cons-case {w} (split , inl (q , cons {t} x y , z) , char) = {!!}
-- -- -- -- -- -- -- -- -- --       cons-case {w} (split , inl (q , ε-cons {t} x y , z) , char) = {!!}
-- -- -- -- -- -- -- -- -- --       cons-case {w} (split , fsuc x , char) = {!!}


-- -- -- -- -- -- -- -- -- --   -- NFA Combinators
-- -- -- -- -- -- -- -- -- -- --   module _ (N : NFA) where
-- -- -- -- -- -- -- -- -- -- --     module _ (N' : NFA) where

-- -- -- -- -- -- -- -- -- -- --       ⊕NFA : NFA
-- -- -- -- -- -- -- -- -- -- --       -- States stratified into init, N states, N' states
-- -- -- -- -- -- -- -- -- -- --       Q ⊕NFA .fst = ⊤ ⊎ (N .Q .fst ⊎ N' .Q .fst)
-- -- -- -- -- -- -- -- -- -- --       Q ⊕NFA .snd =
-- -- -- -- -- -- -- -- -- -- --         isFinSet⊎
-- -- -- -- -- -- -- -- -- -- --           (_ , isFinSetUnit)
-- -- -- -- -- -- -- -- -- -- --           (_ , (isFinSet⊎ (N .Q) (N' .Q)))
-- -- -- -- -- -- -- -- -- -- --       -- initial state
-- -- -- -- -- -- -- -- -- -- --       init ⊕NFA = inl _
-- -- -- -- -- -- -- -- -- -- --       -- Acceptance at subautomata accepting states
-- -- -- -- -- -- -- -- -- -- --       isAcc ⊕NFA x =
-- -- -- -- -- -- -- -- -- -- --         -- LOL this is way too complicated
-- -- -- -- -- -- -- -- -- -- --         -- could've just pattern matched on x
-- -- -- -- -- -- -- -- -- -- --         DecProp⊎
-- -- -- -- -- -- -- -- -- -- --           (DecPropΣ
-- -- -- -- -- -- -- -- -- -- --             (((fiber (inr ∘ inl) x) , inr∘inl-prop-fibs) ,
-- -- -- -- -- -- -- -- -- -- --               decRec
-- -- -- -- -- -- -- -- -- -- --                 (PT.elim
-- -- -- -- -- -- -- -- -- -- --                     (λ _ → isPropDec inr∘inl-prop-fibs)
-- -- -- -- -- -- -- -- -- -- --                     (λ y → yes y))
-- -- -- -- -- -- -- -- -- -- --                 (λ ∄preimage →
-- -- -- -- -- -- -- -- -- -- --                   no λ y → ∄preimage ∣ y ∣₁
-- -- -- -- -- -- -- -- -- -- --                 )
-- -- -- -- -- -- -- -- -- -- --                 (DecPropIso .Iso.inv
-- -- -- -- -- -- -- -- -- -- --                   (_ , isDecProp∃ (N .Q)
-- -- -- -- -- -- -- -- -- -- --                     (λ y → (inr (inl y) ≡ x) ,
-- -- -- -- -- -- -- -- -- -- --                       isDecProp≡ (⊕NFA .Q) (inr (inl y)) x) ) .snd))
-- -- -- -- -- -- -- -- -- -- --             (N .isAcc ∘ fst))
-- -- -- -- -- -- -- -- -- -- --           (DecPropΣ
-- -- -- -- -- -- -- -- -- -- --             ((fiber (inr ∘ inr) x , inr∘inr-prop-fibs) ,
-- -- -- -- -- -- -- -- -- -- --               decRec
-- -- -- -- -- -- -- -- -- -- --                 (PT.elim
-- -- -- -- -- -- -- -- -- -- --                   (λ _ → isPropDec inr∘inr-prop-fibs)
-- -- -- -- -- -- -- -- -- -- --                   λ y → yes y)
-- -- -- -- -- -- -- -- -- -- --                 (λ ∄preimage → no λ y → ∄preimage ∣ y ∣₁)
-- -- -- -- -- -- -- -- -- -- --                 (DecPropIso .Iso.inv
-- -- -- -- -- -- -- -- -- -- --                   ((_ , isDecProp∃ (N' .Q) λ y → (inr (inr  y) ≡ x) ,
-- -- -- -- -- -- -- -- -- -- --                     (isDecProp≡ (⊕NFA .Q) (inr (inr y)) x))) .snd))
-- -- -- -- -- -- -- -- -- -- --             (N' .isAcc ∘ fst))
-- -- -- -- -- -- -- -- -- -- --           mutex
-- -- -- -- -- -- -- -- -- -- --           where
-- -- -- -- -- -- -- -- -- -- --           inr∘inl-prop-fibs =
-- -- -- -- -- -- -- -- -- -- --             isEmbedding→hasPropFibers
-- -- -- -- -- -- -- -- -- -- --               (compEmbedding (_ , isEmbedding-inr)
-- -- -- -- -- -- -- -- -- -- --                              (_ , isEmbedding-inl) .snd) x

-- -- -- -- -- -- -- -- -- -- --           inr∘inr-prop-fibs =
-- -- -- -- -- -- -- -- -- -- --             isEmbedding→hasPropFibers
-- -- -- -- -- -- -- -- -- -- --               (compEmbedding
-- -- -- -- -- -- -- -- -- -- --                 (_ , isEmbedding-inr)
-- -- -- -- -- -- -- -- -- -- --                 (_ , isEmbedding-inr) .snd) x

-- -- -- -- -- -- -- -- -- -- --           mutex =
-- -- -- -- -- -- -- -- -- -- --             (λ (q , _) (q' , _) →
-- -- -- -- -- -- -- -- -- -- --               lower (⊎Path.encode _ _
-- -- -- -- -- -- -- -- -- -- --                 (isEmbedding→Inj isEmbedding-inr _ _
-- -- -- -- -- -- -- -- -- -- --                   (q .snd ∙ (sym (q' .snd))))))
-- -- -- -- -- -- -- -- -- -- --       transition ⊕NFA .fst =
-- -- -- -- -- -- -- -- -- -- --         N .transition .fst ⊎ N' .transition .fst
-- -- -- -- -- -- -- -- -- -- --       transition ⊕NFA .snd =
-- -- -- -- -- -- -- -- -- -- --         isFinSet⊎ (N .transition) (N' .transition)
-- -- -- -- -- -- -- -- -- -- --       -- the labeled transitions have same src, dst, and label as
-- -- -- -- -- -- -- -- -- -- --       -- in original automata
-- -- -- -- -- -- -- -- -- -- --       src ⊕NFA (inl x) = inr (inl (N .src x))
-- -- -- -- -- -- -- -- -- -- --       src ⊕NFA (inr x) = inr (inr (N' .src x))
-- -- -- -- -- -- -- -- -- -- --       dst ⊕NFA (inl x) = inr (inl (N .dst x))
-- -- -- -- -- -- -- -- -- -- --       dst ⊕NFA (inr x) = inr (inr (N' .dst x))
-- -- -- -- -- -- -- -- -- -- --       label ⊕NFA (inl x) = N .label x
-- -- -- -- -- -- -- -- -- -- --       label ⊕NFA (inr x) = N' .label x
-- -- -- -- -- -- -- -- -- -- --       fst (ε-transition ⊕NFA) =
-- -- -- -- -- -- -- -- -- -- --         Fin 2 ⊎
-- -- -- -- -- -- -- -- -- -- --         (N .ε-transition .fst ⊎ N' .ε-transition .fst)
-- -- -- -- -- -- -- -- -- -- --       snd (ε-transition ⊕NFA) =
-- -- -- -- -- -- -- -- -- -- --         isFinSet⊎
-- -- -- -- -- -- -- -- -- -- --           (_ , isFinSetFin)
-- -- -- -- -- -- -- -- -- -- --           (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))
-- -- -- -- -- -- -- -- -- -- --       -- ε-transitions to subautomata initial states
-- -- -- -- -- -- -- -- -- -- --       ε-src ⊕NFA (inl fzero) = ⊕NFA .init
-- -- -- -- -- -- -- -- -- -- --       ε-dst ⊕NFA (inl fzero) = inr (inl (N .init))
-- -- -- -- -- -- -- -- -- -- --       ε-src ⊕NFA (inl (inr fzero)) = ⊕NFA .init
-- -- -- -- -- -- -- -- -- -- --       ε-dst ⊕NFA (inl (inr fzero)) = inr (inr (N' .init))
-- -- -- -- -- -- -- -- -- -- --       -- internal ε-transitions from subautomata
-- -- -- -- -- -- -- -- -- -- --       ε-src ⊕NFA (inr (inl x)) = inr (inl (N .ε-src x))
-- -- -- -- -- -- -- -- -- -- --       ε-dst ⊕NFA (inr (inl x)) = inr (inl (N .ε-dst x))
-- -- -- -- -- -- -- -- -- -- --       ε-src ⊕NFA (inr (inr x)) = inr (inr (N' .ε-src x))
-- -- -- -- -- -- -- -- -- -- --       ε-dst ⊕NFA (inr (inr x)) = inr (inr (N' .ε-dst x))

-- -- -- -- -- -- -- -- -- -- --       ⊗NFA : NFA
-- -- -- -- -- -- -- -- -- -- --       Q ⊗NFA .fst = N .Q .fst ⊎ N' .Q .fst
-- -- -- -- -- -- -- -- -- -- --       Q ⊗NFA .snd = isFinSet⊎ (N .Q) (N' .Q)
-- -- -- -- -- -- -- -- -- -- --       init ⊗NFA = inl (N .init)
-- -- -- -- -- -- -- -- -- -- --       isAcc ⊗NFA (inl x) =
-- -- -- -- -- -- -- -- -- -- --         DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
-- -- -- -- -- -- -- -- -- -- --       isAcc ⊗NFA (inr x) = N' .isAcc x
-- -- -- -- -- -- -- -- -- -- --       transition ⊗NFA .fst = N .transition .fst ⊎ N' .transition .fst
-- -- -- -- -- -- -- -- -- -- --       transition ⊗NFA .snd = isFinSet⊎ (N .transition) (N' .transition)
-- -- -- -- -- -- -- -- -- -- --       src ⊗NFA (inl x) = inl (N .src x)
-- -- -- -- -- -- -- -- -- -- --       dst ⊗NFA (inl x) = inl (N .dst x)
-- -- -- -- -- -- -- -- -- -- --       src ⊗NFA (inr x) = inr (N' .src x)
-- -- -- -- -- -- -- -- -- -- --       dst ⊗NFA (inr x) = inr (N' .dst x)
-- -- -- -- -- -- -- -- -- -- --       label ⊗NFA (inl x) = N .label x
-- -- -- -- -- -- -- -- -- -- --       label ⊗NFA (inr x) = N' .label x
-- -- -- -- -- -- -- -- -- -- --       ε-transition ⊗NFA .fst =
-- -- -- -- -- -- -- -- -- -- --         (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
-- -- -- -- -- -- -- -- -- -- --         (N .ε-transition .fst ⊎ N' .ε-transition .fst)
-- -- -- -- -- -- -- -- -- -- --       ε-transition ⊗NFA .snd =
-- -- -- -- -- -- -- -- -- -- --         isFinSet⊎
-- -- -- -- -- -- -- -- -- -- --           (_ , isFinSetΣ (N .Q)
-- -- -- -- -- -- -- -- -- -- --             λ x → _ ,
-- -- -- -- -- -- -- -- -- -- --               isDecProp→isFinSet
-- -- -- -- -- -- -- -- -- -- --                 (N .isAcc x .fst .snd)
-- -- -- -- -- -- -- -- -- -- --                 (N .isAcc x .snd))
-- -- -- -- -- -- -- -- -- -- --           ((_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
-- -- -- -- -- -- -- -- -- -- --       ε-src ⊗NFA (inl x) = inl (x .fst)
-- -- -- -- -- -- -- -- -- -- --       ε-dst ⊗NFA (inl x) = inr (N' .init)
-- -- -- -- -- -- -- -- -- -- --       ε-src ⊗NFA (inr (inl x)) = inl (N .ε-src x)
-- -- -- -- -- -- -- -- -- -- --       ε-dst ⊗NFA (inr (inl x)) = inl (N .ε-dst x)
-- -- -- -- -- -- -- -- -- -- --       ε-src ⊗NFA (inr (inr x)) = inr (N' .ε-src x)
-- -- -- -- -- -- -- -- -- -- --       ε-dst ⊗NFA (inr (inr x)) = inr (N' .ε-dst x)

-- -- -- -- -- -- -- -- -- -- --     KL*NFA : NFA
-- -- -- -- -- -- -- -- -- -- --     Q KL*NFA .fst = N .Q .fst ⊎ ⊤
-- -- -- -- -- -- -- -- -- -- --     Q KL*NFA .snd = isFinSet⊎ (N .Q) (_ , isFinSetUnit)
-- -- -- -- -- -- -- -- -- -- --     init KL*NFA = inl (N .init)
-- -- -- -- -- -- -- -- -- -- --     isAcc KL*NFA (inl x) =
-- -- -- -- -- -- -- -- -- -- --       DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
-- -- -- -- -- -- -- -- -- -- --     isAcc KL*NFA (inr x) =
-- -- -- -- -- -- -- -- -- -- --       DecPropIso .Iso.inv (Unit* , (true , (invEquiv LiftEquiv)))
-- -- -- -- -- -- -- -- -- -- --     transition KL*NFA = N .transition
-- -- -- -- -- -- -- -- -- -- --     src KL*NFA x = inl (N .src x)
-- -- -- -- -- -- -- -- -- -- --     dst KL*NFA x = inl (N .dst x)
-- -- -- -- -- -- -- -- -- -- --     label KL*NFA = N .label
-- -- -- -- -- -- -- -- -- -- --     ε-transition KL*NFA .fst =
-- -- -- -- -- -- -- -- -- -- --       ⊤ ⊎
-- -- -- -- -- -- -- -- -- -- --       ((Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
-- -- -- -- -- -- -- -- -- -- --         (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst))
-- -- -- -- -- -- -- -- -- -- --     ε-transition KL*NFA .snd =
-- -- -- -- -- -- -- -- -- -- --       isFinSet⊎
-- -- -- -- -- -- -- -- -- -- --         (_ , isFinSetUnit)
-- -- -- -- -- -- -- -- -- -- --         (_ , isFinSet⊎
-- -- -- -- -- -- -- -- -- -- --           (_ , isFinSetAccΣ)
-- -- -- -- -- -- -- -- -- -- --           (_ , isFinSetAccΣ))
-- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- --       isFinSetAccΣ :
-- -- -- -- -- -- -- -- -- -- --         isFinSet
-- -- -- -- -- -- -- -- -- -- --           (Σ-syntax (N .Q .fst) (λ q → N .isAcc q .fst .fst))
-- -- -- -- -- -- -- -- -- -- --       isFinSetAccΣ =
-- -- -- -- -- -- -- -- -- -- --         isFinSetΣ (N .Q)
-- -- -- -- -- -- -- -- -- -- --           (λ x → _ ,
-- -- -- -- -- -- -- -- -- -- --             isDecProp→isFinSet
-- -- -- -- -- -- -- -- -- -- --               (N .isAcc x .fst .snd)
-- -- -- -- -- -- -- -- -- -- --               (N .isAcc x .snd))
-- -- -- -- -- -- -- -- -- -- --     ε-src KL*NFA (inl x) = inl (N .init)
-- -- -- -- -- -- -- -- -- -- --     ε-dst KL*NFA (inl x) = inr _
-- -- -- -- -- -- -- -- -- -- --     ε-src KL*NFA (inr (inl x)) = inl (x .fst)
-- -- -- -- -- -- -- -- -- -- --     ε-dst KL*NFA (inr (inl x)) = inl (N .init)
-- -- -- -- -- -- -- -- -- -- --     ε-src KL*NFA (inr (inr x)) = inl (x .fst)
-- -- -- -- -- -- -- -- -- -- --     ε-dst KL*NFA (inr (inr x)) = inr _

-- -- -- -- -- -- -- -- -- -- --   NFAfromRegularGrammar : RegularGrammar → NFA
-- -- -- -- -- -- -- -- -- -- --   NFAfromRegularGrammar ε-Reg = emptyNFA
-- -- -- -- -- -- -- -- -- -- --   NFAfromRegularGrammar (g ⊗Reg h) =
-- -- -- -- -- -- -- -- -- -- --     ⊗NFA (NFAfromRegularGrammar g) (NFAfromRegularGrammar h)
-- -- -- -- -- -- -- -- -- -- --   NFAfromRegularGrammar (literalReg c) = literalNFA c
-- -- -- -- -- -- -- -- -- -- --   NFAfromRegularGrammar (g ⊕Reg h) =
-- -- -- -- -- -- -- -- -- -- --     ⊕NFA (NFAfromRegularGrammar g) (NFAfromRegularGrammar h)
-- -- -- -- -- -- -- -- -- -- --   NFAfromRegularGrammar (KL*Reg g) = KL*NFA (NFAfromRegularGrammar g)

-- -- -- -- -- -- -- -- -- -- --   open Iso
-- -- -- -- -- -- -- -- -- -- --   module regex-isos
-- -- -- -- -- -- -- -- -- -- --     -- TODO need to prove these in the grammar module
-- -- -- -- -- -- -- -- -- -- --     -- but there are some cubical issues, so we'll
-- -- -- -- -- -- -- -- -- -- --     -- -- take them as given here
-- -- -- -- -- -- -- -- -- -- --     -- (⊗-unit-l-isStronglyEquivalent : (g : Grammar) →
-- -- -- -- -- -- -- -- -- -- --     --   isStronglyEquivalent (ε-grammar ⊗ g) g)
-- -- -- -- -- -- -- -- -- -- --     -- (⊗-unit-r-isStronglyEquivalent : (g : Grammar) →
-- -- -- -- -- -- -- -- -- -- --     --   isStronglyEquivalent (g ⊗ ε-grammar) g)
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     elimEmptyNFA :
-- -- -- -- -- -- -- -- -- -- --       ∀ {q}{q'} →
-- -- -- -- -- -- -- -- -- -- --       ParseTransformer (NFATrace emptyNFA q q') ε-grammar
-- -- -- -- -- -- -- -- -- -- --     elimEmptyNFA p =
-- -- -- -- -- -- -- -- -- -- --       elimNFA
-- -- -- -- -- -- -- -- -- -- --         emptyNFA
-- -- -- -- -- -- -- -- -- -- --         (λ _ _ → the-P)
-- -- -- -- -- -- -- -- -- -- --         (id-PT ε-grammar)
-- -- -- -- -- -- -- -- -- -- --         (λ {_}{_}{t} x y → ⊥.rec (lower t))
-- -- -- -- -- -- -- -- -- -- --         (λ x → id-PT the-P)
-- -- -- -- -- -- -- -- -- -- --         p
-- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- --       the-P = ε-grammar
-- -- -- -- -- -- -- -- -- -- --       the-nil-case = id-PT ε-grammar

-- -- -- -- -- -- -- -- -- -- --     isProp-emptyNFAParse' : ∀ {w} →
-- -- -- -- -- -- -- -- -- -- --       isProp (NFATrace emptyNFA (lift fzero) (lift (fsuc fzero)) w)
-- -- -- -- -- -- -- -- -- -- --     isProp-emptyNFAParse' {w} (nil x x₁) (nil x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --       cong₂ (λ a b → NFATrace.nil {emptyNFA} a {w} b)
-- -- -- -- -- -- -- -- -- -- --         (isSetLift isSetFin _ _ x x₂) (isSetString _ _ x₁ x₃)
-- -- -- -- -- -- -- -- -- -- --     isProp-emptyNFAParse' {w} (nil x x₁) (ε-cons x₂ y) =
-- -- -- -- -- -- -- -- -- -- --       ⊥.rec (fzero≠fone (cong lower x))
-- -- -- -- -- -- -- -- -- -- --     isProp-emptyNFAParse' {w} (ε-cons x x₁) (nil x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --       ⊥.rec (fzero≠fone (cong lower x₂))
-- -- -- -- -- -- -- -- -- -- --     isProp-emptyNFAParse' {w} (ε-cons x x₁) (ε-cons x₂ y) =
-- -- -- -- -- -- -- -- -- -- --       cong₂ (λ a b →
-- -- -- -- -- -- -- -- -- -- --         NFATrace.ε-cons {emptyNFA} {lift fzero}{lift (fsuc fzero)} a {w} b)
-- -- -- -- -- -- -- -- -- -- --         (isSetLift isSetFin _ _ x x₂) (a _ _)
-- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- --       a : isProp (NFATrace emptyNFA (lift (fsuc fzero)) (lift (fsuc fzero)) w)
-- -- -- -- -- -- -- -- -- -- --       a (nil x x₁) (nil x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --         cong₂ (λ a b → NFATrace.nil {emptyNFA} a {w} b)
-- -- -- -- -- -- -- -- -- -- --           (isSetLift isSetFin _ _ x x₂) (isSetString _ _ x₁ x₃)
-- -- -- -- -- -- -- -- -- -- --       a (nil x x₁) (ε-cons x₂ y) = ⊥.rec (fzero≠fone (cong lower x₂))
-- -- -- -- -- -- -- -- -- -- --       a (ε-cons x x₁) (nil x₂ x₃) = ⊥.rec (fzero≠fone (cong lower x))
-- -- -- -- -- -- -- -- -- -- --       a (ε-cons x x₁) (ε-cons x₂ y) = ⊥.rec (fzero≠fone (cong lower x))

-- -- -- -- -- -- -- -- -- -- --     ε-regex-iso : isStronglyEquivalent ε-grammar (Parses emptyNFA)
-- -- -- -- -- -- -- -- -- -- --     fst (fst (fun (ε-regex-iso w) p)) = _
-- -- -- -- -- -- -- -- -- -- --     snd (fst (fun (ε-regex-iso w) p)) = refl
-- -- -- -- -- -- -- -- -- -- --     snd (fun (ε-regex-iso w) p) = ε-cons refl (nil refl p)
-- -- -- -- -- -- -- -- -- -- --     inv (ε-regex-iso w) p = elimEmptyNFA (p .snd)
-- -- -- -- -- -- -- -- -- -- --     rightInv (ε-regex-iso w) b =
-- -- -- -- -- -- -- -- -- -- --       Σ≡Prop
-- -- -- -- -- -- -- -- -- -- --         (λ x → transport
-- -- -- -- -- -- -- -- -- -- --           (cong (λ a → isProp (NFATrace _ _ a _ )) (sym (x .snd)))
-- -- -- -- -- -- -- -- -- -- --         isProp-emptyNFAParse') (ΣPathP ((sym (b .fst .snd)) ,
-- -- -- -- -- -- -- -- -- -- --           (isSet→SquareP ((λ _ _ → isSetLift isSetFin)) _ _ _ _)))
-- -- -- -- -- -- -- -- -- -- --     leftInv (ε-regex-iso w) a = isSetString w [] _ _

-- -- -- -- -- -- -- -- -- -- --     literal-P : ∀ {c} → (q q' : (literalNFA c) .Q .fst) → Grammar
-- -- -- -- -- -- -- -- -- -- --     literal-P (lift fzero) (lift fzero) = ε-grammar
-- -- -- -- -- -- -- -- -- -- --     literal-P {c} (lift fzero) (lift (fsuc fzero)) = literal c
-- -- -- -- -- -- -- -- -- -- --     literal-P (lift (fsuc fzero)) (lift fzero) = ⊥-grammar
-- -- -- -- -- -- -- -- -- -- --     literal-P (lift (fsuc fzero)) (lift (fsuc fzero)) = ε-grammar

-- -- -- -- -- -- -- -- -- -- --     elimLiteralNFA :
-- -- -- -- -- -- -- -- -- -- --       ∀ {q}{q'}{c} →
-- -- -- -- -- -- -- -- -- -- --       ParseTransformer
-- -- -- -- -- -- -- -- -- -- --         (NFATrace (literalNFA c) q q') (literal-P {c} q q')
-- -- -- -- -- -- -- -- -- -- --     elimLiteralNFA {q}{q'}{c} p =
-- -- -- -- -- -- -- -- -- -- --       elimNFA
-- -- -- -- -- -- -- -- -- -- --         (literalNFA c)
-- -- -- -- -- -- -- -- -- -- --         literal-P
-- -- -- -- -- -- -- -- -- -- --         the-nil-case
-- -- -- -- -- -- -- -- -- -- --         the-cons-case
-- -- -- -- -- -- -- -- -- -- --         the-ε-cons-case
-- -- -- -- -- -- -- -- -- -- --         p
-- -- -- -- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- -- -- -- --         the-nil-case : ∀ {q} → ParseTransformer ε-grammar (literal-P {c} q q)
-- -- -- -- -- -- -- -- -- -- --         the-nil-case {lift fzero} p = p
-- -- -- -- -- -- -- -- -- -- --         the-nil-case {lift (fsuc fzero)} p = p

-- -- -- -- -- -- -- -- -- -- --         the-cons-case : ∀ {q}{q'} → (lift fzero ≡ q) →
-- -- -- -- -- -- -- -- -- -- --           ParseTransformer
-- -- -- -- -- -- -- -- -- -- --             (literal c ⊗ literal-P (lift (fsuc fzero)) q') (literal-P q q')
-- -- -- -- -- -- -- -- -- -- --         the-cons-case {lift fzero} {lift (fsuc fzero)} p par =
-- -- -- -- -- -- -- -- -- -- --           (par .fst .snd ∙
-- -- -- -- -- -- -- -- -- -- --             cong (λ a → _ ++ a) (par .snd .snd) ∙
-- -- -- -- -- -- -- -- -- -- --             ++-unit-r (par .fst .fst .fst)) ∙
-- -- -- -- -- -- -- -- -- -- --             par .snd .fst
-- -- -- -- -- -- -- -- -- -- --         the-cons-case {lift (fsuc fzero)} {lift (fsuc fzero)} p par =
-- -- -- -- -- -- -- -- -- -- --           ⊥.rec (fzero≠fone (cong lower p))

-- -- -- -- -- -- -- -- -- -- --         the-ε-cons-case : ∀ {q}{q'}{t} → (literalNFA c) .ε-src t ≡ q →
-- -- -- -- -- -- -- -- -- -- --           ParseTransformer
-- -- -- -- -- -- -- -- -- -- --             (literal-P ((literalNFA c) .ε-dst t) q')
-- -- -- -- -- -- -- -- -- -- --             (literal-P q q')
-- -- -- -- -- -- -- -- -- -- --         the-ε-cons-case {t = t} = ⊥.rec (lower t)


-- -- -- -- -- -- -- -- -- -- --     isProp-literalNFAParse' : ∀ {w}{c} →
-- -- -- -- -- -- -- -- -- -- --       isProp (NFATrace (literalNFA c) (lift fzero) (lift (fsuc fzero)) w)
-- -- -- -- -- -- -- -- -- -- --     isProp-literalNFAParse' {w} {c} (nil x x₁) (nil x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --       ⊥.rec (fzero≠fone (cong lower x))
-- -- -- -- -- -- -- -- -- -- --     isProp-literalNFAParse' {w} {c} (nil x x₁) (cons x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --       ⊥.rec (fzero≠fone (cong lower x))
-- -- -- -- -- -- -- -- -- -- --     isProp-literalNFAParse' {w} {c} (cons x x₁) (nil x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --       ⊥.rec (fzero≠fone (cong lower x₂))
-- -- -- -- -- -- -- -- -- -- --     isProp-literalNFAParse' {w} {c} (cons x x₁) (cons x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --       cong₂ (λ a b → NFATrace.cons {literalNFA c}
-- -- -- -- -- -- -- -- -- -- --         {_}{lift (fsuc fzero)} a {w} b) (isSetLift isSetFin _ _ x x₂) a
-- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- --       b : ∀ {w'} → isProp (NFATrace (literalNFA c) (lift (fsuc fzero))
-- -- -- -- -- -- -- -- -- -- --         (lift (fsuc fzero)) w')
-- -- -- -- -- -- -- -- -- -- --       b {w'} (nil x x₁) (nil x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --         cong₂ (λ a b → NFATrace.nil {literalNFA c} a {w'} b)
-- -- -- -- -- -- -- -- -- -- --           (isSetLift isSetFin _ _ x x₂) (isSetString w' [] _ _)
-- -- -- -- -- -- -- -- -- -- --       b (nil x x₁) (cons x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --         ⊥.rec (fzero≠fone (cong lower x₂))
-- -- -- -- -- -- -- -- -- -- --       b (cons x x₁) (nil x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --         ⊥.rec (fzero≠fone (cong lower x))
-- -- -- -- -- -- -- -- -- -- --       b (cons x x₁) (cons x₂ x₃) =
-- -- -- -- -- -- -- -- -- -- --         ⊥.rec (fzero≠fone (cong lower x₂))

-- -- -- -- -- -- -- -- -- -- --       a : x₁ ≡ x₃
-- -- -- -- -- -- -- -- -- -- --       a = Σ≡Prop (λ s → isProp× (isSetString _ _) b)
-- -- -- -- -- -- -- -- -- -- --         (Σ≡Prop (λ _ → isSetString _ _)
-- -- -- -- -- -- -- -- -- -- --           (ΣPathP (fsts-agree , snds-agree)))
-- -- -- -- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- -- -- -- --         fsts-agree = (x₁ .snd .fst ∙ (sym (x₃ .snd .fst)))
-- -- -- -- -- -- -- -- -- -- --         snds-agree =
-- -- -- -- -- -- -- -- -- -- --           cons-inj₂ (
-- -- -- -- -- -- -- -- -- -- --           cong (λ a → a ++ x₁ .fst .fst .snd) (sym (x₁ .snd .fst)) ∙
-- -- -- -- -- -- -- -- -- -- --           sym (x₁ .fst .snd) ∙ (x₃ .fst .snd) ∙
-- -- -- -- -- -- -- -- -- -- --           cong (λ a → a ++ x₃ .fst .fst .snd) (x₃ .snd .fst))

-- -- -- -- -- -- -- -- -- -- --     literal-regex-iso : ∀ {c} →
-- -- -- -- -- -- -- -- -- -- --       isStronglyEquivalent (literal c) (Parses (literalNFA c))
-- -- -- -- -- -- -- -- -- -- --     fst (fst (fun (literal-regex-iso {c} w) p)) = lift (inr (inl tt))
-- -- -- -- -- -- -- -- -- -- --     snd (fst (fun (literal-regex-iso {c} w) p)) = refl
-- -- -- -- -- -- -- -- -- -- --     snd (fun (literal-regex-iso {c} w) p) =
-- -- -- -- -- -- -- -- -- -- --       cons refl ((([ c ] , []) , p) , (refl , (nil refl refl)))
-- -- -- -- -- -- -- -- -- -- --     inv (literal-regex-iso {c} w) p =
-- -- -- -- -- -- -- -- -- -- --        elimLiteralNFA {q = lift fzero} {q' = lift (fsuc fzero)} {c = c}
-- -- -- -- -- -- -- -- -- -- --          (transport (cong (λ a → NFATrace _ _ a _) (p .fst .snd)) (p .snd))
-- -- -- -- -- -- -- -- -- -- --     rightInv (literal-regex-iso {c} w) b =
-- -- -- -- -- -- -- -- -- -- --       Σ≡Prop (λ x → transport (cong (λ a → isProp (NFATrace _ _ a _))
-- -- -- -- -- -- -- -- -- -- --         (sym (x .snd))) isProp-literalNFAParse')
-- -- -- -- -- -- -- -- -- -- --           (Σ≡Prop (λ x → isSetLift isSetFin _ _) (sym (b .fst .snd)))
-- -- -- -- -- -- -- -- -- -- --     leftInv (literal-regex-iso {c} w) a = isSetString w [ c ] _ _

-- -- -- -- -- -- -- -- -- -- --     module _
-- -- -- -- -- -- -- -- -- -- --       (g h : RegularGrammar)
-- -- -- -- -- -- -- -- -- -- --       (isog : isStronglyEquivalent
-- -- -- -- -- -- -- -- -- -- --         (RegularGrammar→Grammar g)
-- -- -- -- -- -- -- -- -- -- --         (Parses (NFAfromRegularGrammar g)))
-- -- -- -- -- -- -- -- -- -- --       (isoh : isStronglyEquivalent
-- -- -- -- -- -- -- -- -- -- --         (RegularGrammar→Grammar h)
-- -- -- -- -- -- -- -- -- -- --         (Parses (NFAfromRegularGrammar h)))
-- -- -- -- -- -- -- -- -- -- --         where

-- -- -- -- -- -- -- -- -- -- --       g' = (RegularGrammar→Grammar g)
-- -- -- -- -- -- -- -- -- -- --       h' = (RegularGrammar→Grammar h)
-- -- -- -- -- -- -- -- -- -- --       NFAg = (NFAfromRegularGrammar g)
-- -- -- -- -- -- -- -- -- -- --       NFAh = (NFAfromRegularGrammar h)
-- -- -- -- -- -- -- -- -- -- --       Ng = NFATrace (NFAfromRegularGrammar g)
-- -- -- -- -- -- -- -- -- -- --       Parses-g = Parses (NFAfromRegularGrammar g)
-- -- -- -- -- -- -- -- -- -- --       Nh = NFATrace (NFAfromRegularGrammar h)
-- -- -- -- -- -- -- -- -- -- --       Parses-h = Parses (NFAfromRegularGrammar h)

-- -- -- -- -- -- -- -- -- -- --       g⊗h' = (RegularGrammar→Grammar (g GrammarDefs.⊗Reg h))
-- -- -- -- -- -- -- -- -- -- --       NFAg⊗h = (NFAfromRegularGrammar (g GrammarDefs.⊗Reg h))
-- -- -- -- -- -- -- -- -- -- --       N⊗ = NFATrace (NFAfromRegularGrammar (g GrammarDefs.⊗Reg h))
-- -- -- -- -- -- -- -- -- -- --       Parses-⊗ = Parses (NFAfromRegularGrammar (g GrammarDefs.⊗Reg h))

-- -- -- -- -- -- -- -- -- -- --       -- Remember that this is sensitive to the encoding of the ⊗NFA
-- -- -- -- -- -- -- -- -- -- --       Nh→N⊗ : ∀ {q}{q'} →
-- -- -- -- -- -- -- -- -- -- --         ParseTransformer (Nh q q') (N⊗ (inr q) (inr q'))
-- -- -- -- -- -- -- -- -- -- --       Nh→N⊗ (nil x x₁) = nil (cong inr x) x₁
-- -- -- -- -- -- -- -- -- -- --       Nh→N⊗ (cons {t} x x₁) =
-- -- -- -- -- -- -- -- -- -- --         cons {t = inr t} (cong inr x) ((x₁ .fst) , ((x₁ .snd .fst) ,
-- -- -- -- -- -- -- -- -- -- --           (Nh→N⊗ (x₁ .snd .snd))))
-- -- -- -- -- -- -- -- -- -- --       Nh→N⊗ (ε-cons {t} x x₁) =
-- -- -- -- -- -- -- -- -- -- --         ε-cons {t = inr (inr t)} (cong inr x) (Nh→N⊗ x₁)

-- -- -- -- -- -- -- -- -- -- --       -- parses from the h segment to the end
-- -- -- -- -- -- -- -- -- -- --       N⊗h = LinΣ[ q ∈ Accepting NFAh ] Nh (NFAh .init) (q .fst)

-- -- -- -- -- -- -- -- -- -- --       Ng→N⊗ : ∀ {q}{q'} →
-- -- -- -- -- -- -- -- -- -- --         ParseTransformer (Ng q q') (N⊗ (inl q) (inl q'))
-- -- -- -- -- -- -- -- -- -- --       Ng→N⊗ (nil x x₁) = nil (cong inl x) x₁
-- -- -- -- -- -- -- -- -- -- --       Ng→N⊗ (cons {t} x x₁) =
-- -- -- -- -- -- -- -- -- -- --         cons {t = inl t} (cong inl x) ((x₁ .fst) , ((x₁ .snd .fst) ,
-- -- -- -- -- -- -- -- -- -- --           (Ng→N⊗ (x₁ .snd .snd))))
-- -- -- -- -- -- -- -- -- -- --       Ng→N⊗ (ε-cons {t} x x₁) =
-- -- -- -- -- -- -- -- -- -- --         ε-cons {t = inr (inl t)} (cong inl x) (Ng→N⊗ x₁)

-- -- -- -- -- -- -- -- -- -- --       Parses-g⊗Parses-h→Parses⊗ :
-- -- -- -- -- -- -- -- -- -- --         ParseTransformer (Parses-g ⊗ Parses-h) Parses-⊗
-- -- -- -- -- -- -- -- -- -- --       fst (Parses-g⊗Parses-h→Parses⊗ (split , pg , ph)) =
-- -- -- -- -- -- -- -- -- -- --         (inr (ph .fst .fst)) , ph .fst .snd
-- -- -- -- -- -- -- -- -- -- --       snd (Parses-g⊗Parses-h→Parses⊗ (split , pg , ph)) =
-- -- -- -- -- -- -- -- -- -- --         transport
-- -- -- -- -- -- -- -- -- -- --         (cong (λ a → NFATrace _ _ _ a) (sym (split .snd)))
-- -- -- -- -- -- -- -- -- -- --         (
-- -- -- -- -- -- -- -- -- -- --         concatTrace
-- -- -- -- -- -- -- -- -- -- --           NFAg⊗h
-- -- -- -- -- -- -- -- -- -- --           (split .fst .fst)
-- -- -- -- -- -- -- -- -- -- --           (split .fst .snd)
-- -- -- -- -- -- -- -- -- -- --           (Ng→N⊗ (pg .snd))
-- -- -- -- -- -- -- -- -- -- --           (ε-cons {t = inl (pg .fst)} refl (Nh→N⊗ (ph .snd)))
-- -- -- -- -- -- -- -- -- -- --         )

-- -- -- -- -- -- -- -- -- -- --       g⊗h→Parses⊗ :
-- -- -- -- -- -- -- -- -- -- --         ParseTransformer (g' ⊗ h') Parses-⊗
-- -- -- -- -- -- -- -- -- -- --       g⊗h→Parses⊗ (split , pg , ph) =
-- -- -- -- -- -- -- -- -- -- --         Parses-g⊗Parses-h→Parses⊗ (split ,
-- -- -- -- -- -- -- -- -- -- --           ((isog (split .fst .fst) .fun pg) ,
-- -- -- -- -- -- -- -- -- -- --           (isoh (split .fst .snd) .fun ph)))


-- -- -- -- -- -- -- -- -- -- --       ⊗-P : (q q' : Q NFAg⊗h .fst) → Grammar
-- -- -- -- -- -- -- -- -- -- --       ⊗-P (inl x) (inl y) = Ng x y
-- -- -- -- -- -- -- -- -- -- --       ⊗-P (inl x) (inr y) =
-- -- -- -- -- -- -- -- -- -- --         ε-grammar &
-- -- -- -- -- -- -- -- -- -- --         (NFA.acc? NFAg x & NFA.init? NFAh y)
-- -- -- -- -- -- -- -- -- -- --       ⊗-P (inr x) (inl y) = ⊥-grammar
-- -- -- -- -- -- -- -- -- -- --       ⊗-P (inr x) (inr y) = Nh x y

-- -- -- -- -- -- -- -- -- -- --       N⊗→g⊗h : ∀ {q}{q'} →
-- -- -- -- -- -- -- -- -- -- --         ParseTransformer (N⊗ q q') (g' ⊗ h')
-- -- -- -- -- -- -- -- -- -- --       N⊗→g⊗h {q} {q'} =
-- -- -- -- -- -- -- -- -- -- --         elimNFA
-- -- -- -- -- -- -- -- -- -- --           NFAg⊗h
-- -- -- -- -- -- -- -- -- -- --           (λ v v₁ → _)
-- -- -- -- -- -- -- -- -- -- --           {!!}
-- -- -- -- -- -- -- -- -- -- --           {!!}
-- -- -- -- -- -- -- -- -- -- --           {!!}
-- -- -- -- -- -- -- -- -- -- --           {q}
-- -- -- -- -- -- -- -- -- -- --           {q'}
-- -- -- -- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- -- -- -- --         the-nil-case : ∀ {q} → ParseTransformer ε-grammar (⊗-P q q)
-- -- -- -- -- -- -- -- -- -- --         the-nil-case {inl q} x = nil refl x
-- -- -- -- -- -- -- -- -- -- --         the-nil-case {inr q} x = nil refl x

-- -- -- -- -- -- -- -- -- -- --         the-cons-case : ∀ {q}{q'}{t} → NFAg⊗h .src t ≡ q →
-- -- -- -- -- -- -- -- -- -- --           ParseTransformer
-- -- -- -- -- -- -- -- -- -- --             (literal (NFAg⊗h .label t) ⊗ ⊗-P (NFAg⊗h .dst t) q')
-- -- -- -- -- -- -- -- -- -- --             (⊗-P q q')
-- -- -- -- -- -- -- -- -- -- --         the-cons-case {inl x} {inl x₁} {inl x₂} srct p =
-- -- -- -- -- -- -- -- -- -- --           cons {t = x₂} (isEmbedding→Inj isEmbedding-inl _ _ srct) p
-- -- -- -- -- -- -- -- -- -- --         the-cons-case {inl x} {inr x₁} {inl x₂} srct (a , b , c , d , e) =
-- -- -- -- -- -- -- -- -- -- --           {!!} , ({!d!} , {!!})
-- -- -- -- -- -- -- -- -- -- --           -- elimDecProp-PT
-- -- -- -- -- -- -- -- -- -- --           --   (((init (NFAfromRegularGrammar h) ≡ x₁) ,
-- -- -- -- -- -- -- -- -- -- --           --     (isFinSet→isSet (NFAh .Q .snd) _ _)) ,
-- -- -- -- -- -- -- -- -- -- --           --     decEqQ (NFAh) (NFAh .init) x₁)
-- -- -- -- -- -- -- -- -- -- --           --   _
-- -- -- -- -- -- -- -- -- -- --           --   (λ _ isInit →
-- -- -- -- -- -- -- -- -- -- --           --     elimDecProp-PT
-- -- -- -- -- -- -- -- -- -- --           --     _
-- -- -- -- -- -- -- -- -- -- --           --     _
-- -- -- -- -- -- -- -- -- -- --           --     (λ _ isAcc → {!!} , ({!!} , {!!}))
-- -- -- -- -- -- -- -- -- -- --           --     {!!}
-- -- -- -- -- -- -- -- -- -- --           --     d)
-- -- -- -- -- -- -- -- -- -- --           --   (λ _ notInit → {!!})
-- -- -- -- -- -- -- -- -- -- --           --   e
-- -- -- -- -- -- -- -- -- -- --         the-cons-case {inl x} {inr x₁} {fsuc x₂} srct p =
-- -- -- -- -- -- -- -- -- -- --           ⊥.rec (lower (Cubical.Data.Sum.⊎Path.Cover≃Path
-- -- -- -- -- -- -- -- -- -- --             _ _ .snd .equiv-proof srct .fst .fst))
-- -- -- -- -- -- -- -- -- -- --         the-cons-case {inr x} {inl x₁} {inl x₂} srct p =
-- -- -- -- -- -- -- -- -- -- --           Cubical.Data.Sum.⊎Path.Cover≃Path
-- -- -- -- -- -- -- -- -- -- --             _ _ .snd .equiv-proof srct .fst .fst
-- -- -- -- -- -- -- -- -- -- --         the-cons-case {inr x} {inr x₁} {inl x₂} srct p =
-- -- -- -- -- -- -- -- -- -- --           ⊥.rec (
-- -- -- -- -- -- -- -- -- -- --           lower (Cubical.Data.Sum.⊎Path.Cover≃Path
-- -- -- -- -- -- -- -- -- -- --             _ _ .snd .equiv-proof srct .fst .fst)
-- -- -- -- -- -- -- -- -- -- --           )
-- -- -- -- -- -- -- -- -- -- --         the-cons-case {inr x} {inr x₁} {inr x₂} srct p =
-- -- -- -- -- -- -- -- -- -- --           cons {t = x₂} (isEmbedding→Inj isEmbedding-inr _ _ srct) p

-- -- -- -- -- -- -- -- -- -- --         the-ε-cons-case : ∀ {q}{q'}{t} → NFAg⊗h .ε-src t ≡ q →
-- -- -- -- -- -- -- -- -- -- --           ParseTransformer
-- -- -- -- -- -- -- -- -- -- --           (⊗-P (NFAg⊗h .ε-dst t) q')
-- -- -- -- -- -- -- -- -- -- --           (⊗-P q q')
-- -- -- -- -- -- -- -- -- -- --         the-ε-cons-case = {!!}
-- -- -- -- -- -- -- -- -- -- --         -- the-ε-cons-case {inl x} {inl x₁} {fsuc (inl x₂)} srct p =
-- -- -- -- -- -- -- -- -- -- --         --   ε-cons {t = x₂} (isEmbedding→Inj isEmbedding-inl _ _ srct) p
-- -- -- -- -- -- -- -- -- -- --         -- the-ε-cons-case {inl x} {fsuc x₁} {inl x₂} srct p = {!!}
-- -- -- -- -- -- -- -- -- -- --         -- the-ε-cons-case {inl x} {fsuc x₁} {fsuc (fsuc x₂)} srct p =
-- -- -- -- -- -- -- -- -- -- --         --   ⊥.rec (
-- -- -- -- -- -- -- -- -- -- --         --   lower (Cubical.Data.Sum.⊎Path.Cover≃Path
-- -- -- -- -- -- -- -- -- -- --         --     _ _ .snd .equiv-proof srct .fst .fst)
-- -- -- -- -- -- -- -- -- -- --         --   )
-- -- -- -- -- -- -- -- -- -- --         -- the-ε-cons-case {fsuc x} {inl x₁} {fsuc (inl x₂)} srct p =
-- -- -- -- -- -- -- -- -- -- --         --   Cubical.Data.Sum.⊎Path.Cover≃Path
-- -- -- -- -- -- -- -- -- -- --         --     _ _ .snd .equiv-proof srct .fst .fst
-- -- -- -- -- -- -- -- -- -- --         -- the-ε-cons-case {fsuc x} {fsuc x₁} {inl x₂} srct p = {!p!}
-- -- -- -- -- -- -- -- -- -- --         -- the-ε-cons-case {fsuc x} {fsuc x₁} {fsuc (inl x₂)} srct p = {!!}
-- -- -- -- -- -- -- -- -- -- --         -- the-ε-cons-case {fsuc x} {fsuc x₁} {fsuc (fsuc x₂)} srct p =
-- -- -- -- -- -- -- -- -- -- --         --   ε-cons {t = x₂} (isEmbedding→Inj isEmbedding-inr _ _ srct) p

-- -- -- -- -- -- -- -- -- -- --       ⊗NFA-regex-iso :
-- -- -- -- -- -- -- -- -- -- --         isStronglyEquivalent
-- -- -- -- -- -- -- -- -- -- --           (RegularGrammar→Grammar (g GrammarDefs.⊗Reg h))
-- -- -- -- -- -- -- -- -- -- --           (Parses (NFAfromRegularGrammar (g GrammarDefs.⊗Reg h)))
-- -- -- -- -- -- -- -- -- -- --       fun (⊗NFA-regex-iso w) = {!!}
-- -- -- -- -- -- -- -- -- -- --       inv (⊗NFA-regex-iso w) = {!!}
-- -- -- -- -- -- -- -- -- -- --       rightInv (⊗NFA-regex-iso w) = {!!}
-- -- -- -- -- -- -- -- -- -- --       leftInv (⊗NFA-regex-iso w) = {!!}

-- -- -- -- -- -- -- -- -- -- --     ⊕NFA-regex-iso :
-- -- -- -- -- -- -- -- -- -- --       (g h : RegularGrammar) →
-- -- -- -- -- -- -- -- -- -- --       (isStronglyEquivalent
-- -- -- -- -- -- -- -- -- -- --         (RegularGrammar→Grammar g)
-- -- -- -- -- -- -- -- -- -- --         (Parses (NFAfromRegularGrammar g))) →
-- -- -- -- -- -- -- -- -- -- --       (isStronglyEquivalent
-- -- -- -- -- -- -- -- -- -- --         (RegularGrammar→Grammar h)
-- -- -- -- -- -- -- -- -- -- --         (Parses (NFAfromRegularGrammar h))) →
-- -- -- -- -- -- -- -- -- -- --       isStronglyEquivalent
-- -- -- -- -- -- -- -- -- -- --         (RegularGrammar→Grammar (g GrammarDefs.⊕Reg h))
-- -- -- -- -- -- -- -- -- -- --         (Parses (NFAfromRegularGrammar (g GrammarDefs.⊕Reg h)))
-- -- -- -- -- -- -- -- -- -- --     fun (⊕NFA-regex-iso g h isog isoh w) = {!!}
-- -- -- -- -- -- -- -- -- -- --     inv (⊕NFA-regex-iso g h isog isoh w) = {!!}
-- -- -- -- -- -- -- -- -- -- --     rightInv (⊕NFA-regex-iso g h isog isoh w) = {!!}
-- -- -- -- -- -- -- -- -- -- --     leftInv (⊕NFA-regex-iso g h isog isoh w) = {!!}

-- -- -- -- -- -- -- -- -- -- --     isStronglyEquivalent-NFA-Regex : (g : RegularGrammar) →
-- -- -- -- -- -- -- -- -- -- --       isStronglyEquivalent
-- -- -- -- -- -- -- -- -- -- --         (RegularGrammar→Grammar g)
-- -- -- -- -- -- -- -- -- -- --         (Parses (NFAfromRegularGrammar g))
-- -- -- -- -- -- -- -- -- -- --     isStronglyEquivalent-NFA-Regex GrammarDefs.ε-Reg = ε-regex-iso
-- -- -- -- -- -- -- -- -- -- --     isStronglyEquivalent-NFA-Regex (GrammarDefs.literalReg x) =
-- -- -- -- -- -- -- -- -- -- --       literal-regex-iso
-- -- -- -- -- -- -- -- -- -- --     isStronglyEquivalent-NFA-Regex (g GrammarDefs.⊗Reg h) =
-- -- -- -- -- -- -- -- -- -- --       ⊗NFA-regex-iso g h
-- -- -- -- -- -- -- -- -- -- --         (isStronglyEquivalent-NFA-Regex g)
-- -- -- -- -- -- -- -- -- -- --         (isStronglyEquivalent-NFA-Regex h)
-- -- -- -- -- -- -- -- -- -- --     isStronglyEquivalent-NFA-Regex (g GrammarDefs.⊕Reg h) =
-- -- -- -- -- -- -- -- -- -- --       ⊕NFA-regex-iso g h
-- -- -- -- -- -- -- -- -- -- --         (isStronglyEquivalent-NFA-Regex g)
-- -- -- -- -- -- -- -- -- -- --         (isStronglyEquivalent-NFA-Regex h)
-- -- -- -- -- -- -- -- -- -- --     isStronglyEquivalent-NFA-Regex (GrammarDefs.KL*Reg g) w = {!!}
