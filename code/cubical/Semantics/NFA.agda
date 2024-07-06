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

    -- module _ (q-start q-mid : Q .fst) where
    --   open Algebra
    --   the-concat-alg : Algebra q-mid
    --   the-ℓs the-concat-alg _ = ℓN
    --   P the-concat-alg q-end = [ q-start →* q-mid ] -⊗ [ q-start →* q-end ]
    --   nil-case the-concat-alg =
    --     -⊗-intro {g = [ q-start →* q-mid ]} {h = ε-grammar}
    --       {k = [ q-start →* q-mid ]}
    --       (ε-extension-r {g = ε-grammar} {h = [ q-start →* q-mid ]}
    --         {k = [ q-start →* q-mid ]}
    --         (id {g = ε-grammar})
    --         (id {g = [ q-start →* q-mid ]}))
    --   cons-case the-concat-alg tr =
    --     -⊗-intro {g = [ q-start →* q-mid ]}
    --       {h = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ]) ⊗ literal (label tr)}
    --       {k = [ q-start →* dst tr ]}
    --       (⊗-assoc-inv {g = [ q-start →* q-mid ]}
    --         {h = [ q-start →* q-mid ] -⊗ [ q-start →* src tr ]}
    --         {k = literal (label tr)}
    --         {l = [ q-start →* dst tr ]}
    --         (trans
    --           {g = ([ q-start →* q-mid ] ⊗
    --             ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ]))
    --             ⊗ literal (label tr)}
    --           {h = [ q-start →* src tr ] ⊗ literal (label tr)}
    --           {k = [ q-start →* dst tr ]}
    --           (cut
    --             {g = [ q-start →* q-mid ] ⊗
    --               ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])}
    --             {h = [ q-start →* src tr ]}
    --             (var ⊗l literal (label tr))
    --             (-⊗-elim {g = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])}
    --               {h = [ q-start →* q-mid ]} {k = [ q-start →* src tr ]}
    --               {l = [ q-start →* q-mid ]}
    --               (id {g = ([ q-start →* q-mid ] -⊗ [ q-start →* src tr ])} )
    --               (id {g = [ q-start →* q-mid ]})))
    --           (cons tr)))
    --   ε-cons-case the-concat-alg εtr =
    --     cut {g = [ q-start →* ε-src εtr ]}
    --       {h = [ q-start →* ε-dst εtr ]}
    --       ([ q-start →* q-mid ] -⊗OH var)
    --       (ε-cons εtr)

    -- open AlgebraHom
    -- concatTrace : ∀ {q-start}{q-mid}{q-end} →
    --   [ q-start →* q-mid ] ⊗ [ q-mid →* q-end ] ⊢ [ q-start →* q-end ]
    -- concatTrace {q-start}{q-mid}{q-end} =
    --   -⊗-elim
    --    {g = [ q-mid →* q-end ]}
    --    {h = [ q-start →* q-mid ]} {k = [ q-start →* q-end ]}
    --    {l = [ q-start →* q-mid ]}
    --    (∃AlgebraHom q-mid (the-concat-alg q-start q-mid) .f q-end)
    --    (id {g = [ q-start →* q-mid ]})

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
