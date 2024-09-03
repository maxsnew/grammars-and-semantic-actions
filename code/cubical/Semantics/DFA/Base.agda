open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.DFA.Base ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Equivalence (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)
open import Semantics.Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

record DFA : Type (ℓ-suc ℓD) where
  field
    Q : FinSet ℓD
    init : ⟨ Q ⟩
    isAcc : ⟨ Q ⟩ → DecProp ℓD
    δ : ⟨ Q ⟩ → Σ₀ → ⟨ Q ⟩

  negate : DFA
  Q negate = Q
  init negate = init
  isAcc negate q = negateDecProp (isAcc q)
  δ negate = δ

  acc? : ⟨ Q ⟩ → Grammar ℓD
  acc? q = DecProp-grammar' {ℓG = ℓD} (isAcc q)

  rej? : ⟨ Q ⟩ → Grammar ℓD
  rej? q = DecProp-grammar' {ℓG = ℓD} (negateDecProp (isAcc q))

  module _ (q-end : ⟨ Q ⟩) where
    -- The grammar "Trace q" denotes the type of traces in the DFA
    -- from state q to q-end
    data Trace : (q : ⟨ Q ⟩) → Grammar ℓD where
      nil : ε-grammar ⊢ Trace q-end
      cons : ∀ q c →
        literal c ⊗ Trace (δ q c) ⊢ Trace q

    record Algebra : Typeω where
      field
        the-ℓs : ⟨ Q ⟩ → Level
        G : (q : ⟨ Q ⟩) → Grammar (the-ℓs q)
        nil-case : ε-grammar ⊢ G q-end
        cons-case : ∀ q c →
          literal c ⊗ G (δ q c) ⊢ G q

    open Algebra

    initial : Algebra
    the-ℓs initial _ = ℓD
    G initial = Trace
    nil-case initial = nil
    cons-case initial = cons

    record AlgebraHom (alg alg' : Algebra) : Typeω where
      field
        f : (q : ⟨ Q ⟩) → alg .G q ⊢ alg' .G q
        on-nil :
          f q-end ∘g alg .nil-case ≡ alg' .nil-case
        on-cons : ∀ q c →
          f q ∘g alg .cons-case q c ≡
            alg' .cons-case q c ∘g (⊗-intro id (f (δ q c)))
      fInit = f init

    open AlgebraHom

    idAlgebraHom : (alg : Algebra) →
      AlgebraHom alg alg
    f (idAlgebraHom alg) q = id
    on-nil (idAlgebraHom alg) = refl
    on-cons (idAlgebraHom alg) _ _ = refl

    AlgebraHom-seq : {alg alg' alg'' : Algebra} →
      AlgebraHom alg alg' → AlgebraHom alg' alg'' →
      AlgebraHom alg alg''
    AlgebraHom-seq ϕ ψ .f q = ψ .f q ∘g ϕ .f q
    AlgebraHom-seq ϕ ψ .on-nil =
      cong (ψ .f _ ∘g_) (ϕ .on-nil)  ∙
      ψ .on-nil
    AlgebraHom-seq ϕ ψ .on-cons q c =
      cong (ψ .f q ∘g_) (ϕ .on-cons q c) ∙
      cong (_∘g ⊗-intro id (ϕ .f (δ q c))) (ψ .on-cons q c)

    module _ (the-alg : Algebra) where
      recTrace : ∀ {q} → Trace q ⊢ the-alg .G q
      recTrace {q} w (nil .w pε) = the-alg .nil-case w pε
      recTrace {q} w (cons .q c .w p⊗) =
        the-alg .cons-case q c _
          (p⊗ .fst , (p⊗ .snd .fst) , (recTrace _ (p⊗ .snd .snd)))

      recInit : Trace init ⊢ the-alg .G init
      recInit = recTrace

      ∃AlgebraHom : AlgebraHom initial the-alg
      f ∃AlgebraHom q = recTrace {q}
      on-nil ∃AlgebraHom = refl
      on-cons ∃AlgebraHom _ _ = refl

      !AlgebraHom-help :
        (e : AlgebraHom initial the-alg) →
        (q : ⟨ Q ⟩) →
        (∀ w p → e .f q w p ≡ recTrace w p)
      !AlgebraHom-help e q w (nil .w pε) =
        cong (λ a → a w pε) (e .on-nil)
      !AlgebraHom-help e q w (cons .q c .w p⊗) =
        cong (λ a → a w p⊗) (e .on-cons q c) ∙
        cong (λ a → the-alg .cons-case q c _
          ((p⊗ .fst) , ((p⊗ .snd .fst) , a)))
          (!AlgebraHom-help e (δ q c) _
            (p⊗ .snd .snd))

      !AlgebraHom :
        (e : AlgebraHom initial the-alg) →
        (q : ⟨ Q ⟩) →
        e .f q ≡ recTrace {q}
      !AlgebraHom e q =
        funExt (λ w → funExt (λ p → !AlgebraHom-help e q w p))

      -- TODO rename
      !AlgebraHom' :
        (e e' : AlgebraHom initial the-alg) →
        (q : ⟨ Q ⟩) →
        e .f q ≡ e' .f q
      !AlgebraHom' e e' q =
        !AlgebraHom e q ∙
        sym (!AlgebraHom e' q)

    initial→initial≡id :
      (e : AlgebraHom initial initial) →
      (q : ⟨ Q ⟩) →
      (e .f q)
         ≡
      id
    initial→initial≡id e q =
      !AlgebraHom initial e q ∙
      sym (!AlgebraHom initial (idAlgebraHom initial) q)

    algebra-η :
      (e : AlgebraHom initial initial) →
      fInit e ≡ id
    algebra-η e = initial→initial≡id e _

  module _ (q-start : ⟨ Q ⟩) where
    data SnocTrace : (q : ⟨ Q ⟩) → Grammar ℓD where
      nil : ε-grammar ⊢ SnocTrace q-start
      snoc : ∀ q c →
        SnocTrace q ⊗ literal c ⊢ SnocTrace (δ q c)

    InitSnocTrace : Grammar ℓD
    InitSnocTrace = SnocTrace init

    record SnocAlgebra : Typeω where
      field
        the-ℓs : ⟨ Q ⟩ → Level
        G : (q : ⟨ Q ⟩) → Grammar (the-ℓs q)
        nil-case : ε-grammar ⊢ G q-start
        snoc-case : ∀ q c →
          G q ⊗ literal c ⊢ G (δ q c)

    open SnocAlgebra

    initialSnoc : SnocAlgebra
    initialSnoc .the-ℓs _ = ℓD
    initialSnoc .G = SnocTrace
    initialSnoc .nil-case = nil
    initialSnoc .snoc-case = snoc

    record SnocAlgebraHom (alg alg' : SnocAlgebra) : Typeω where
      field
        f : (q : ⟨ Q ⟩) → alg .G q ⊢ alg' .G q
        on-nil :
          f q-start ∘g alg .nil-case ≡ alg' .nil-case
        on-snoc : ∀ q c →
          f (δ q c) ∘g alg .snoc-case q c ≡
            alg' .snoc-case q c ∘g ⊗-intro (f q) id

    open SnocAlgebraHom

    idSnocAlgebraHom : (alg : SnocAlgebra) →
      SnocAlgebraHom alg alg
    f (idSnocAlgebraHom alg) q = id
    on-nil (idSnocAlgebraHom alg) = refl
    on-snoc (idSnocAlgebraHom alg) _ _ = refl

    SnocAlgebraHom-seq : {alg alg' alg'' : SnocAlgebra} →
      SnocAlgebraHom alg alg' → SnocAlgebraHom alg' alg'' →
      SnocAlgebraHom alg alg''
    SnocAlgebraHom-seq ϕ ψ .f q = ψ .f q ∘g ϕ .f q
    SnocAlgebraHom-seq ϕ ψ .on-nil =
      cong (ψ .f _ ∘g_) (ϕ .on-nil) ∙
      ψ .on-nil
    SnocAlgebraHom-seq ϕ ψ .on-snoc q c =
      cong (ψ .f (δ q c) ∘g_) (ϕ .on-snoc q c) ∙
      cong (_∘g ⊗-intro (ϕ .f q) id) (ψ .on-snoc q c)

    module _ (the-alg : SnocAlgebra) where
      recSnocTrace : ∀ {q} → SnocTrace q ⊢ the-alg .G q
      recSnocTrace {q} w (nil .w pε) = the-alg .nil-case w pε
      recSnocTrace {q} w (snoc _ c .w p⊗) =
        the-alg .snoc-case _ c _
          ((p⊗ .fst) , (recSnocTrace _ (p⊗ .snd .fst) , p⊗ .snd .snd))

      recSnocInit : SnocTrace init ⊢ the-alg .G init
      recSnocInit = recSnocTrace

      ∃SnocAlgebraHom : SnocAlgebraHom initialSnoc the-alg
      f ∃SnocAlgebraHom q = recSnocTrace {q}
      on-nil ∃SnocAlgebraHom = refl
      on-snoc ∃SnocAlgebraHom _ _ = refl

      !SnocAlgebraHom-help :
        (e : SnocAlgebraHom initialSnoc the-alg) →
        (q : ⟨ Q ⟩) →
        (∀ w p → e .f q w p ≡ recSnocTrace w p)
      !SnocAlgebraHom-help e q w (nil .w pε) =
        cong (λ a → a w pε) (e .on-nil)
      !SnocAlgebraHom-help e q w (snoc _ c .w p⊗) =
        cong (λ a → a w p⊗) (e .on-snoc _ c) ∙
        cong (λ a → the-alg .snoc-case _ c _
          ((p⊗ .fst) , (a , (p⊗ .snd .snd))))
          (!SnocAlgebraHom-help e _ _ (p⊗ .snd .fst))

      !SnocAlgebraHom :
        (e : SnocAlgebraHom initialSnoc the-alg) →
        (q : ⟨ Q ⟩) →
        e .f q ≡ recSnocTrace {q}
      !SnocAlgebraHom e q =
        funExt (λ w → funExt (λ p → !SnocAlgebraHom-help e q w p))

      -- TODO rename
      !SnocAlgebraHom' :
        (e e' : SnocAlgebraHom initialSnoc the-alg) →
        (q : ⟨ Q ⟩) →
        e .f q ≡ e' .f q
      !SnocAlgebraHom' e e' q =
        !SnocAlgebraHom e q ∙
        sym (!SnocAlgebraHom e' q)

    initialSnoc→initialSnoc≡id :
      (e : SnocAlgebraHom initialSnoc initialSnoc) →
      (q : ⟨ Q ⟩) →
      (e .f q)
         ≡
      id
    initialSnoc→initialSnoc≡id e q =
      !SnocAlgebraHom initialSnoc e q ∙
      sym (!SnocAlgebraHom initialSnoc (idSnocAlgebraHom initialSnoc) q)

    snocAlgebra-η :
      (e : SnocAlgebraHom initialSnoc initialSnoc) →
      e .f init ≡ id
    snocAlgebra-η e = initialSnoc→initialSnoc≡id e _

  module _ (q-start q-end : ⟨ Q ⟩) where
    open Algebra
    open AlgebraHom
    open SnocAlgebra
    open SnocAlgebraHom

    alg : Algebra q-end
    alg .the-ℓs _ = ℓD
    alg .G q = SnocTrace q q-end
    alg .nil-case = nil
    alg .cons-case q c =
      -⊗-app ∘g
      ⊗-intro id (∃SnocAlgebraHom (δ q c) λsnocAlg .f q-end)
      where
      λsnocAlg : SnocAlgebra (δ q c)
      λsnocAlg .the-ℓs _ = ℓD
      λsnocAlg .G q' = literal c -⊗ SnocTrace q q'
      λsnocAlg .nil-case =
        -⊗-intro
          (snoc q c ∘g
          ⊗-intro SnocTrace.nil id ∘g
          ⊗-unit-l⁻ ∘g
          ⊗-unit-r)
      λsnocAlg .snoc-case q' c' =
        -⊗-intro
          (snoc q' c' ∘g
          ⊗-intro -⊗-app id ∘g
          ⊗-assoc)

    snocAlg : SnocAlgebra q-start
    snocAlg .the-ℓs _ = ℓD
    snocAlg .G q = Trace q q-start
    snocAlg .nil-case = nil
    snocAlg .snoc-case q c =
      ⟜-app ∘g
      ⊗-intro (∃AlgebraHom q λalg .f q-start) id
      where
      λalg : Algebra q
      λalg .the-ℓs _ = ℓD
      λalg .G q' = Trace (δ q c) q' ⊗- literal c
      λalg .nil-case =
        ⟜-intro
          (cons q c ∘g
          ⊗-intro id Trace.nil ∘g
          ⊗-unit-r⁻ ∘g
          ⊗-unit-l)
      λalg .cons-case q' c' =
        ⟜-intro
          (cons q' c' ∘g
          ⊗-intro id ⟜-app ∘g
          ⊗-assoc⁻)

    Trace→SnocTrace : Trace q-end q-start ⊢ SnocTrace q-start q-end
    Trace→SnocTrace = ∃AlgebraHom q-end alg .f q-start

    SnocTrace→Trace : SnocTrace q-start q-end ⊢ Trace q-end q-start
    SnocTrace→Trace = ∃SnocAlgebraHom q-start snocAlg .f q-end

    open LogicalEquivalence
    -- TODO up this to a strong equivalence
    -- However this is sufficient for building a DFA decider at the moment
    Trace⊣⊢SnocTrace :
      LogicalEquivalence
        (Trace q-end q-start)
        (SnocTrace q-start q-end)
    Trace⊣⊢SnocTrace .fun = Trace→SnocTrace
    Trace⊣⊢SnocTrace .inv = SnocTrace→Trace

  module _ (q-start q-end : ⟨ Q ⟩) where
    TraceAppendLiteral : ∀ c →
      Trace q-end q-start ⊗ literal c ⊢ Trace (δ q-end c) q-start
    TraceAppendLiteral c =
      SnocTrace→Trace q-start (δ q-end c) ∘g
      snoc q-end c ∘g
      ⊗-intro (Trace→SnocTrace q-start q-end) id

    -- Trace≅SnocTrace :
    --   StrongEquivalence
    --     (Trace q-end q-start)
    --     (SnocTrace q-start q-end)
    -- Trace≅SnocTrace .fun = ∃AlgebraHom q-end alg .f q-start
    -- Trace≅SnocTrace .inv = ∃SnocAlgebraHom q-start snocAlg .f q-end
    -- Trace≅SnocTrace .sec =
    --   !SnocAlgebraHom' q-start
    --     (initialSnoc q-start)
    --     (SnocAlgebraHom-seq q-start
    --       (∃SnocAlgebraHom q-start snocAlg)
    --       (record {
    --         f = λ q → ∃AlgebraHom q {!!} .f q-start
    --       ; on-nil = {!!}
    --       ; on-snoc = {!!} }))
    --     -- (record {
    --     --   f = λ q → {!!}
    --     -- ; on-nil = {!!}
    --     -- ; on-snoc = {!!} })
    --     (idSnocAlgebraHom q-start (initialSnoc q-start)) q-end
    -- Trace≅SnocTrace .ret =
    --   {!!}
