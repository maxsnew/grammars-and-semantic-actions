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

  -- The grammar "Parse q" denotes the type of traces in the DFA
  -- from state q to an accepting state
  data Parse : (q : ⟨ Q ⟩) → Grammar ℓD where
    nil : ∀ {q} → isAcc q .fst .fst →
      ε-grammar ⊢ Parse q
    cons : ∀ q c →
      literal c ⊗ Parse (δ q c) ⊢ Parse q

  InitParse : Grammar ℓD
  InitParse = Parse init

  record Algebra : Typeω where
    field
      the-ℓs : ⟨ Q ⟩ → Level
      G : (q : ⟨ Q ⟩) → Grammar (the-ℓs q)
      nil-case : ∀ {q} → isAcc q .fst .fst →
        ε-grammar ⊢ G q
      cons-case : ∀ q c →
        literal c ⊗ G (δ q c) ⊢ G q

  open Algebra

  initial : Algebra
  the-ℓs initial _ = ℓD
  G initial = Parse
  nil-case initial = nil
  cons-case initial = cons

  record AlgebraHom (alg alg' : Algebra) : Typeω where
    field
      f : (q : ⟨ Q ⟩) → alg .G q ⊢ alg' .G q
      on-nil : ∀ {q} → (qAcc : isAcc q .fst .fst) →
        f q ∘g alg .nil-case qAcc ≡ alg' .nil-case qAcc
      on-cons : ∀ q c →
        f q ∘g alg .cons-case q c ≡
          alg' .cons-case q c ∘g (⊗-intro id (f (δ q c)))
    fInit = f init

  open AlgebraHom

  idAlgebraHom : (alg : Algebra) →
    AlgebraHom alg alg
  f (idAlgebraHom alg) q = id
  on-nil (idAlgebraHom alg) _ = refl
  on-cons (idAlgebraHom alg) _ _ = refl

  AlgebraHom-seq : {alg alg' alg'' : Algebra} →
    AlgebraHom alg alg' → AlgebraHom alg' alg'' →
    AlgebraHom alg alg''
  AlgebraHom-seq ϕ ψ .f q = ψ .f q ∘g ϕ .f q
  AlgebraHom-seq ϕ ψ .on-nil qAcc =
    cong (ψ .f _ ∘g_) (ϕ .on-nil qAcc) ∙
    ψ .on-nil qAcc
  AlgebraHom-seq ϕ ψ .on-cons q c =
    cong (ψ .f q ∘g_) (ϕ .on-cons q c) ∙
    cong (_∘g ⊗-intro id (ϕ .f (δ q c))) (ψ .on-cons q c)

  module _ (the-alg : Algebra) where
    recTrace : ∀ {q} → Parse q ⊢ the-alg .G q
    recTrace {q} w (nil qAcc .w pε) = the-alg .nil-case qAcc w pε
    recTrace {q} w (cons .q c .w p⊗) =
      the-alg .cons-case q c _
        (p⊗ .fst , (p⊗ .snd .fst) , (recTrace _ (p⊗ .snd .snd)))

    recInit : Parse init ⊢ the-alg .G init
    recInit = recTrace

    ∃AlgebraHom : AlgebraHom initial the-alg
    f ∃AlgebraHom q = recTrace {q}
    on-nil ∃AlgebraHom _ = refl
    on-cons ∃AlgebraHom _ _ = refl

    !AlgebraHom-help :
      (e : AlgebraHom initial the-alg) →
      (q : ⟨ Q ⟩) →
      (∀ w p → e .f q w p ≡ recTrace w p)
    !AlgebraHom-help e q w (nil qAcc .w pε) =
      cong (λ a → a w pε) (e .on-nil qAcc)
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

  -- data SnocParse : (q : ⟨ Q ⟩) → Grammar ℓD where
  --   nil : ∀ {q} → isAcc q .fst .fst →
  --     ε-grammar ⊢ SnocParse q
  --   snoc : ∀ q c →
  --     SnocParse q ⊗ literal c ⊢ SnocParse (δ q c)

  -- InitSnocParse : Grammar ℓD
  -- InitSnocParse = SnocParse init

  -- record SnocAlgebra : Typeω where
  --   field
  --     the-ℓs : ⟨ Q ⟩ → Level
  --     G : (q : ⟨ Q ⟩) → Grammar (the-ℓs q)
  --     nil-case : ∀ {q} → isAcc q .fst .fst →
  --       ε-grammar ⊢ G q
  --     snoc-case : ∀ q c →
  --       G q ⊗ literal c ⊢ G (δ q c)

  -- open SnocAlgebra

  -- initialSnoc : SnocAlgebra
  -- initialSnoc .the-ℓs _ = ℓD
  -- initialSnoc .G = SnocParse
  -- initialSnoc .nil-case = nil
  -- initialSnoc .snoc-case = snoc

  -- record SnocAlgebraHom (alg alg' : SnocAlgebra) : Typeω where
  --   field
  --     f : (q : ⟨ Q ⟩) → alg .G q ⊢ alg' .G q
  --     on-nil : ∀ {q} → (qAcc : isAcc q .fst .fst) →
  --       f q ∘g alg .nil-case qAcc ≡ alg' .nil-case qAcc
  --     on-snoc : ∀ q c →
  --       f (δ q c) ∘g alg .snoc-case q c ≡
  --         alg' .snoc-case q c ∘g ⊗-intro (f q) id

  -- open SnocAlgebraHom

  -- idSnocAlgebraHom : (alg : SnocAlgebra) →
  --   SnocAlgebraHom alg alg
  -- f (idSnocAlgebraHom alg) q = id
  -- on-nil (idSnocAlgebraHom alg) _ = refl
  -- on-snoc (idSnocAlgebraHom alg) _ _ = refl

  -- SnocAlgebraHom-seq : {alg alg' alg'' : SnocAlgebra} →
  --   SnocAlgebraHom alg alg' → SnocAlgebraHom alg' alg'' →
  --   SnocAlgebraHom alg alg''
  -- SnocAlgebraHom-seq ϕ ψ .f q = ψ .f q ∘g ϕ .f q
  -- SnocAlgebraHom-seq ϕ ψ .on-nil qAcc =
  --   cong (ψ .f _ ∘g_) (ϕ .on-nil qAcc) ∙
  --   ψ .on-nil qAcc
  -- SnocAlgebraHom-seq ϕ ψ .on-snoc q c =
  --   cong (ψ .f (δ q c) ∘g_) (ϕ .on-snoc q c) ∙
  --   cong (_∘g ⊗-intro (ϕ .f q) id) (ψ .on-snoc q c)

  -- module _ (the-alg : SnocAlgebra) where
  --   recSnocTrace : ∀ {q} → SnocParse q ⊢ the-alg .G q
  --   recSnocTrace {q} w (nil qAcc .w pε) = the-alg .nil-case qAcc w pε
  --   recSnocTrace {q} w (snoc _ c .w p⊗) =
  --     the-alg .snoc-case _ c _
  --       ((p⊗ .fst) , (recSnocTrace _ (p⊗ .snd .fst) , p⊗ .snd .snd))

  --   recSnocInit : SnocParse init ⊢ the-alg .G init
  --   recSnocInit = recSnocTrace

  --   ∃SnocAlgebraHom : SnocAlgebraHom initialSnoc the-alg
  --   f ∃SnocAlgebraHom q = recSnocTrace {q}
  --   on-nil ∃SnocAlgebraHom _ = refl
  --   on-snoc ∃SnocAlgebraHom _ _ = refl

  --   !SnocAlgebraHom-help :
  --     (e : SnocAlgebraHom initialSnoc the-alg) →
  --     (q : ⟨ Q ⟩) →
  --     (∀ w p → e .f q w p ≡ recSnocTrace w p)
  --   !SnocAlgebraHom-help e q w (nil qAcc .w pε) =
  --     cong (λ a → a w pε) (e .on-nil qAcc)
  --   !SnocAlgebraHom-help e q w (snoc _ c .w p⊗) =
  --     cong (λ a → a w p⊗) (e .on-snoc _ c) ∙
  --     cong (λ a → the-alg .snoc-case _ c _
  --       ((p⊗ .fst) , (a , (p⊗ .snd .snd))))
  --       (!SnocAlgebraHom-help e _ _ (p⊗ .snd .fst))

  --   !SnocAlgebraHom :
  --     (e : SnocAlgebraHom initialSnoc the-alg) →
  --     (q : ⟨ Q ⟩) →
  --     e .f q ≡ recSnocTrace {q}
  --   !SnocAlgebraHom e q =
  --     funExt (λ w → funExt (λ p → !SnocAlgebraHom-help e q w p))

  --   -- TODO rename
  --   !SnocAlgebraHom' :
  --     (e e' : SnocAlgebraHom initialSnoc the-alg) →
  --     (q : ⟨ Q ⟩) →
  --     e .f q ≡ e' .f q
  --   !SnocAlgebraHom' e e' q =
  --     !SnocAlgebraHom e q ∙
  --     sym (!SnocAlgebraHom e' q)

  -- initialSnoc→initialSnoc≡id :
  --   (e : SnocAlgebraHom initialSnoc initialSnoc) →
  --   (q : ⟨ Q ⟩) →
  --   (e .f q)
  --      ≡
  --   id
  -- initialSnoc→initialSnoc≡id e q =
  --   !SnocAlgebraHom initialSnoc e q ∙
  --   sym (!SnocAlgebraHom initialSnoc (idSnocAlgebraHom initialSnoc) q)

  -- snocAlgebra-η :
  --   (e : SnocAlgebraHom initialSnoc initialSnoc) →
  --   e .f init ≡ id
  -- snocAlgebra-η e = initialSnoc→initialSnoc≡id e _
