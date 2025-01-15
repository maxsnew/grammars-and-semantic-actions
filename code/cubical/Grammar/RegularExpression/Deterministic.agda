{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Deterministic (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Cubical.Data.FinSet
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.Literal.Parseable Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.RegularExpression.Base Alphabet
open import Term Alphabet
open import Helper

private
  variable ℓg ℓh : Level

open StrongEquivalence

FollowLastG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG g c = (g ⊗ ＂ c ＂ ⊗ ⊤) & g

_∉FollowLast_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉FollowLast g) .fst = uninhabited (FollowLastG g c)
(c ∉FollowLast g) .snd = isProp-uninhabited

¬FollowLast : Grammar ℓg → Type ℓg
¬FollowLast g = Σ[ c ∈ ⟨ Alphabet ⟩ ] ⟨ c ∉FollowLast g ⟩

FirstG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FirstG g c = (＂ c ＂ ⊗ ⊤) & g

_∉First_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉First g) .fst = uninhabited (FirstG g c)
(c ∉First g) .snd = isProp-uninhabited

¬First : Grammar ℓg → Type ℓg
¬First g = Σ[ c ∈ ⟨ Alphabet ⟩ ] ⟨ c ∉First g ⟩

NullableG : Grammar ℓg → Grammar ℓg
NullableG g = ε & g

¬Nullable_ : Grammar ℓg → hProp ℓg
(¬Nullable g) .fst = uninhabited (NullableG g)
(¬Nullable g) .snd = isProp-uninhabited

Dec¬Nullableε : Dec ⟨ ¬Nullable ε ⟩
¬Nullableε-DecProp : DecProp ℓ-zero
Nullableε-DecProp : DecProp ℓ-zero
Nullableε-witness : ⟨ Nullableε-DecProp ⟩DecProp

¬Nullableε-DecProp .fst = ¬Nullable ε
¬Nullableε-DecProp .snd = Dec¬Nullableε
Nullableε-DecProp = ¬DecProp ¬Nullableε-DecProp
Nullableε-witness = (λ e → get⊥ ((e ∘g &-Δ) _ ε-intro))
Dec¬Nullableε = no Nullableε-witness

Dec¬Nullable⊥ : Dec ⟨ ¬Nullable ⊥ ⟩
¬Nullable⊥-DecProp : DecProp ℓ-zero
¬Nullable⊥-witness : ⟨ ¬Nullable⊥-DecProp ⟩DecProp
Nullable⊥-DecProp : DecProp ℓ-zero

¬Nullable⊥-DecProp .fst = ¬Nullable ⊥
¬Nullable⊥-DecProp .snd = Dec¬Nullable⊥
¬Nullable⊥-witness = &-π₂
Dec¬Nullable⊥ = yes ¬Nullable⊥-witness
Nullable⊥-DecProp = ¬DecProp ¬Nullable⊥-DecProp

Dec¬NullableLit : ∀ c → Dec ⟨ ¬Nullable ＂ c ＂ ⟩
¬NullableLit-DecProp : ⟨ Alphabet ⟩ → DecProp ℓ-zero
NullableLit-DecProp : ⟨ Alphabet ⟩ → DecProp ℓ-zero
¬NullableLit-witness :
  ( c : ⟨ Alphabet ⟩) →
  ⟨ ¬NullableLit-DecProp c ⟩DecProp

¬NullableLit-DecProp c .fst = ¬Nullable ＂ c ＂
¬NullableLit-DecProp c .snd = Dec¬NullableLit c
¬NullableLit-witness c = disjoint-ε-char+' ∘g id ,&p (+-singleton char ∘g literal→char c)
Dec¬NullableLit c = yes (¬NullableLit-witness c)
NullableLit-DecProp c = ¬DecProp (¬NullableLit-DecProp c)

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  open DecidablePowerset ⟨ Alphabet ⟩
  open DecidableFinitePowerset (⟨ Alphabet ⟩ , isFinSetAlphabet)

  data DetReg : Decℙ → Decℙ → DecProp ℓ-zero → Type (ℓ-suc ℓ-zero)

  Dec¬FirstLit : ∀ c c' → Dec ⟨ c' ∉First ＂ c ＂ ⟩
  Dec¬FirstLit c c' =
    decRec
      (λ c≡c' →
        no (λ e →
          get⊥
            ((e ∘g ((id ,⊗ ⊤-intro ∘g ⊗-unit-r⁻) ∘g transportG (cong literal c≡c')) ,&p id ∘g &-Δ)
              _ (lit-intro {c}) )))
      (λ c≢c' → yes
        (⊕-elim
          (⊕ᴰ-elim (λ c≡c' → Empty.rec (c≢c' c≡c')) ∘g same-literal c c' ∘g &-swap)
          (disjoint-char-char⊗char+ ∘g literal→char c ,&p literal→char c' ,⊗ id ∘g &-swap)
        ∘g &⊕-distR
        ∘g ((⊗-unit-r ,⊕p id) ∘g ⊗⊕-distL ∘g id ,⊗ (unroll-string≅ .fun ∘g ⊤→string)) ,&p id
        )
      )
      (DiscreteAlphabet isFinSetAlphabet c c')

  ¬FirstLit-Decℙ : ⟨ Alphabet ⟩ → Decℙ
  ¬FirstLit-Decℙ c c' .fst = c' ∉First ＂ c ＂
  ¬FirstLit-Decℙ c c' .snd = Dec¬FirstLit c c'

  FirstLit-Decℙ : ⟨ Alphabet ⟩ → Decℙ
  FirstLit-Decℙ c = ¬ℙ (¬FirstLit-Decℙ c)

  DetReg→Regex : ∀ {FL F} {b} → DetReg FL F b → Regex

  DetReg→Grammar : ∀ {FL F} {b} → DetReg FL F b → Grammar ℓ-zero

  ⟦_⟧DR : ∀ {FL F} {b} → DetReg FL F b → Grammar ℓ-zero

  Dec¬Nullable-⊗DRnull :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    FL ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ N' ⟩DecProp →
    Dec ⟨ ¬Nullable (⟦ r ⟧DR ⊗ ⟦ r' ⟧DR) ⟩

  ¬Nullable-⊗DRnull-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    FL ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ N' ⟩DecProp →
    DecProp ℓ-zero

  Nullable-⊗DRnull-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    FL ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ N' ⟩DecProp →
    DecProp ℓ-zero

  Dec¬Nullable-⊗DRnotnull :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    FL ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    Dec ⟨ ¬Nullable (⟦ r ⟧DR ⊗ ⟦ r' ⟧DR) ⟩

  ¬Nullable-⊗DRnotnull-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    FL ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    DecProp ℓ-zero

  Nullable-⊗DRnotnull-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    FL ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    DecProp ℓ-zero

  Dec¬Nullable-⊕DRft :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ N' ⟩DecProp →
    Dec ⟨ ¬Nullable (⟦ r ⟧DR ⊕ ⟦ r' ⟧DR) ⟩

  ¬Nullable-⊕DRft-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ N' ⟩DecProp →
    DecProp ℓ-zero

  Nullable-⊕DRft-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ N' ⟩DecProp →
    DecProp ℓ-zero

  Dec¬Nullable-⊕DRtf :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    Dec ⟨ ¬Nullable (⟦ r ⟧DR ⊕ ⟦ r' ⟧DR) ⟩

  ¬Nullable-⊕DRtf-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    DecProp ℓ-zero

  Nullable-⊕DRtf-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    DecProp ℓ-zero

  Dec¬Nullable-⊕DRff :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    Dec ⟨ ¬Nullable (⟦ r ⟧DR ⊕ ⟦ r' ⟧DR) ⟩

  ¬Nullable-⊕DRff-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    DecProp ℓ-zero

  Nullable-⊕DRff-DecProp :
    ∀ {FL F FL' F' : Decℙ} →
    {N N' : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    (r' : DetReg FL' F' N') →
    F ∩ℙ F' ≡ ∅ℙ →
    ⟨ ¬DecProp N ⟩DecProp →
    ⟨ ¬DecProp N' ⟩DecProp →
    DecProp ℓ-zero

  Dec¬Nullable-*DR :
    ∀ {FL F : Decℙ} →
    {N : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    ⟨ ¬DecProp N ⟩DecProp →
    Dec ⟨ ¬Nullable (⟦ r ⟧DR *) ⟩

  ¬Nullable-*DR-DecProp :
    ∀ {FL F : Decℙ} →
    {N : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    ⟨ ¬DecProp N ⟩DecProp →
    DecProp ℓ-zero

  Nullable-*DR-DecProp :
    ∀ {FL F : Decℙ} →
    {N : DecProp ℓ-zero} →
    (r : DetReg FL F N) →
    ⟨ ¬DecProp N ⟩DecProp →
    DecProp ℓ-zero


  -- A deterministic regular expression is parametrized
  -- by its follow last set, first last set, and nullability
  data DetReg where
    εDR : DetReg ∅ℙ ∅ℙ Nullableε-DecProp
    ⊥DR : DetReg ∅ℙ ∅ℙ Nullable⊥-DecProp
    literalDR : (c : ⟨ Alphabet ⟩) → DetReg ∅ℙ (FirstLit-Decℙ c) (NullableLit-DecProp c)
    _⊗DR-null[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      {N N' : DecProp ℓ-zero} →
      (r : DetReg FL F N) →
      (x :
        (FL ∩ℙ F' ≡ ∅ℙ)
        × ⟨ ¬DecProp N ⟩DecProp
        × ⟨ N' ⟩DecProp
      ) →
      (r' : DetReg FL' F' N') →
      DetReg
        (FL ∪ℙ F' ∪ℙ FL')
        F
        (Nullable-⊗DRnull-DecProp r r' (x .fst) (x .snd .fst) (x .snd .snd))
    _⊗DR-notnull[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      {N N' : DecProp ℓ-zero} →
      (r : DetReg FL F N) →
      (x :
        (FL ∩ℙ F' ≡ ∅ℙ)
        × ⟨ ¬DecProp N ⟩DecProp
        × ⟨ ¬DecProp N' ⟩DecProp
      ) →
      (r' : DetReg FL' F' N') →
      DetReg
        (FL ∪ℙ F' ∪ℙ FL')
        F
        (Nullable-⊗DRnotnull-DecProp r r' (x .fst) (x .snd .fst) (x .snd .snd))
    _⊕DR-ft[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      {N N' : DecProp ℓ-zero} →
      (r : DetReg FL F N) →
      (x :
        (F ∩ℙ F' ≡ ∅ℙ)
        × ⟨ ¬DecProp N ⟩DecProp
        × ⟨ N' ⟩DecProp
      ) →
      (r' : DetReg FL' F' N') →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        (Nullable-⊕DRft-DecProp r r' (x .fst) (x .snd .fst) (x .snd .snd))
    _⊕DR-tf[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      {N N' : DecProp ℓ-zero} →
      (r : DetReg FL F N) →
      (x :
        (F ∩ℙ F' ≡ ∅ℙ)
        × ⟨ N ⟩DecProp
        × ⟨ ¬DecProp N' ⟩DecProp
      ) →
      (r' : DetReg FL' F' N') →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        (Nullable-⊕DRtf-DecProp r r' (x .fst) (x .snd .fst) (x .snd .snd))
    _⊕DR-ff[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      {N N' : DecProp ℓ-zero} →
      (r : DetReg FL F N) →
      (x :
        (F ∩ℙ F' ≡ ∅ℙ)
        × ⟨ ¬DecProp N ⟩DecProp
        × ⟨ ¬DecProp N' ⟩DecProp
      ) →
      (r' : DetReg FL' F' N') →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        (Nullable-⊕DRff-DecProp r r' (x .fst) (x .snd .fst) (x .snd .snd))
    _*DR[_] :
      ∀ {FL F : Decℙ} →
      ∀ {N : DecProp ℓ-zero} →
      (r : DetReg FL F N) →
      (x : ⟨ ¬DecProp N ⟩DecProp) →
      DetReg
        (F ∪ℙ FL)
        F
        (Nullable-*DR-DecProp r x)

  DetReg→Regex εDR = ε-Reg
  DetReg→Regex ⊥DR = ⊥-Reg
  DetReg→Regex (literalDR c) = literalReg c
  DetReg→Regex (r ⊗DR-null[ x ] r') =
    (DetReg→Regex r) ⊗Reg (DetReg→Regex r')
  DetReg→Regex (r ⊗DR-notnull[ x ] r') =
    (DetReg→Regex r) ⊗Reg (DetReg→Regex r')
  DetReg→Regex (r ⊕DR-ft[ x ] r') =
    (DetReg→Regex r) ⊕Reg (DetReg→Regex r')
  DetReg→Regex (r ⊕DR-tf[ x ] r') =
    (DetReg→Regex r) ⊕Reg (DetReg→Regex r')
  DetReg→Regex (r ⊕DR-ff[ x ] r') =
    (DetReg→Regex r) ⊕Reg (DetReg→Regex r')
  DetReg→Regex (r *DR[ x ]) = KL*Reg (DetReg→Regex r)

  DetReg→Grammar r = ⟦ DetReg→Regex r ⟧r

  ⟦_⟧DR = DetReg→Grammar

  Dec¬Nullable-⊗DRnull = {!!}

  Dec¬Nullable-⊗DRnotnull = {!!}

  Dec¬Nullable-⊕DRtf = {!!}

  Dec¬Nullable-⊕DRft = {!!}

  Dec¬Nullable-⊕DRff = {!!}

  Dec¬Nullable-*DR = {!!}

  -- Dec¬Nullable-⊗DRnull εDR r' FL∩F'mt rnotnull r'null =
  --   Empty.rec (rnotnull Nullableε-witness)
  -- Dec¬Nullable-⊗DRnull ⊥DR r' FL∩F'mt rnotnull r'null =
  --   yes ¬Nullable⊥-witness
  -- Dec¬Nullable-⊗DRnull (literalDR c) r' FL∩F'mt rnotnull r'null =
  --   yes (¬NullableLit-witness c)
  -- Dec¬Nullable-⊗DRnull (r ⊗DR-null[ x ] r₁) r' FL∩F'mt rnotnull r'null =
  --   {!!}

  ¬Nullable-⊗DRnull-DecProp r r' FL∩F'mt rnotnull r'null .fst =
    ¬Nullable (⟦ r ⟧DR ⊗ ⟦ r' ⟧DR)
  ¬Nullable-⊗DRnull-DecProp r r' FL∩F'mt rnotnull r'null .snd =
    Dec¬Nullable-⊗DRnull r r' FL∩F'mt rnotnull r'null

  Nullable-⊗DRnull-DecProp r r' FL∩F'mt rnotnull r'null =
    ¬DecProp ¬Nullable-⊗DRnull-DecProp r r' FL∩F'mt rnotnull r'null

  ¬Nullable-⊗DRnotnull-DecProp r r' FL∩F'mt rnotnull r'notnull .fst =
    ¬Nullable (⟦ r ⟧DR ⊗ ⟦ r' ⟧DR)
  ¬Nullable-⊗DRnotnull-DecProp r r' FL∩F'mt rnotnull r'notnull .snd =
    Dec¬Nullable-⊗DRnotnull r r' FL∩F'mt rnotnull r'notnull

  Nullable-⊗DRnotnull-DecProp r r' FL∩F'mt rnotnull r'notnull =
    ¬DecProp ¬Nullable-⊗DRnotnull-DecProp r r' FL∩F'mt rnotnull r'notnull

  ¬Nullable-⊕DRtf-DecProp r r' F∩F'mt rnull r'notnull .fst =
    ¬Nullable (⟦ r ⟧DR ⊕ ⟦ r' ⟧DR)
  ¬Nullable-⊕DRtf-DecProp r r' F∩F'mt rnull r'notnull .snd =
    Dec¬Nullable-⊕DRtf r r' F∩F'mt rnull r'notnull

  Nullable-⊕DRtf-DecProp r r' F∩F'mt rnull r'notnull =
    ¬DecProp ¬Nullable-⊕DRtf-DecProp r r' F∩F'mt rnull r'notnull

  ¬Nullable-⊕DRft-DecProp r r' F∩F'mt rnotnull r'null .fst =
    ¬Nullable (⟦ r ⟧DR ⊕ ⟦ r' ⟧DR)
  ¬Nullable-⊕DRft-DecProp r r' F∩F'mt rnotnull r'null .snd =
    Dec¬Nullable-⊕DRft r r' F∩F'mt rnotnull r'null

  Nullable-⊕DRft-DecProp r r' F∩F'mt rnotnull r'null =
    ¬DecProp ¬Nullable-⊕DRft-DecProp r r' F∩F'mt rnotnull r'null

  ¬Nullable-⊕DRff-DecProp r r' F∩F'mt rnotnull r'notnull .fst =
    ¬Nullable (⟦ r ⟧DR ⊕ ⟦ r' ⟧DR)
  ¬Nullable-⊕DRff-DecProp r r' F∩F'mt rnotnull r'notnull .snd =
    Dec¬Nullable-⊕DRff r r' F∩F'mt rnotnull r'notnull

  Nullable-⊕DRff-DecProp r r' F∩F'mt rnotnull r'notnull =
    ¬DecProp ¬Nullable-⊕DRff-DecProp r r' F∩F'mt rnotnull r'notnull

  ¬Nullable-*DR-DecProp r rnotnull .fst =
    ¬Nullable (⟦ r ⟧DR *)
  ¬Nullable-*DR-DecProp r rnotnull .snd =
    Dec¬Nullable-*DR r rnotnull

  Nullable-*DR-DecProp r rnotnull  =
    ¬DecProp ¬Nullable-*DR-DecProp r rnotnull


  -- Dec¬Nullable : ∀ {FL F b} →
  --   (r : DetReg FL F b) →
  --   Dec (⟨ ¬Nullable ⟦ r ⟧DR ⟩)
  -- Dec¬Nullable r = {!!}

  -- -- nulls-agree-true : ∀ {FL F} →
  -- --   (r : DetReg FL F true) →
  -- --   ⟨ ¬Nullable ⟦ r ⟧DR ⟩ →
  -- --   Empty.⊥
  -- -- nulls-agree-false : ∀ {FL F} →
  -- --   (r : DetReg FL F false) →
  -- --   ⟨ ¬Nullable ⟦ r ⟧DR ⟩
  -- -- firsts-agree : ∀ {FL F b} →
  -- --   (r : DetReg FL F b) →
  -- --   (c : ⟨ Alphabet ⟩) →
  -- --   c ∈ℙ (¬ℙ F) →
  -- --   ⟨ c ∉First ⟦ r ⟧DR ⟩
  -- -- follow-lasts-agree : ∀ {FL F b} →
  -- --   (r : DetReg FL F b) →
  -- --   (c : ⟨ Alphabet ⟩) →
  -- --   c ∈ℙ (¬ℙ FL) →
  -- --   ⟨ c ∉FollowLast ⟦ r ⟧DR ⟩

  -- -- nulls-agree-true εDR e = get⊥ ((e ∘g &-Δ) _ ε-intro)
  -- -- nulls-agree-true (r ⊕DR-ft[ x ] r') e = null-r' (e ∘g id ,&p ⊕-inr)
  -- --   where
  -- --   null-r' = nulls-agree-true r'
  -- -- nulls-agree-true (r ⊕DR-tf[ x ] r') e = null-r (e ∘g id ,&p ⊕-inl)
  -- --   where
  -- --   null-r = nulls-agree-true r
  -- -- nulls-agree-true (r *DR) e = get⊥ ((e ∘g id ,& NIL) _ ε-intro)

  -- -- nulls-agree-false ⊥DR = &-π₂
  -- -- nulls-agree-false (literalDR c) = disjoint-ε-char+' ∘g id ,&p (+-singleton char ∘g literal→char c )
  -- -- nulls-agree-false (r ⊗DR-null[ x ] r') = {!!}
  -- --   -- TODO gotta look at FL r and F r'
  -- --   where
  -- --   ¬null-r = nulls-agree-false r
  -- --   null-r' = nulls-agree-true r'
  -- -- nulls-agree-false (r ⊗DR-notnull[ x ] r') = {!!}
  -- --   -- TODO gotta look at FL r and F r'
  -- -- nulls-agree-false (r ⊕DR-ff[ x ] r') = ⊕-elim ¬null-r ¬null-r' ∘g &⊕-distL
  -- --   where
  -- --   ¬null-r = nulls-agree-false r
  -- --   ¬null-r' = nulls-agree-false r'

  -- -- firsts-agree εDR c c∉F =
  -- --   disjoint-ε-char+' ∘g &-swap ∘g (literal→char c ,⊗ ⊤→string) ,&p id
  -- -- firsts-agree ⊥DR c c∉F = &-π₂
  -- -- firsts-agree (literalDR c') c c∉F =
  -- --   ⊕-elim
  -- --     (⊕ᴰ-elim (λ c≡c' → Empty.rec (c∉F c≡c')) ∘g same-literal c c')
  -- --     (disjoint-char-char⊗char+ ∘g literal→char c' ,&p literal→char c ,⊗ id ∘g &-swap)
  -- --   ∘g &⊕-distR
  -- --   ∘g ((⊗-unit-r ,⊕p id) ∘g ⊗⊕-distL ∘g id ,⊗ (unroll-string≅ .fun ∘g ⊤→string)) ,&p id
  -- -- firsts-agree (r ⊗DR-null[ x ] r') c c∉F = c∉Fr ∘g id ,&p {!!}
  -- --   where
  -- --   c∉Fr : ⟨ c ∉First ⟦ r ⟧DR ⟩
  -- --   c∉Fr = firsts-agree r c c∉F
  -- --   ¬null-r = nulls-agree-false r
  -- --   null-r' = nulls-agree-true r'
  -- -- firsts-agree (r ⊗DR-notnull[ x ] r') c c∉F = {!!}
  -- -- firsts-agree (r ⊕DR-ft[ x ] r') c c∉F = {!!}
  -- -- firsts-agree (r ⊕DR-tf[ x ] r') c c∉F = {!!}
  -- -- firsts-agree (r ⊕DR-ff[ x ] r') c c∉F = {!!}
  -- -- firsts-agree (r *DR) c c∉F = {!!}

  -- -- follow-lasts-agree r c c∉F = {!!}

  -- -- -- First' : ∀ {FL F b} →
  -- -- --   (r : DetReg FL F b) →
  -- -- --   (c : ⟨ Alphabet ⟩) →
  -- -- --   c ∈ℙ (¬ℙ F) →
  -- -- --   ⟨ c ∉First ⟦ r ⟧DetReg ⟩
  -- -- -- First' ε-DetReg c c∉F =
  -- -- --   disjoint-ε-char+' ∘g &-swap ∘g (literal→char c ,⊗ ⊤→string) ,&p id
  -- -- -- First' ⊥-DetReg c c∉F = &-π₂
  -- -- -- First' (_⊗DetReg[_]_ {b' = false} r x r') c c∉F = {!!}
  -- -- -- First' (_⊗DetReg[_]_ {b' = true} r x r') c c∉F = {!!}
  -- -- -- First' (literalDetReg c') c c∉F =
  -- -- --   ⊕-elim
  -- -- --     (⊕ᴰ-elim (λ c≡c' → Empty.rec (c∉F c≡c')) ∘g same-literal c c')
  -- -- --     (disjoint-char-char⊗char+ ∘g literal→char c' ,&p literal→char c ,⊗ id ∘g &-swap)
  -- -- --   ∘g &⊕-distR
  -- -- --   ∘g ((⊗-unit-r ,⊕p id) ∘g ⊗⊕-distL ∘g id ,⊗ (unroll-string≅ .fun ∘g ⊤→string)) ,&p id
  -- -- -- First' (r ⊕DetReg[ x ] r₁) c c∉F = {!!}
  -- -- -- First' (r *DetReg) c c∉F = {!!}


  -- -- -- -- dec¬First : ∀ {FL F b}
  -- -- -- --   (r : DetReg FL F b) →
  -- -- -- --   (c : ⟨ Alphabet ⟩) →
  -- -- -- --   Dec ⟨ c ∉First ⟦ r ⟧DetReg ⟩
  -- -- -- -- dec¬First ε-DetReg c = yes {!!}
  -- -- -- -- dec¬First ⊥-DetReg c = yes &-π₂
  -- -- -- -- dec¬First (r ⊗DetReg[ x ] r₁) c = {!c!}
  -- -- -- -- dec¬First (literalDetReg c₁) c = {!!}
  -- -- -- -- dec¬First (r ⊕DetReg[ x ] r₁) c = {!!}
  -- -- -- -- dec¬First (r *DetReg) c = {!!}

  -- -- -- -- totallyParseable'DetReg : ∀ {FL F b}
  -- -- -- --   (r : DetReg FL F b) →
  -- -- -- --   totallyParseable' ⟦ r ⟧DetReg
  -- -- -- -- totallyParseable'DetReg ε-DetReg .fst = char +
  -- -- -- -- totallyParseable'DetReg ε-DetReg .snd = sym≅ unroll-string≅
  -- -- -- -- totallyParseable'DetReg ⊥-DetReg .fst = ⊤
  -- -- -- -- totallyParseable'DetReg ⊥-DetReg .snd = ⊥⊕≅ ⊤ ≅∙ sym≅ string≅⊤
  -- -- -- -- totallyParseable'DetReg (r ⊗DetReg[ x ] r') .fst =
  -- -- -- --   (⟦ r ⟧DetReg ⊗  r'¬ ) ⊕
  -- -- -- --   (r¬ ⊗ ⟦ r' ⟧DetReg) ⊕
  -- -- -- --   (r¬ ⊗ r'¬)
  -- -- -- --   where
  -- -- -- --   tpr : totallyParseable' ⟦ r ⟧DetReg
  -- -- -- --   tpr = totallyParseable'DetReg r
  -- -- -- --   r¬ = tpr .fst

  -- -- -- --   tpr' : totallyParseable' ⟦ r' ⟧DetReg
  -- -- -- --   tpr' = totallyParseable'DetReg r'
  -- -- -- --   r'¬ = tpr' .fst
  -- -- -- -- totallyParseable'DetReg (r ⊗DetReg[ x ] r') .snd = {!!}
  -- -- -- -- totallyParseable'DetReg (literalDetReg c) =
  -- -- -- --   totallyParseable'Literal c (DiscreteAlphabet isFinSetAlphabet)
  -- -- -- -- totallyParseable'DetReg (r ⊕DetReg[ x ] r₁) = {!!}
  -- -- -- -- totallyParseable'DetReg (r *DetReg) = {!!}


  -- -- -- -- -- decPropFirst : ?

  -- -- -- -- -- disjoint-firsts→disjoint :
  -- -- -- -- --   ∀ {FL FL' F F'} {b b'} →
  -- -- -- -- --     (r : DetReg FL F b) →
  -- -- -- -- --     (r' : DetReg FL' F' b') →
  -- -- -- -- --     F ∩ℙ F' ≡ ∅ℙ →
  -- -- -- -- --     (not (b and b')) ≡ true →
  -- -- -- -- --     disjoint ⟦ r ⟧DetReg ⟦ r' ⟧DetReg
  -- -- -- -- -- disjoint-firsts→disjoint ε-DetReg ε-DetReg
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   Empty.rec (false≢true not-both-null)
  -- -- -- -- -- disjoint-firsts→disjoint r ⊥-DetReg
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   &-π₂
  -- -- -- -- -- disjoint-firsts→disjoint ε-DetReg (r' ⊗DetReg[ x ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint ε-DetReg (literalDetReg c)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint ε-DetReg (r' ⊕DetReg[ x ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint ε-DetReg (r' *DetReg)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   Empty.rec (false≢true not-both-null)
  -- -- -- -- -- disjoint-firsts→disjoint ⊥-DetReg r'
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   &-π₁
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) ε-DetReg
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' ⊗DetReg[ x₁ ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (literalDetReg c)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' ⊕DetReg[ x₁ ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' *DetReg)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (literalDetReg c) ε-DetReg
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (literalDetReg c) (r' ⊗DetReg[ x ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (literalDetReg c) (literalDetReg c₁)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (literalDetReg c) (r' ⊕DetReg[ x ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (literalDetReg c) (r' *DetReg)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) ε-DetReg
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' ⊗DetReg[ x₁ ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (literalDetReg c)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' ⊕DetReg[ x₁ ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' *DetReg)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r *DetReg) ε-DetReg
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   Empty.rec (false≢true not-both-null)
  -- -- -- -- -- disjoint-firsts→disjoint (r *DetReg) (r' ⊗DetReg[ x ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r *DetReg) (literalDetReg c)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r *DetReg) (r' ⊕DetReg[ x ] r'')
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   {!!}
  -- -- -- -- -- disjoint-firsts→disjoint (r *DetReg) (r' *DetReg)
  -- -- -- -- --   disjoint-firsts not-both-null =
  -- -- -- -- --   Empty.rec (false≢true not-both-null)

  -- -- -- -- -- unambiguous-DetReg :
  -- -- -- -- --   ∀ {FL F} {b} (r : DetReg FL F b) → unambiguous (⟦ r ⟧DetReg)
  -- -- -- -- -- unambiguous-DetReg ε-DetReg = unambiguousε isFinSetAlphabet
  -- -- -- -- -- unambiguous-DetReg ⊥-DetReg = unambiguous⊥
  -- -- -- -- -- unambiguous-DetReg (r ⊗DetReg[ x ] r₁) = {!!}
  -- -- -- -- -- unambiguous-DetReg (literalDetReg c) =
  -- -- -- -- --   unambiguous-literal c isFinSetAlphabet
  -- -- -- -- -- unambiguous-DetReg (r ⊕DetReg[ x ] r') =
  -- -- -- -- --   unambiguous⊕
  -- -- -- -- --     (disjoint-firsts→disjoint r r' x {!!})
  -- -- -- -- --     unambig-r
  -- -- -- -- --     unambig-r'
  -- -- -- -- --     isFinSetAlphabet
  -- -- -- -- --   where
  -- -- -- -- --   unambig-r = unambiguous-DetReg r
  -- -- -- -- --   unambig-r' = unambiguous-DetReg r'

  -- -- -- -- -- unambiguous-DetReg (r *DetReg) = {!!}
