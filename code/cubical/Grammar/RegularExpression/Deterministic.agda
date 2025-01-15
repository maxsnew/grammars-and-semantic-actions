{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Deterministic (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Cubical.Data.FinSet
open import Cubical.Data.List
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Cubical.Relation.Nullary.Base

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

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  open DecidablePowerset ⟨ Alphabet ⟩
  open DecidableFinitePowerset (⟨ Alphabet ⟩ , isFinSetAlphabet)

  -- A deterministic regular expression is parametrized
  -- by its follow last set, first last set, and nullability
  data DetReg : Decℙ → Decℙ → Bool → Type (ℓ-suc ℓ-zero) where
    εDR : DetReg ∅ℙ ∅ℙ true
    ⊥DR : DetReg ∅ℙ ∅ℙ false
    literalDR : (c : ⟨ Alphabet ⟩) → DetReg ∅ℙ ⟦ c ⟧ℙ false
    _⊗DR-null[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      DetReg FL F false →
      FL ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' true →
      DetReg
        (FL ∪ℙ F' ∪ℙ FL')
        F
        false
    _⊗DR-notnull[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      DetReg FL F false →
      FL ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' false →
      DetReg
        FL'
        F
        false
    _⊕DR-ft[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      DetReg FL F false →
      F ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' true →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        true
    _⊕DR-tf[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      DetReg FL F true →
      F ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' false →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        true
    _⊕DR-ff[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      DetReg FL F false →
      F ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' false →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        false
    _*DR :
      ∀ {FL F : Decℙ} →
      DetReg FL F false →
      DetReg
        (F ∪ℙ FL)
        F
        true

  DetReg→Regex : ∀ {FL F} {b} → DetReg FL F b → Regex
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
  DetReg→Regex (r *DR) = KL*Reg (DetReg→Regex r)

  DetReg→Grammar : ∀ {FL F} {b} → DetReg FL F b → Grammar ℓ-zero
  DetReg→Grammar r = ⟦ DetReg→Regex r ⟧r

  ⟦_⟧DR : ∀ {FL F} {b} → DetReg FL F b → Grammar ℓ-zero
  ⟦_⟧DR = DetReg→Grammar

  nulls-agree-true : ∀ {FL F} →
    (r : DetReg FL F true) →
    ⟨ ¬Nullable ⟦ r ⟧DR ⟩ →
    Empty.⊥
  nulls-agree-false : ∀ {FL F} →
    (r : DetReg FL F false) →
    ⟨ ¬Nullable ⟦ r ⟧DR ⟩
  firsts-agree : ∀ {FL F b} →
    (r : DetReg FL F b) →
    (c : ⟨ Alphabet ⟩) →
    c ∈ℙ (¬ℙ F) →
    ⟨ c ∉First ⟦ r ⟧DR ⟩
  follow-lasts-agree : ∀ {FL F b} →
    (r : DetReg FL F b) →
    (c : ⟨ Alphabet ⟩) →
    c ∈ℙ (¬ℙ FL) →
    ⟨ c ∉FollowLast ⟦ r ⟧DR ⟩

  nulls-agree-true εDR e = get⊥ ((e ∘g &-Δ) _ ε-intro)
  nulls-agree-true (r ⊕DR-ft[ x ] r') e = null-r' (e ∘g id ,&p ⊕-inr)
    where
    null-r' = nulls-agree-true r'
  nulls-agree-true (r ⊕DR-tf[ x ] r') e = null-r (e ∘g id ,&p ⊕-inl)
    where
    null-r = nulls-agree-true r
  nulls-agree-true (r *DR) e = get⊥ ((e ∘g id ,& NIL) _ ε-intro)

  nulls-agree-false ⊥DR = &-π₂
  nulls-agree-false (literalDR c) = disjoint-ε-char+' ∘g id ,&p (+-singleton char ∘g literal→char c )
  nulls-agree-false (r ⊗DR-null[ x ] r') = {!!}
    -- TODO gotta look at FL r and F r'
    where
    ¬null-r = nulls-agree-false r
    null-r' = nulls-agree-true r'
  nulls-agree-false (r ⊗DR-notnull[ x ] r') = {!!}
    -- TODO gotta look at FL r and F r'
  nulls-agree-false (r ⊕DR-ff[ x ] r') = ⊕-elim ¬null-r ¬null-r' ∘g &⊕-distL
    where
    ¬null-r = nulls-agree-false r
    ¬null-r' = nulls-agree-false r'

  firsts-agree εDR c c∉F =
    disjoint-ε-char+' ∘g &-swap ∘g (literal→char c ,⊗ ⊤→string) ,&p id
  firsts-agree ⊥DR c c∉F = &-π₂
  firsts-agree (literalDR c') c c∉F =
    ⊕-elim
      (⊕ᴰ-elim (λ c≡c' → Empty.rec (c∉F c≡c')) ∘g same-literal c c')
      (disjoint-char-char⊗char+ ∘g literal→char c' ,&p literal→char c ,⊗ id ∘g &-swap)
    ∘g &⊕-distR
    ∘g ((⊗-unit-r ,⊕p id) ∘g ⊗⊕-distL ∘g id ,⊗ (unroll-string≅ .fun ∘g ⊤→string)) ,&p id
  firsts-agree (r ⊗DR-null[ x ] r') c c∉F = c∉Fr ∘g id ,&p {!!}
    where
    c∉Fr : ⟨ c ∉First ⟦ r ⟧DR ⟩
    c∉Fr = firsts-agree r c c∉F
    ¬null-r = nulls-agree-false r
    null-r' = nulls-agree-true r'
  firsts-agree (r ⊗DR-notnull[ x ] r') c c∉F = {!!}
  firsts-agree (r ⊕DR-ft[ x ] r') c c∉F = {!!}
  firsts-agree (r ⊕DR-tf[ x ] r') c c∉F = {!!}
  firsts-agree (r ⊕DR-ff[ x ] r') c c∉F = {!!}
  firsts-agree (r *DR) c c∉F = {!!}

  follow-lasts-agree r c c∉F = {!!}

  -- First' : ∀ {FL F b} →
  --   (r : DetReg FL F b) →
  --   (c : ⟨ Alphabet ⟩) →
  --   c ∈ℙ (¬ℙ F) →
  --   ⟨ c ∉First ⟦ r ⟧DetReg ⟩
  -- First' ε-DetReg c c∉F =
  --   disjoint-ε-char+' ∘g &-swap ∘g (literal→char c ,⊗ ⊤→string) ,&p id
  -- First' ⊥-DetReg c c∉F = &-π₂
  -- First' (_⊗DetReg[_]_ {b' = false} r x r') c c∉F = {!!}
  -- First' (_⊗DetReg[_]_ {b' = true} r x r') c c∉F = {!!}
  -- First' (literalDetReg c') c c∉F =
  --   ⊕-elim
  --     (⊕ᴰ-elim (λ c≡c' → Empty.rec (c∉F c≡c')) ∘g same-literal c c')
  --     (disjoint-char-char⊗char+ ∘g literal→char c' ,&p literal→char c ,⊗ id ∘g &-swap)
  --   ∘g &⊕-distR
  --   ∘g ((⊗-unit-r ,⊕p id) ∘g ⊗⊕-distL ∘g id ,⊗ (unroll-string≅ .fun ∘g ⊤→string)) ,&p id
  -- First' (r ⊕DetReg[ x ] r₁) c c∉F = {!!}
  -- First' (r *DetReg) c c∉F = {!!}


  -- -- dec¬First : ∀ {FL F b}
  -- --   (r : DetReg FL F b) →
  -- --   (c : ⟨ Alphabet ⟩) →
  -- --   Dec ⟨ c ∉First ⟦ r ⟧DetReg ⟩
  -- -- dec¬First ε-DetReg c = yes {!!}
  -- -- dec¬First ⊥-DetReg c = yes &-π₂
  -- -- dec¬First (r ⊗DetReg[ x ] r₁) c = {!c!}
  -- -- dec¬First (literalDetReg c₁) c = {!!}
  -- -- dec¬First (r ⊕DetReg[ x ] r₁) c = {!!}
  -- -- dec¬First (r *DetReg) c = {!!}

  -- -- totallyParseable'DetReg : ∀ {FL F b}
  -- --   (r : DetReg FL F b) →
  -- --   totallyParseable' ⟦ r ⟧DetReg
  -- -- totallyParseable'DetReg ε-DetReg .fst = char +
  -- -- totallyParseable'DetReg ε-DetReg .snd = sym≅ unroll-string≅
  -- -- totallyParseable'DetReg ⊥-DetReg .fst = ⊤
  -- -- totallyParseable'DetReg ⊥-DetReg .snd = ⊥⊕≅ ⊤ ≅∙ sym≅ string≅⊤
  -- -- totallyParseable'DetReg (r ⊗DetReg[ x ] r') .fst =
  -- --   (⟦ r ⟧DetReg ⊗  r'¬ ) ⊕
  -- --   (r¬ ⊗ ⟦ r' ⟧DetReg) ⊕
  -- --   (r¬ ⊗ r'¬)
  -- --   where
  -- --   tpr : totallyParseable' ⟦ r ⟧DetReg
  -- --   tpr = totallyParseable'DetReg r
  -- --   r¬ = tpr .fst

  -- --   tpr' : totallyParseable' ⟦ r' ⟧DetReg
  -- --   tpr' = totallyParseable'DetReg r'
  -- --   r'¬ = tpr' .fst
  -- -- totallyParseable'DetReg (r ⊗DetReg[ x ] r') .snd = {!!}
  -- -- totallyParseable'DetReg (literalDetReg c) =
  -- --   totallyParseable'Literal c (DiscreteAlphabet isFinSetAlphabet)
  -- -- totallyParseable'DetReg (r ⊕DetReg[ x ] r₁) = {!!}
  -- -- totallyParseable'DetReg (r *DetReg) = {!!}


  -- -- -- decPropFirst : ?

  -- -- -- disjoint-firsts→disjoint :
  -- -- --   ∀ {FL FL' F F'} {b b'} →
  -- -- --     (r : DetReg FL F b) →
  -- -- --     (r' : DetReg FL' F' b') →
  -- -- --     F ∩ℙ F' ≡ ∅ℙ →
  -- -- --     (not (b and b')) ≡ true →
  -- -- --     disjoint ⟦ r ⟧DetReg ⟦ r' ⟧DetReg
  -- -- -- disjoint-firsts→disjoint ε-DetReg ε-DetReg
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   Empty.rec (false≢true not-both-null)
  -- -- -- disjoint-firsts→disjoint r ⊥-DetReg
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   &-π₂
  -- -- -- disjoint-firsts→disjoint ε-DetReg (r' ⊗DetReg[ x ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint ε-DetReg (literalDetReg c)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint ε-DetReg (r' ⊕DetReg[ x ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint ε-DetReg (r' *DetReg)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   Empty.rec (false≢true not-both-null)
  -- -- -- disjoint-firsts→disjoint ⊥-DetReg r'
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   &-π₁
  -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) ε-DetReg
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' ⊗DetReg[ x₁ ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (literalDetReg c)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' ⊕DetReg[ x₁ ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' *DetReg)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (literalDetReg c) ε-DetReg
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (literalDetReg c) (r' ⊗DetReg[ x ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (literalDetReg c) (literalDetReg c₁)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (literalDetReg c) (r' ⊕DetReg[ x ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (literalDetReg c) (r' *DetReg)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) ε-DetReg
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' ⊗DetReg[ x₁ ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (literalDetReg c)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' ⊕DetReg[ x₁ ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' *DetReg)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r *DetReg) ε-DetReg
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   Empty.rec (false≢true not-both-null)
  -- -- -- disjoint-firsts→disjoint (r *DetReg) (r' ⊗DetReg[ x ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r *DetReg) (literalDetReg c)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r *DetReg) (r' ⊕DetReg[ x ] r'')
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   {!!}
  -- -- -- disjoint-firsts→disjoint (r *DetReg) (r' *DetReg)
  -- -- --   disjoint-firsts not-both-null =
  -- -- --   Empty.rec (false≢true not-both-null)

  -- -- -- unambiguous-DetReg :
  -- -- --   ∀ {FL F} {b} (r : DetReg FL F b) → unambiguous (⟦ r ⟧DetReg)
  -- -- -- unambiguous-DetReg ε-DetReg = unambiguousε isFinSetAlphabet
  -- -- -- unambiguous-DetReg ⊥-DetReg = unambiguous⊥
  -- -- -- unambiguous-DetReg (r ⊗DetReg[ x ] r₁) = {!!}
  -- -- -- unambiguous-DetReg (literalDetReg c) =
  -- -- --   unambiguous-literal c isFinSetAlphabet
  -- -- -- unambiguous-DetReg (r ⊕DetReg[ x ] r') =
  -- -- --   unambiguous⊕
  -- -- --     (disjoint-firsts→disjoint r r' x {!!})
  -- -- --     unambig-r
  -- -- --     unambig-r'
  -- -- --     isFinSetAlphabet
  -- -- --   where
  -- -- --   unambig-r = unambiguous-DetReg r
  -- -- --   unambig-r' = unambiguous-DetReg r'

  -- -- -- unambiguous-DetReg (r *DetReg) = {!!}
