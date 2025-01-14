open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Deterministic (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Cubical.Data.FinSet
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Empty as Empty

open import Cubical.Relation.Nullary.Base

open import Grammar Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.RegularExpression.Base Alphabet
open import Term Alphabet
open import Helper

private
  variable ℓg ℓh : Level

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

¬Nullable_ : Grammar ℓg → Type ℓg
¬Nullable g = uninhabited (NullableG g)

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  open DecidablePowerset ⟨ Alphabet ⟩
  open DecidableFinitePowerset (⟨ Alphabet ⟩ , isFinSetAlphabet)

  -- A deterministic regular expression is parametrized
  -- by its follow last set, first last set, and nullability
  data DetReg : Decℙ → Decℙ → Bool → Type (ℓ-suc ℓ-zero) where
    ε-DetReg : DetReg ∅ℙ ∅ℙ true
    ⊥-DetReg : DetReg ∅ℙ ∅ℙ false
    _⊗DetReg[_]_ :
      ∀ {FL FL' F F' : Decℙ} {b' : Bool} →
      DetReg FL F false →
      FL ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' b' →
      DetReg
        (if b' then
        FL ∪ℙ F' ∪ℙ FL'
        else
        FL')
        F
        false
    literalDetReg : (c : ⟨ Alphabet ⟩) → DetReg ∅ℙ ⟦ c ⟧ℙ false
    _⊕DetReg[_]_ :
      ∀ {FL FL' F F' : Decℙ} {b b' : Bool} →
      DetReg FL F b →
      F ∩ℙ F' ≡ ∅ℙ →
      DetReg FL' F' b' →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        -- (b or b')
        (not (b and b'))
    _*DetReg :
      ∀ {FL F : Decℙ} →
      DetReg FL F false →
      DetReg
        (F ∪ℙ FL)
        F
        true

  DetReg→Regex : ∀ {FL F} {b} → DetReg FL F b → Regex
  DetReg→Regex ε-DetReg = ε-Reg
  DetReg→Regex ⊥-DetReg = ⊥-Reg
  DetReg→Regex (r ⊗DetReg[ _ ] r') =
    (DetReg→Regex r) ⊗Reg (DetReg→Regex r')
  DetReg→Regex (literalDetReg c) = literalReg c
  DetReg→Regex (r ⊕DetReg[ _ ] r') =
    (DetReg→Regex r) ⊕Reg (DetReg→Regex r')
  DetReg→Regex (r *DetReg) =
    KL*Reg (DetReg→Regex r)

  DetReg→Grammar : ∀ {FL F} {b} → DetReg FL F b → Grammar ℓ-zero
  DetReg→Grammar r = ⟦ DetReg→Regex r ⟧r

  ⟦_⟧DetReg : ∀ {FL F} {b} → DetReg FL F b → Grammar ℓ-zero
  ⟦_⟧DetReg = DetReg→Grammar

  dec¬First : ∀ {FL F b}
    (r : DetReg FL F b) →
    (c : ⟨ Alphabet ⟩) →
    Dec ⟨ c ∉First ⟦ r ⟧DetReg ⟩
  dec¬First ε-DetReg c = yes {!!}
  dec¬First ⊥-DetReg c = yes &-π₂
  dec¬First (r ⊗DetReg[ x ] r₁) c = {!dec¬First r c!}
  dec¬First (literalDetReg c₁) c = {!!}
  dec¬First (r ⊕DetReg[ x ] r₁) c = {!!}
  dec¬First (r *DetReg) c = {!!}

  totallyParseableDetReg : ∀ {FL F b}
    (r : DetReg FL F b) →
    totallyParseable ⟦ r ⟧DetReg
  totallyParseableDetReg ε-DetReg .fst = char +
  totallyParseableDetReg ε-DetReg .snd =
    sym≅ (*≅ε⊕g⊗g* char) ≅∙ string≅⊤
  totallyParseableDetReg ⊥-DetReg .fst = ⊤
  totallyParseableDetReg ⊥-DetReg .snd = ⊥⊕≅ ⊤
  totallyParseableDetReg (r ⊗DetReg[ x ] r₁) = {!!}
  totallyParseableDetReg (literalDetReg c) .fst =
    ε ⊕ (char-complement c ⊗ ⊤)
  totallyParseableDetReg (literalDetReg c) .snd = {!!}
  totallyParseableDetReg (r ⊕DetReg[ x ] r₁) = {!!}
  totallyParseableDetReg (r *DetReg) = {!!}


  -- decPropFirst : ?

  -- disjoint-firsts→disjoint :
  --   ∀ {FL FL' F F'} {b b'} →
  --     (r : DetReg FL F b) →
  --     (r' : DetReg FL' F' b') →
  --     F ∩ℙ F' ≡ ∅ℙ →
  --     (not (b and b')) ≡ true →
  --     disjoint ⟦ r ⟧DetReg ⟦ r' ⟧DetReg
  -- disjoint-firsts→disjoint ε-DetReg ε-DetReg
  --   disjoint-firsts not-both-null =
  --   Empty.rec (false≢true not-both-null)
  -- disjoint-firsts→disjoint r ⊥-DetReg
  --   disjoint-firsts not-both-null =
  --   &-π₂
  -- disjoint-firsts→disjoint ε-DetReg (r' ⊗DetReg[ x ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint ε-DetReg (literalDetReg c)
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint ε-DetReg (r' ⊕DetReg[ x ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint ε-DetReg (r' *DetReg)
  --   disjoint-firsts not-both-null =
  --   Empty.rec (false≢true not-both-null)
  -- disjoint-firsts→disjoint ⊥-DetReg r'
  --   disjoint-firsts not-both-null =
  --   &-π₁
  -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) ε-DetReg
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' ⊗DetReg[ x₁ ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (literalDetReg c)
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' ⊕DetReg[ x₁ ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊗DetReg[ x ] r₁) (r' *DetReg)
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (literalDetReg c) ε-DetReg
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (literalDetReg c) (r' ⊗DetReg[ x ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (literalDetReg c) (literalDetReg c₁)
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (literalDetReg c) (r' ⊕DetReg[ x ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (literalDetReg c) (r' *DetReg)
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) ε-DetReg
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' ⊗DetReg[ x₁ ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (literalDetReg c)
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' ⊕DetReg[ x₁ ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r ⊕DetReg[ x ] r₁) (r' *DetReg)
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r *DetReg) ε-DetReg
  --   disjoint-firsts not-both-null =
  --   Empty.rec (false≢true not-both-null)
  -- disjoint-firsts→disjoint (r *DetReg) (r' ⊗DetReg[ x ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r *DetReg) (literalDetReg c)
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r *DetReg) (r' ⊕DetReg[ x ] r'')
  --   disjoint-firsts not-both-null =
  --   {!!}
  -- disjoint-firsts→disjoint (r *DetReg) (r' *DetReg)
  --   disjoint-firsts not-both-null =
  --   Empty.rec (false≢true not-both-null)

  -- unambiguous-DetReg :
  --   ∀ {FL F} {b} (r : DetReg FL F b) → unambiguous (⟦ r ⟧DetReg)
  -- unambiguous-DetReg ε-DetReg = unambiguousε isFinSetAlphabet
  -- unambiguous-DetReg ⊥-DetReg = unambiguous⊥
  -- unambiguous-DetReg (r ⊗DetReg[ x ] r₁) = {!!}
  -- unambiguous-DetReg (literalDetReg c) =
  --   unambiguous-literal c isFinSetAlphabet
  -- unambiguous-DetReg (r ⊕DetReg[ x ] r') =
  --   unambiguous⊕
  --     (disjoint-firsts→disjoint r r' x {!!})
  --     unambig-r
  --     unambig-r'
  --     isFinSetAlphabet
  --   where
  --   unambig-r = unambiguous-DetReg r
  --   unambig-r' = unambiguous-DetReg r'

  -- unambiguous-DetReg (r *DetReg) = {!!}
