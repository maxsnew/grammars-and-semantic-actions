{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression.Deterministic (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Cubical.Functions.Logic renaming (⊥ to ⊥P)

open import Cubical.Data.FinSet
open import Cubical.Data.List hiding (rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
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
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.RegularExpression.Base Alphabet
open import Term Alphabet
open import Helper

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh
    c : ⟨ Alphabet ⟩

open StrongEquivalence

FollowLastG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FollowLastG g c = (g ⊗ ＂ c ＂ ⊗ string) & g

_∉FollowLast_ : ⟨ Alphabet ⟩ → Grammar ℓg → hProp ℓg
(c ∉FollowLast g) .fst = uninhabited (FollowLastG g c)
(c ∉FollowLast g) .snd = isProp-uninhabited

¬FollowLast : Grammar ℓg → Type ℓg
¬FollowLast g = Σ[ c ∈ ⟨ Alphabet ⟩ ] ⟨ c ∉FollowLast g ⟩

FirstG : Grammar ℓg → ⟨ Alphabet ⟩ → Grammar ℓg
FirstG g c = (＂ c ＂ ⊗ string) & g

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

¬Nullable→char+ : ⟨ ¬Nullable g ⟩ → g ⊢ char +
¬Nullable→char+ notnull =
  ⊕-elim
    (⊥-elim ∘g notnull ∘g &-swap)
    &-π₂
  ∘g &string-split≅ .fun

⊢char+→¬Nullable : g ⊢ char + → ⟨ ¬Nullable g ⟩
⊢char+→¬Nullable e =
  disjoint-ε-char+'
  ∘g id ,&p e

¬Nullable⊗l : ⟨ ¬Nullable g ⟩ → ⟨ ¬Nullable (g ⊗ h) ⟩
¬Nullable⊗l notnull =
  ⊢char+→¬Nullable (char+⊗l→char+ ∘g ¬Nullable→char+ notnull ,⊗ id)

¬Nullable⊗r : ⟨ ¬Nullable g ⟩ → ⟨ ¬Nullable (h ⊗ g) ⟩
¬Nullable⊗r notnull =
  ⊢char+→¬Nullable (char+⊗r→char+ ∘g id ,⊗ ¬Nullable→char+ notnull)

module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
  ∉First⊗l' : ⟨ ¬Nullable g ⟩ → ⟨ c ∉First g ⟩ → ⟨ c ∉First (g ⊗ string) ⟩
  ∉First⊗l' {g = g} {c = c} ¬nullg c∉Fg =
    {!!}

  ∉First⊗l : ⟨ ¬Nullable g ⟩ → ⟨ c ∉First g ⟩ → ⟨ c ∉First (g ⊗ h) ⟩
  ∉First⊗l {g = g} {c = c} {h = h} ¬nullg c∉Fg =
    ∉First⊗l' ¬nullg c∉Fg
    ∘g id ,&p (id ,⊗ string-intro)

  open DecidablePowerset ⟨ Alphabet ⟩
  open DecidableFinitePowerset (⟨ Alphabet ⟩ , isFinSetAlphabet)

  data DetReg : Decℙ → Decℙ → Bool → Type (ℓ-suc ℓ-zero)

  Dec¬FirstLit : ∀ c c' → Dec ⟨ c' ∉First ＂ c ＂ ⟩
  Dec¬FirstLit c c' =
    decRec
      (λ c≡c' →
        no (λ e →
          get⊥
            ((e ∘g ((id ,⊗ string-intro ∘g ⊗-unit-r⁻) ∘g transportG (cong literal c≡c')) ,&p id ∘g &-Δ)
              _ (lit-intro {c}) )))
      (λ c≢c' → yes
        (⊕-elim
          (⊕ᴰ-elim (λ c≡c' → Empty.rec (c≢c' c≡c')) ∘g same-literal c c' ∘g &-swap)
          (disjoint-char-char⊗char+ ∘g literal→char c ,&p literal→char c' ,⊗ id ∘g &-swap)
        ∘g &⊕-distR
        ∘g ((⊗-unit-r ,⊕p id) ∘g ⊗⊕-distL ∘g id ,⊗ (unroll-string≅ .fun)) ,&p id
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

  witness¬¬Nullable :
    ∀ {FL F : Decℙ} →
    (r : DetReg FL F true) →
    ⟨ ¬Nullable ⟦ r ⟧DR ⟩ →
    Empty.⊥

  witness¬Nullable :
    ∀ {FL F : Decℙ} →
    (r : DetReg FL F false) →
    ⟨ ¬Nullable ⟦ r ⟧DR ⟩

  decidable¬Nullable :
    ∀ {FL F : Decℙ} →
    {b : Bool} →
    (r : DetReg FL F b) →
    Dec ⟨ ¬Nullable ⟦ r ⟧DR ⟩

  ¬NullableDecProp :
    ∀ {FL F : Decℙ} →
    {b : Bool} →
    (r : DetReg FL F b) →
    DecProp ℓ-zero

  decidable¬First :
    ∀ {FL F : Decℙ} →
    {b : Bool} →
    (r : DetReg FL F b) →
    (c : ⟨ Alphabet ⟩) →
    Dec ⟨ c ∉First ⟦ r ⟧DR ⟩

  witness¬First :
    ∀ {FL F : Decℙ} →
    {b : Bool} →
    (r : DetReg FL F b) →
    (c : ⟨ Alphabet ⟩) →
    ⟨ ¬DecProp F c ⟩DecProp →
    ⟨ c ∉First ⟦ r ⟧DR ⟩

  -- A deterministic regular expression is parametrized
  -- by its follow last set, first last set, and nullability
  data DetReg where
    εDR : DetReg ∅ℙ ∅ℙ true
    ⊥DR : DetReg ∅ℙ ∅ℙ false
    literalDR :
      (c : ⟨ Alphabet ⟩) →
      DetReg ∅ℙ ⟦ c ⟧ℙ false
    _⊗DR-null[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      (r : DetReg FL F false) →
      (x : FL ∩ℙ F' ≡ ∅ℙ) →
      (r' : DetReg FL' F' true) →
      DetReg
        (FL ∪ℙ F' ∪ℙ FL')
        F
        false
    _⊗DR-notnull[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      (r : DetReg FL F false) →
      (x : FL ∩ℙ F' ≡ ∅ℙ) →
      (r' : DetReg FL' F' false) →
      DetReg
        (FL ∪ℙ F' ∪ℙ FL')
        F
        false
    _⊕DR-ft[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      (r : DetReg FL F false) →
      (x : F ∩ℙ F' ≡ ∅ℙ) →
      (r' : DetReg FL' F' true) →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        true
    _⊕DR-tf[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      (r : DetReg FL F true) →
      (x : F ∩ℙ F' ≡ ∅ℙ) →
      (r' : DetReg FL' F' false) →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        true
    _⊕DR-ff[_]_ :
      ∀ {FL FL' F F' : Decℙ} →
      (r : DetReg FL F false) →
      (x : F ∩ℙ F' ≡ ∅ℙ) →
      (r' : DetReg FL' F' false) →
      DetReg
        (FL ∪ℙ FL')
        (F ∪ℙ F')
        false
    _*DR :
      ∀ {FL F : Decℙ} →
      (r : DetReg FL F false) →
      DetReg
        (F ∪ℙ FL)
        F
        true

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

  DetReg→Grammar r = ⟦ DetReg→Regex r ⟧r

  ⟦_⟧DR = DetReg→Grammar

  ¬NullableDecProp r .fst = ¬Nullable ⟦ r ⟧DR
  ¬NullableDecProp r .snd = decidable¬Nullable r

  witness¬Nullable ⊥DR = &-π₂
  witness¬Nullable (literalDR c) = disjoint-ε-literal c
  witness¬Nullable (r ⊗DR-null[ x ] r') =
    ¬Nullable⊗l (witness¬Nullable r)
  witness¬Nullable (r ⊗DR-notnull[ x ] r') =
    ¬Nullable⊗l (witness¬Nullable r)
  witness¬Nullable (r ⊕DR-ff[ x ] r') =
    ⊕-elim (witness¬Nullable r) (witness¬Nullable r')
    ∘g &⊕-distL

  witness¬¬Nullable εDR e = get⊥ ((e ∘g &-Δ) _ ε-intro)
  witness¬¬Nullable (r ⊕DR-ft[ x ] r') e =
    witness¬¬Nullable r' (e ∘g id ,&p ⊕-inr)
  witness¬¬Nullable (r ⊕DR-tf[ x ] r') e =
    witness¬¬Nullable r (e ∘g id ,&p ⊕-inl)
  witness¬¬Nullable (r *DR) e =
    get⊥ ((e ∘g id ,&p NIL ∘g &-Δ) _ ε-intro)

  decidable¬Nullable {b = false} r = yes (witness¬Nullable r)
  decidable¬Nullable {b = true} r = no (witness¬¬Nullable r)

  witness¬First εDR c c∉F =
    disjoint-ε-char+
    ∘g id ,&p literal→char c ,⊗ string-intro
    ∘g &-swap
  witness¬First ⊥DR c c∉F = &-π₂
  witness¬First (literalDR c') c c∉F =
    ⊕ᴰ-elim (λ c'≡c → Empty.rec (c∉F (sym c'≡c)))
    ∘g same-first c' c
    ∘g &-swap
  witness¬First (r ⊗DR-null[ x ] r') c c∉F =
    ∉First⊗l (witness¬Nullable r) (witness¬First r c c∉F)
  witness¬First (r ⊗DR-notnull[ x ] r') c c∉F =
    ∉First⊗l (witness¬Nullable r) (witness¬First r c c∉F)
  witness¬First (r ⊕DR-ft[ x ] r') c c∉F =
    ⊕-elim
      (witness¬First r c {!c∉F !})
      (witness¬First r' c {!!})
    ∘g &⊕-distL
  witness¬First (r ⊕DR-tf[ x ] r') c c∉F =
    {!!}
  witness¬First (r ⊕DR-ff[ x ] r') c c∉F =
    {!!}
  witness¬First (r *DR) c c∉F =
    {!!}

  decidable¬First = {!!}

  -- -- -- -- -- -- totallyParseable'DetReg : ∀ {FL F b}
  -- -- -- -- -- --   (r : DetReg FL F b) →
  -- -- -- -- -- --   totallyParseable' ⟦ r ⟧DetReg
  -- -- -- -- -- -- totallyParseable'DetReg ε-DetReg .fst = char +
  -- -- -- -- -- -- totallyParseable'DetReg ε-DetReg .snd = sym≅ unroll-string≅
  -- -- -- -- -- -- totallyParseable'DetReg ⊥-DetReg .fst = ⊤
  -- -- -- -- -- -- totallyParseable'DetReg ⊥-DetReg .snd = ⊥⊕≅ ⊤ ≅∙ sym≅ string≅⊤
  -- -- -- -- -- -- totallyParseable'DetReg (r ⊗DetReg[ x ] r') .fst =
  -- -- -- -- -- --   (⟦ r ⟧DetReg ⊗  r'¬ ) ⊕
  -- -- -- -- -- --   (r¬ ⊗ ⟦ r' ⟧DetReg) ⊕
  -- -- -- -- -- --   (r¬ ⊗ r'¬)
  -- -- -- -- -- --   where
  -- -- -- -- -- --   tpr : totallyParseable' ⟦ r ⟧DetReg
  -- -- -- -- -- --   tpr = totallyParseable'DetReg r
  -- -- -- -- -- --   r¬ = tpr .fst

  -- -- -- -- -- --   tpr' : totallyParseable' ⟦ r' ⟧DetReg
  -- -- -- -- -- --   tpr' = totallyParseable'DetReg r'
  -- -- -- -- -- --   r'¬ = tpr' .fst
  -- -- -- -- -- -- totallyParseable'DetReg (r ⊗DetReg[ x ] r') .snd = {!!}
  -- -- -- -- -- -- totallyParseable'DetReg (literalDetReg c) =
  -- -- -- -- -- --   totallyParseable'Literal c (DiscreteAlphabet isFinSetAlphabet)
  -- -- -- -- -- -- totallyParseable'DetReg (r ⊕DetReg[ x ] r₁) = {!!}
  -- -- -- -- -- -- totallyParseable'DetReg (r *DetReg) = {!!}


  -- -- -- -- -- -- -- unambiguous-DetReg :
  -- -- -- -- -- -- --   ∀ {FL F} {b} (r : DetReg FL F b) → unambiguous (⟦ r ⟧DetReg)
  -- -- -- -- -- -- -- unambiguous-DetReg ε-DetReg = unambiguousε isFinSetAlphabet
  -- -- -- -- -- -- -- unambiguous-DetReg ⊥-DetReg = unambiguous⊥
  -- -- -- -- -- -- -- unambiguous-DetReg (r ⊗DetReg[ x ] r₁) = {!!}
  -- -- -- -- -- -- -- unambiguous-DetReg (literalDetReg c) =
  -- -- -- -- -- -- --   unambiguous-literal c isFinSetAlphabet
  -- -- -- -- -- -- -- unambiguous-DetReg (r ⊕DetReg[ x ] r') =
  -- -- -- -- -- -- --   unambiguous⊕
  -- -- -- -- -- -- --     (disjoint-firsts→disjoint r r' x {!!})
  -- -- -- -- -- -- --     unambig-r
  -- -- -- -- -- -- --     unambig-r'
  -- -- -- -- -- -- --     isFinSetAlphabet
  -- -- -- -- -- -- --   where
  -- -- -- -- -- -- --   unambig-r = unambiguous-DetReg r
  -- -- -- -- -- -- --   unambig-r' = unambiguous-DetReg r'

  -- -- -- -- -- -- -- unambiguous-DetReg (r *DetReg) = {!!}
