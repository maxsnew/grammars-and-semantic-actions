{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.List
open import Cubical.Data.Empty as Empty hiding (⊥;⊥*)
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Negation Alphabet
open import Grammar.Literal Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Product Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.String Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl


open isStrongEquivalence

unambiguous : Grammar ℓg → Typeω
unambiguous {ℓg = ℓg} g = isMono {g = g}{h = ⊤} (⊤-intro {g = g})

module _ where
  -- This is not intended to be used in the library
  -- This is the external notion of what we'd expected an unambiguous
  -- grammar to be, that each input string is parsed uniquely

  unambiguous' : Grammar ℓg → Type ℓg
  unambiguous' g = ∀ w → isProp (g w)

  unambiguous'→unambiguous : unambiguous' g → unambiguous g
  unambiguous'→unambiguous {g = g} unambig' e e' _ =
    funExt (λ w → funExt (λ x → unambig' w (e w x) (e' w x)))

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    opaque
      unfolding uniquely-supported-⌈w⌉ internalize ⊤
      unambiguous→unambiguous' : unambiguous g → unambiguous' g
      unambiguous→unambiguous' {g = g} unambig w pg pg' =
        isMono→injective unambig w pg pg' refl
        where
        pick-parse : ∀ w' (h : Grammar ℓh) → h w' → ⌈ w' ⌉ ⊢ h
        pick-parse w' h p w'' x =
          subst h (uniquely-supported-⌈w⌉ isFinSetAlphabet w' w'' x) p

        isMono→injective : {e : h ⊢ ⊤} →
          isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
        isMono→injective {h = h}{e = e} mono-e w p p' ewp≡ewp' =
          sym (transportRefl p) ∙
          cong (λ a → transp (λ i → h (a i)) i0 p) (isSetString _ w refl _) ∙
          funExt⁻
            (funExt⁻ (mono-e (pick-parse w h p) (pick-parse w h p') refl) w)
              (internalize w) ∙
          cong (λ a → transp (λ i → h (a i)) i0 p') (isSetString _ w _ refl) ∙
          transportRefl p'

  -- Thus the internal and external notions of unambiguity are logically
  -- equivalent. Moreover, each of these can be show to be prop-valued
  -- (up to rewriting the definition of mono to not be a Typeω), so the
  -- logical equivalence can be lifted to an iso

totallyParseable : Grammar ℓg → Type (ℓ-suc ℓg)
totallyParseable {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] StrongEquivalence (g ⊕ g') ⊤

open StrongEquivalence

opaque
  unfolding ⊤-intro
  totallyParseable→unambiguous :
    totallyParseable g → unambiguous g
  totallyParseable→unambiguous parseable =
    Mono∘g {e = ⊕-inl}
      (isStrongEquivalence→isMono
        (parseable .snd .fun)
        (StrongEquivalence→isStrongEquivalence _ _ (parseable .snd)))
      isMono-⊕-inl

decidable : Grammar ℓg → Type ℓg
decidable g = StrongEquivalence (g ⊕ (¬ g)) ⊤

decidable→totallyParseable :
  decidable g → totallyParseable g
decidable→totallyParseable dec-g = _ , dec-g

opaque
  unfolding ⊤
  unambiguous⊤ : unambiguous ⊤
  unambiguous⊤ e e' _ = refl

opaque
  unfolding ⊤*
  unambiguous⊤* : ∀ {ℓg} → unambiguous (⊤* {ℓg})
  unambiguous⊤* e e' _ = refl

unambiguous⊥ : unambiguous ⊥
unambiguous⊥ {k = k} e e' !∘e≡!∘e' =
  is-initial→propHoms (g⊢⊥→is-initial e) _ _

-- TODO this changes to unambiguous-ext
opaque
  unfolding ε
  unambiguousε : unambiguous ε
  unambiguousε = unambiguous'→unambiguous (λ w → isSetString w [])
opaque
  unfolding literal
  unambiguous-literal : (c : ⟨ Alphabet ⟩) → unambiguous (literal c)
  unambiguous-literal c = unambiguous'→unambiguous (λ w → isSetString w [ c ])

-- Breaking abstractions to prove this.
-- Should be justified because the axiom we are adding
-- is "string ≅ ⊤", not just the existence of a map ⊤ ⊢ string
string≅⊤ : StrongEquivalence string ⊤
string≅⊤ .fun = ⊤-intro
string≅⊤ .inv = ⊤→string
string≅⊤ .sec = unambiguous⊤ _ _ {!!}
string≅⊤ .ret = {!!}
  -- funExt λ {
  --   [] → funExt λ {
  --     (KL*.nil .[] x) → cong (KL*.nil []) (isSetString [] [] refl x)
  --   ; (KL*.cons .[] x) →
  --     Empty.rec (¬nil≡cons (x .fst .snd ∙
  --                          cong (_++ x .fst .fst .snd) (x .snd .fst .snd))) }
  -- ; (c ∷ w) → funExt (λ {
  --   (KL*.nil .(c ∷ w) x) → Empty.rec (¬cons≡nil x)
  -- ; (KL*.cons .(c ∷ w) x) →
  --   cong (KL*.cons (c ∷ w))
  --     {!!}
      -- (⊗≡ (((c ∷ [] , w) , (λ _ → c ∷ w)) , (c , (λ _ → c ∷ [])) , ⌈ w ⌉)
      --   x
      --   (≡-× (cong (_∷ [])
      --     (cons-inj₁ (x .fst .snd ∙
      --       cong (_++ x .fst .fst .snd) (x .snd .fst .snd))) ∙
      --     sym (x .snd .fst .snd))
      --     (cons-inj₂ (x .fst .snd ∙
      --       cong (_++ x .fst .fst .snd) (x .snd .fst .snd))))
      --     (isProp→PathP (λ _ → {!isSetString!}) ((c , (λ _ → c ∷ [])) , ⌈ w ⌉) (x .snd)))
  -- }) }

-- open isStrongEquivalence
-- unambiguous≅ : StrongEquivalence g h → unambiguous g → unambiguous h
-- unambiguous≅ eq unambig-g =
--   Mono∘g {e = eq .inv} unambig-g
--     (isStrongEquivalence→isMono
--       (eq .inv) (isStrEq (eq .fun) (eq .ret) (eq .sec)))

-- unabmiguous-string : unambiguous string
-- unabmiguous-string =
--   unambiguous≅ (sym-strong-equivalence string≅⊤) unambiguous⊤

_∉first_ : (c : ⟨ Alphabet ⟩) → (g : Grammar ℓg) → Type ℓg
c ∉first g = (literal c ⊗ ⊤) & g ⊢ ⊥

_∉last_ : (c : ⟨ Alphabet ⟩) → (g : Grammar ℓg) → Type ℓg
c ∉last g = (⊤ ⊗ literal c) & g ⊢ ⊥

nonempty : Grammar ℓg → Grammar ℓg
nonempty g = (char ⊗ ⊤) & g

first : Grammar ℓg → Grammar ℓg
first g = g ⟜ (char ⊸ g)

opaque
  unfolding _⊸_ _⟜_ literal
  get-first : (c : ⟨ Alphabet ⟩) (w : String) → g (c ∷ w) → (first g) [ c ]
  get-first c w p w' p⊸ = p⊸ (c ∷ []) (c , refl)

last : Grammar ℓg → Grammar ℓg
last g = (g ⟜ char) ⊸ g

followlast : Grammar ℓg → Grammar ℓg
followlast g = (nonempty g ⊸ g) ⟜ g

disjoint : Grammar ℓg → Grammar ℓh → Type (ℓ-max ℓg ℓh)
disjoint g h = g & h ⊢ ⊥

nullable : Grammar ℓg → Type ℓg
nullable g = ε ⊢ g

¬nullable : Grammar ℓg → Type ℓg
¬nullable g = disjoint g ε

opaque
  unfolding literal ε _&_
  literal¬nullable : (c : ⟨ Alphabet ⟩) → ¬nullable (literal c)
  literal¬nullable c w x = Empty.rec (¬cons≡nil (sym (x .fst) ∙ x .snd))

_∉followlast_ : (c : ⟨ Alphabet ⟩) → (g : Grammar ℓg) → Type ℓg
c ∉followlast g = (nonempty g) ⊗ literal c ⊗ g ⊢ ⊥

