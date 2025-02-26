open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

module Grammar.Subgrammar.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty

open import Grammar Alphabet hiding (k)
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.HLevels.MonoInjective Alphabet

open import Term Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX ℓY ℓ : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

Ω : Grammar (ℓ-suc ℓ)
Ω {ℓ = ℓ} w = hProp ℓ

isSetGrammar-Ω : isSetGrammar (Ω {ℓ = ℓ})
isSetGrammar-Ω w = isSetHProp

isSet⊢Ω : isSet (A ⊢ Ω {ℓ = ℓ})
isSet⊢Ω = isSetΠ (λ w → isSet→ (isSetGrammar-Ω w))

opaque
  unfolding ⊤
  true : ⊤ ⊢ Ω {ℓ = ℓ}
  true w x .fst = Unit*
  true w x .snd = isPropUnit*

  false : ⊤ ⊢ Ω {ℓ = ℓ}
  false w x .fst = Empty.⊥*
  false w x .snd = Empty.isProp⊥*

-- A subgrammar is a subobject in the category of grammars
-- Intuitively,
-- if a grammar A is a map from strings to sets of parses,
-- a subgrammar is map that picks out
-- a subset of parses for each string
--
-- More precisely, we'll handle these by means of
-- the subobject classifier. i.e. a subgrammar of A
-- is uniquely identified by a morphism from
-- A to Ω
--
-- It isn't clear to me how to best expose this syntactically in
-- the language
--
-- Even if these aren't exposed in the language itself, it gives
-- a nice interface to easily axiomatize a
-- selection of propositions
--
-- We could just add in constructs to the language like we did
-- with equalizers, although I'm not sure if we'd need to restrict
-- the type of propositions of not
-- For instance, in the cases we care about, we could just
-- restrict the language of propositions you can perform the
-- following constructions on to be something like
--    - the proposition that two maps are equal, recovering
--      the definition of equalizers
--    - the proposition that some grammar is uninhabited. For example
--      you could take the subgrammar of A that doesn't start
--      with the character c
--      -  which would be the subgrammar over the proposition
--         that A & (＂ c ＂ ⊗ ⊤) ⊢ ⊥
module Subgrammar {ℓ} {A : Grammar ℓA} (p : A ⊢ Ω {ℓ = ℓ}) where
  opaque
    unfolding ⊤ true
    subgrammar : Grammar (ℓ-max ℓA ℓ)
    subgrammar w = Σ[ x ∈ A w ] ⟨ p w x ⟩

    sub-π : subgrammar ⊢ A
    sub-π w = fst

    -- p holds for the image of sub-π
    sub-π-pf : p ∘g sub-π ≡ true ∘g ⊤-intro
    sub-π-pf = funExt (λ w → funExt λ x →
      Σ≡Prop
        (λ _ → isPropIsProp)
        (hPropExt (p w (x .fst) .snd) (true w _ .snd)
          _
          λ _ → x .snd)
      )

  module _ (f : B ⊢ A) (pf : ∀ w x → ⟨ p w (f w x) ⟩) where
    opaque
      unfolding true ⊤
      insert-pf : p ∘g f ≡ true ∘g ⊤-intro
      insert-pf = funExt λ w → funExt λ x →
        Σ≡Prop
          (λ _ → isPropIsProp)
          (hPropExt (p w (f w x) .snd) isPropUnit* _ λ _ → pf w x)

  module _
    (f : B ⊢ A)
    (pB : p ∘g f ≡ true ∘g ⊤-intro) where
    opaque
      unfolding subgrammar
      extract-pf :
        ∀ (w : String) → (x : B w) →
        ⟨ p w (f w x) ⟩
      extract-pf w x =
        transport
          (sym (cong fst (funExt⁻ (funExt⁻ pB w) x)))
          tt*

      sub-intro : B ⊢ subgrammar
      sub-intro w x .fst = f w x
      sub-intro w x .snd = extract-pf w x

      sub-β : sub-π ∘g sub-intro ≡ f
      sub-β = refl

  module _
    (f : B ⊢ subgrammar)
    where
    opaque
      unfolding subgrammar sub-intro
      private
        the-path : p ∘g sub-π ∘g f ≡ true ∘g ⊤-intro
        the-path = cong (_∘g f) sub-π-pf

      sub-η :
        f
          ≡
        sub-intro
          (sub-π ∘g f)
          the-path  -- writing "the-path" here works but
                    -- cong (_∘g f) sub-π-pf is a weird levels error.
                    -- Not quite sure why
      sub-η i = f

  -- if you can build a section, then p holds over all of
  -- A
  -- the statement "p ≡ true ∘g ⊤-intro" means
  -- semantically ∀ w → (x : A w) → ⟨ p w x ⟩
  -- i.e. that p holds for each A parse
  subgrammar-section :
    (f : A ⊢ subgrammar) →
    (sub-π ∘g f ≡ id) →
    p ≡ true ∘g ⊤-intro
  subgrammar-section f sec =
    cong (p ∘g_) (sym sec)
    ∙ cong (_∘g f) sub-π-pf
    ∙ cong (true ∘g_) (unambiguous⊤ _ _)

  opaque
    unfolding sub-π
    isMono-sub-π : isMono sub-π
    isMono-sub-π e e' π≡ = funExt λ w → funExt λ x →
      ΣPathP (
        (funExt⁻ (funExt⁻ π≡ w) x) ,
        (isProp→PathP (λ i → p w _ .snd) _ _)
      )

open Subgrammar

module _
  {ℓ'}
  {X : Type ℓX} (F : X → Functor X) (A : X → Grammar ℓA)
  (p : ∀ (x : X) → μ F x ⊢ Ω {ℓ = ℓ'})
  (pf : ∀ (x : X) →
    p x ∘g roll ∘g map (F x) (λ y → sub-π (p y))
      ≡
    true ∘g ⊤-intro
  )
  where

  subgrammar-ind-alg : Algebra F (λ x → subgrammar (p x))
  subgrammar-ind-alg x =
    sub-intro
      (p x)
      (roll ∘g map (F x) (λ y → sub-π (p y)))
      (pf x)

  sub-π-homo :
    Homomorphism F subgrammar-ind-alg (initialAlgebra F)
  sub-π-homo .fst x = sub-π (p x)
  sub-π-homo .snd x = is-homo
    where
    opaque
      unfolding sub-π sub-intro
      is-homo :
        sub-π (p x) ∘g subgrammar-ind-alg x
        ≡
        initialAlgebra F x ∘g map (F x) (λ y → sub-π (p y))
      is-homo = refl

  subgrammar-ind' : ∀ (x : X) → μ F x ⊢ subgrammar (p x)
  subgrammar-ind' = rec F subgrammar-ind-alg

  -- p holds over all of μ F x, for all x
  subgrammar-ind : ∀ (x : X) → p x ≡ true ∘g ⊤-intro
  subgrammar-ind x =
    subgrammar-section
      (p x)
      (subgrammar-ind' x)
      (ind-id'
        F
        (compHomo F
          (initialAlgebra F)
          subgrammar-ind-alg
          (initialAlgebra F)
          sub-π-homo
          (recHomo F subgrammar-ind-alg)
        )
        x
      )

module _
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  (f : B ⊢ A)
  (p : A ⊢ Ω {ℓ = ℓ})
  where

  preimage : Grammar (ℓ-max ℓB ℓ)
  preimage = subgrammar (p ∘g f)

  preimage-map : preimage ⊢ subgrammar p
  preimage-map = sub-intro p (f ∘g sub-π (p ∘g f)) (sub-π-pf (p ∘g f))

module _ {A : Grammar ℓA} {B : Grammar ℓB}
  (f : B ⊢ A)
  (isSet-A : isSetGrammar A)
  (isMono-f : isMono f)
  where
  mono-prop : A ⊢ Ω
  mono-prop w x .fst = Σ[ y ∈ B w ] f w y ≡ x
  mono-prop w x .snd = isMono→hasPropFibers isSet-A isMono-f w x

  mono→subgrammar : Grammar (ℓ-max ℓA ℓB)
  mono→subgrammar = subgrammar mono-prop

module _
  {A : Grammar ℓA}
  (unambig-A : unambiguous A)
  (B : Grammar ℓB)
  where
  unambiguous-prop : B ⊢ Ω
  unambiguous-prop w x .fst = A w
  unambiguous-prop w x .snd =
    EXTERNAL.unambiguous→isLang unambig-A w

  unambiguous→subgrammar : Grammar (ℓ-max ℓA ℓB)
  unambiguous→subgrammar = subgrammar unambiguous-prop
