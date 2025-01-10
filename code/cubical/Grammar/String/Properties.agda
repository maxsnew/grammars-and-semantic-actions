{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Top Alphabet
open import Grammar.Literal Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet

open import Term.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

-- This is the definition of unambiguity you'd expect in the grammar model of the
-- theory, that each string has at most one parse (up to paths bw parses)
--
-- These definitions should not be used for abstract grammars, but can prove
-- useful for showing unambiguity for things like literals, ε, and string
module EXTERNAL where
  propParses : Grammar ℓg → Type ℓg
  propParses g = ∀ w → isProp (g w)

  propParses→unambiguous' : propParses g → unambiguous' g
  propParses→unambiguous' {g = g} unambig' e e' _ =
    funExt (λ w → funExt (λ x → unambig' w (e w x) (e' w x)))

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    opaque
      unfolding uniquely-supported-⌈w⌉ internalize ⊤
      unambiguous'→propParses : unambiguous' g → propParses g
      unambiguous'→propParses {g = g} unambig w pg pg' =
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

    unambigous→propParses : unambiguous g → propParses g
    unambigous→propParses unambig =
      unambiguous'→propParses (unambiguous→unambiguous' unambig)

    propParses→unambiguous : propParses g → unambiguous g
    propParses→unambiguous ppg =
      unambiguous'→unambiguous (propParses→unambiguous' ppg)

-- TODO fix unambiguity for strings
opaque
  unfolding ε literal _⊗_
  propParses-string : EXTERNAL.propParses string
  propParses-string = ?
--   propParses-string [] (roll .[] (nil , x)) (roll .[] (cons , y)) = {!!}
--   propParses-string [] (roll .[] (nil , x)) (roll .[] (nil , y)) =
--     cong (λ z → roll [] (nil , z)) (cong (λ z → lift (lift z)) (isSetString _ _ _ _))
--   propParses-string [] (roll .[] (cons , x)) (roll .[] (cons , y)) = {!!}
--   propParses-string [] (roll .[] (cons , x)) (roll .[] (nil , y)) = {!!}
--   propParses-string (c ∷ w) (roll .(c ∷ w) (nil , x)) (roll .(c ∷ w) (cons , y)) = {!!}
--   propParses-string (c ∷ w) (roll .(c ∷ w) (nil , x)) (roll .(c ∷ w) (nil , y)) = {!!}
--   propParses-string (c ∷ w) (roll .(c ∷ w) (cons , x)) (roll .(c ∷ w) (cons , y)) = {!!}
--   propParses-string (c ∷ w) (roll .(c ∷ w) (cons , x)) (roll .(c ∷ w) (nil , y)) = {!!}
--   propParses-string [] (nil .[] x) (nil .[] y) =
--     cong (nil []) (isSetString _ _ _ _)
--   propParses-string [] (nil .[] _) (cons .[] x) =
--     Empty.rec
--       (¬nil≡cons
--         (x .fst .snd ∙
--           cong (_++ x .fst .fst .snd)
--             (x .snd .fst .snd)))
--   propParses-string [] (cons .[] x) _ =
--     Empty.rec
--       (¬nil≡cons
--         (x .fst .snd ∙
--           cong (_++ x .fst .fst .snd)
--             (x .snd .fst .snd)))
--   propParses-string (c ∷ w) (nil .(c ∷ w) x) (nil .(c ∷ w) y) =
--     Empty.rec (¬nil≡cons (sym x))
--   propParses-string (c ∷ w) (nil .(c ∷ w) x) (cons .(c ∷ w) y) =
--     Empty.rec (¬nil≡cons (sym x))
--   propParses-string (c ∷ w) (cons .(c ∷ w) x) (nil .(c ∷ w) y) =
--     Empty.rec (¬nil≡cons (sym y))
--   propParses-string (c ∷ w) (cons .(c ∷ w) x) (cons .(c ∷ w) y) =
--     cong (cons (c ∷ w))
--       (⊗≡ x y
--         (≡-× (x .snd .fst .snd ∙
--              cong ([_]) (sym c≡x₂₁₁ ∙ c≡y₂₁₁) ∙
--              sym (y .snd .fst .snd))
--              (sym w≡x₁₁₂ ∙ w≡y₁₁₂))
--         (ΣPathP ((ΣPathP
--           ((sym c≡x₂₁₁ ∙ c≡y₂₁₁) ,
--           isProp→PathP (λ i → isSetString _ _) _ _)) ,
--           isProp→PathP
--             (λ i → isProp-at-w'i i)
--             (x .snd .snd) (y .snd .snd))))
--     where
--       c≡x₂₁₁ : c ≡ x .snd .fst .fst
--       c≡x₂₁₁ =
--         cons-inj₁
--             (x .fst .snd ∙ cong (_++ x .fst .fst .snd) (x .snd .fst .snd))

--       c≡y₂₁₁ : c ≡ y .snd .fst .fst
--       c≡y₂₁₁ =
--         cons-inj₁
--             (y .fst .snd ∙ cong (_++ y .fst .fst .snd) (y .snd .fst .snd))

--       w≡x₁₁₂ : w ≡ x .fst .fst .snd
--       w≡x₁₁₂ =
--         cons-inj₂ (x .fst .snd ∙ (cong (_++ x .fst .fst .snd) (x .snd .fst .snd)) )

--       w≡y₁₁₂ : w ≡ y .fst .fst .snd
--       w≡y₁₁₂ =
--         cons-inj₂ (y .fst .snd ∙ (cong (_++ y .fst .fst .snd) (y .snd .fst .snd)) )

--       w' : x .fst .fst .snd ≡ y .fst .fst .snd
--       w' =
--         (λ i →
--         (≡-×
--         (x .snd .fst .snd ∙
--          (λ i₁ → [ ((λ i₂ → c≡x₂₁₁ (~ i₂)) ∙ c≡y₂₁₁) i₁ ]) ∙
--          (λ i₁ → y .snd .fst .snd (~ i₁)))
--         ((λ i₁ → w≡x₁₁₂ (~ i₁)) ∙ w≡y₁₁₂) i .snd))

--       isProp-at-w : isProp (KL* char w)
--       isProp-at-w = propParses-string w

--       -- There has to be a nicer way to extract this goal out
--       -- from isProp (KL* char w) because w is equal to each of
--       -- the endpoints of w'
--       -- I guessed at what the path variables need to be below
--       -- and somehow it worked
--       isProp-at-w'i : (i : I) → isProp (KL* char (w' i))
--       isProp-at-w'i i =
--         transport
--         (cong (λ z → isProp (KL* char z))
--           (w≡x₁₁₂ ∙ (λ j → (w') (i ∧ j))))
--         isProp-at-w

unambiguous'-string : unambiguous' string
unambiguous'-string = EXTERNAL.propParses→unambiguous' propParses-string

unambiguous-string : unambiguous string
unambiguous-string = unambiguous'→unambiguous unambiguous'-string

⊤→string : ⊤ ⊢ string
⊤→string w _ = ⌈w⌉→string {w = w} w (internalize w)

⊤*→string : ∀ {ℓg} → ⊤* {ℓg} ⊢ string
⊤*→string w _ = ⌈w⌉→string {w = w} w (internalize w)

open StrongEquivalence
string≅⊤ : StrongEquivalence string ⊤
string≅⊤ .fun = ⊤-intro
string≅⊤ .inv = ⊤→string
string≅⊤ .sec = unambiguous⊤ _ _
string≅⊤ .ret = unambiguous-string _ _
