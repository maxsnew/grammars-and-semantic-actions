open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.String.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.List.More
open import Cubical.Data.Sigma
import Cubical.Data.Sum as Sum
open import Cubical.Data.Nat
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥* ; rec)

open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Grammar.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.Properties Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Epsilon.Base Alphabet
open import Grammar.Equalizer.Base Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.LinearFunction.Base Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Distributivity Alphabet

open import Grammar.String.Base Alphabet
open import Grammar.String.Terminal Alphabet public
open import Grammar.String.Unambiguous Alphabet public

open import Term.Base Alphabet

private
  variable
    w : String
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence
open WeakEquivalence
open _isRetractOf_

unrolled-string : Grammar ℓ-zero
unrolled-string = ε ⊕ char ⊗ string

unrolled-string2 : Grammar ℓ-zero
unrolled-string2 = ε ⊕ char ⊕ (char ⊗ char +)

unrolled-string' : Grammar ℓ-zero
unrolled-string' = ε ⊕ (string ⊗ char)

unrolled-stringL : Grammar ℓ-zero
unrolled-stringL = ε ⊕ (stringL ⊗ char)

unroll-string≅ : string ≅ unrolled-string
unroll-string≅ = *≅ε⊕A⊗A* char

unroll-string2Retract : (char ⊕ ((char ⊗ char) ⊗ string)) isRetractOf (char ⊗ string)
unroll-string2Retract .weak .fun =
   ⊕-elim (id ,⊗ NIL ∘g ⊗-unit-r⁻) (id ,⊗ CONS ∘g ⊗-assoc⁻)
unroll-string2Retract .weak .inv =
  ⟜-intro⁻ (fold*r char
    (⟜-intro (inl ∘g ⊗-unit-r))
    (⟜-intro (inr ∘g id ,⊗ string-intro ∘g ⊗-assoc)))
unroll-string2Retract .ret = {!!} -- the-ret
  -- where
  -- opaque
  --   unfolding ⊕-elim ⊗-intro ⊗-assoc⁻
  --   @0 the-ret : unroll-string2Retract .weak .inv ∘g unroll-string2Retract .weak .fun ≡ id
  --   the-ret =
  --     ⊕≡ _ _
  --     (cong (_∘g ⊗-unit-r⁻) (⟜-β (inl ∘g ⊗-unit-r))
  --     ∙ cong (inl ∘g_) (⊗-unit-r⁻r))
  --     (equalizer-ind-⊗r (λ _ → *Tag char) _ _ _ _ _
  --       (λ _ → λ @0 where
  --         nil →
  --           (cong (_∘g (⊗-assoc⁻ ∘g id ,⊗ (⟜-intro (inl ∘g ⊗-unit-r) ∘g lowerG ∘g lowerG)))
  --                   (⟜-β (inr ∘g id ,⊗ string-intro ∘g ⊗-assoc)))
  --           ∙ (cong (λ z →
  --                   inr {B = char} ∘g id ,⊗ string-intro ∘g z
  --                   ∘g id ,⊗ (⟜-intro {A = char}(inl {B = (char ⊗ char) ⊗ string} ∘g ⊗-unit-r) ∘g lowerG ∘g lowerG))
  --                   ⊗-assoc∘⊗-assoc⁻≡id)
  --           ∙ (cong (λ z → inr {B = char} ∘g ⊗-intro {A = (char ⊗ char)} id z) (unambiguous-string _ _))
  --         cons →
  --           (cong (_∘g (⊗-assoc⁻ ∘g id ,⊗ fold*r char (⟜-intro (inl ∘g ⊗-unit-r))
  --                                                     (⟜-intro (inr ∘g id ,⊗ string-intro ∘g ⊗-assoc))
  --                       ∘g id ,⊗ CONS
  --                       ∘g id ,⊗ id ,⊗ eq-π _ _ ∘g id ,⊗ lowerG ,⊗ lowerG))
  --                   (⟜-β (inr ∘g id ,⊗ string-intro ∘g ⊗-assoc)))
  --           ∙ (cong (λ z → inr {B = char} ∘g id ,⊗ string-intro ∘g z
  --                          ∘g id ,⊗ fold*r char (⟜-intro {A = char}(inl ∘g ⊗-unit-r))
  --                                               (⟜-intro (inr ∘g id ,⊗ string-intro ∘g ⊗-assoc))
  --                          ∘g id ,⊗ CONS
  --                          ∘g id ,⊗ id ,⊗ eq-π {B = char ⊕ (char ⊗ char) ⊗ string ⟜ char ⊗ char}
  --                                           (⟜-intro (unroll-string2Retract .weak .inv ∘g unroll-string2Retract .weak .fun ∘g inr))
  --                                           (⟜-intro inr)
  --                          ∘g id ,⊗ lowerG ,⊗ lowerG)
  --                   (⊗-assoc∘⊗-assoc⁻≡id)
  --             )
  --           ∙ λ i → inr ∘g id ,⊗ unambiguous-string
  --                                (string-intro
  --                                ∘g fold*r char (⟜-intro {A = char}(inl ∘g ⊗-unit-r))
  --                                               (⟜-intro (inr ∘g id ,⊗ string-intro ∘g ⊗-assoc))
  --                                ∘g CONS ∘g id ,⊗ eq-π _ _
  --                                ∘g lowerG ,⊗ lowerG
  --                                )
  --                                ((CONS ∘g id ,⊗ eq-π _ _) ∘g lowerG ,⊗ lowerG)
  --                                i
  --       )
  --       _
  --     )

@0 unambiguous-char⊕char⊗char+' : unambiguous (char ⊕ ((char ⊗ char) ⊗ string))
unambiguous-char⊕char⊗char+' =
  isUnambiguousRetract unroll-string2Retract
    (summand-R-is-unambig (unambiguous≅ unroll-string≅ unambiguous-string))

@0 unambiguous-char⊕char⊗char+ : unambiguous (char ⊕ (char ⊗ char +))
unambiguous-char⊕char⊗char+ = unambiguous≅ (⊕≅ id≅ (sym≅ ⊗-assoc≅)) unambiguous-char⊕char⊗char+'

@0 unambiguous-char : unambiguous char
unambiguous-char = summand-L-is-unambig unambiguous-char⊕char⊗char+

@0 disjoint-char-char⊗char+ : disjoint char (char ⊗ char +)
disjoint-char-char⊗char+ = unambig-⊕-is-disjoint unambiguous-char⊕char⊗char+

@0 disjoint-ε-char+ : disjoint ε (char +)
disjoint-ε-char+ = unambig-⊕-is-disjoint (unambiguous≅ unroll-string≅ unambiguous-string)

unroll-string≅' : string ≅ unrolled-string'
unroll-string≅' = *≅ε⊕A*⊗A char

string≅unrolled-stringL : string ≅ unrolled-stringL
string≅unrolled-stringL =
  unroll-string≅'
  ≅∙ ⊕≅ id≅ (⊗≅ string≅stringL id≅)

unroll-stringL≅ : stringL ≅ unrolled-stringL
unroll-stringL≅ = sym≅ string≅stringL ≅∙ string≅unrolled-stringL

@0 unambiguous-unrolled-string : unambiguous unrolled-string
unambiguous-unrolled-string =
    unambiguous≅ unroll-string≅ unambiguous-string

@0 unambiguous-unrolled-string' : unambiguous unrolled-string'
unambiguous-unrolled-string' =
    unambiguous≅ unroll-string≅' unambiguous-string

disjoint-ε-char+' : disjoint ε (char +)
disjoint-ε-char+' = unambig-⊕-is-disjoint unambiguous-unrolled-string

disjoint-ε-char+L : disjoint ε (char +L)
disjoint-ε-char+L = unambig-⊕-is-disjoint unambiguous-unrolled-string'

disjoint-ε-char : disjoint ε char
disjoint-ε-char = disjoint-ε-char+' ∘g id ,&p +-singleton char

disjoint-ε-literal : ∀ c → disjoint ε ＂ c ＂
disjoint-ε-literal c = disjoint-ε-char ∘g id ,&p (literal→char c)

@0 unambiguous-char+ : unambiguous (char +)
unambiguous-char+ = summand-R-is-unambig unambiguous-unrolled-string

@0 unambiguous-char+L : unambiguous (char +L)
unambiguous-char+L = summand-R-is-unambig unambiguous-unrolled-string'

&string≅ : A ≅ A & string
&string≅ = &⊤≅ ≅∙ &≅ id≅ (sym≅ string≅⊤)

&string-split≅ : A ≅ (A & ε) ⊕ (A & (char +))
&string-split≅ =
  &string≅
  ≅∙ &≅ id≅ unroll-string≅
  ≅∙ &⊕-distL≅

string⊗l-split : A ⊗ string ⊢ A ⊕ (A ⊗ char +)
string⊗l-split =
  (⊗-unit-r ,⊕p id)
  ∘g ⊗⊕-distL
  ∘g id ,⊗ unroll-string≅ .fun

char+⊗l→char+ : char + ⊗ A ⊢ char +
char+⊗l→char+ =
  id ,⊗ string-intro
  ∘g ⊗-assoc⁻

char+L⊗r→char+L : A ⊗ char +L ⊢ char +L
char+L⊗r→char+L =
  string-intro ,⊗ id
  ∘g ⊗-assoc

char+≈char+L : char + ≈ char +L
char+≈char+L =
  disjoint⊕≈
    (≅→≈ id≅)
    disjoint-ε-char+
    disjoint-ε-char+L
    (≅→≈ (sym≅ unroll-string≅ ≅∙ unroll-string≅'))

-- char+≅char+L : char + ≅ char +L
-- char+≅char+L = ≈→≅ unambiguous-char+ unambiguous-char+L char+≈char+L

-- char+⊗r→char+ : A ⊗ char + ⊢ char +
-- char+⊗r→char+ =
--   char+≅char+L .inv
--   ∘g char+L⊗r→char+L
--   ∘g id ,⊗ char+≅char+L .fun

-- module _ {c : ⟨ Alphabet ⟩}
--   where
--   startsWith→char+ : startsWith c ⊢ char +
--   startsWith→char+ = literal→char c ,⊗ id
