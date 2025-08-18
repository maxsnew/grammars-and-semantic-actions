open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Foundations.Structure
import Cubical.Data.Equality as Eq

module Grammar.RegularExpression.Derivative (Alphabet : hSet ℓ-zero) (_≡?_ : ∀ (x y : ⟨ Alphabet ⟩) → Dec (x Eq.≡ y))
  where

open import Cubical.Data.Sum

open import Grammar Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet as GSum
open import Term Alphabet

decNullable : (r : RegularExpression) → (ε ⊢ ⟦ r ⟧r) ⊎ (⟦ r ⟧r ⊢ char + )
decNullable εr = _⊎_.inl id
decNullable ⊥r = _⊎_.inr ⊥-elim
decNullable ＂ c ＂r = _⊎_.inr (literal→char c ,⊗ NIL ∘g ⊗-unit-r⁻)
decNullable (r ⊗r r') with decNullable r | decNullable r'
... | _⊎_.inl nullr | _⊎_.inl nullr' = _⊎_.inl (nullr ,⊗ nullr' ∘g ⊗-unit-l⁻)
... | _⊎_.inl _ | _⊎_.inr ¬nullr' = _⊎_.inr (char+⊗r→char+ ∘g id ,⊗ ¬nullr')
... | _⊎_.inr ¬nullr | _ = _⊎_.inr
  (char+⊗l→char+ ∘g ¬nullr ,⊗ id)
decNullable (r ⊕r r') with decNullable r | decNullable r'
... | _⊎_.inl nullr | _ = _⊎_.inl (GSum.inl ∘g nullr)
... | _ | _⊎_.inl nullr' = _⊎_.inl (GSum.inr ∘g nullr')
... | _⊎_.inr ¬nullr | _⊎_.inr ¬nullr' = _⊎_.inr (GSum.⊕-elim ¬nullr ¬nullr')
decNullable (r *r) = _⊎_.inl NIL

data NullableR : RegularExpression → Type ℓ-zero where
  εrN : NullableR εr
  ⊕rN : ∀ {r r'} → NullableR r ⊎ NullableR r' → NullableR (r ⊕r r')
  ⊗rN : ∀ {r r'} → NullableR r → NullableR r' → NullableR (r ⊗r r')
  ⋆rN : ∀ r → NullableR (r *r)


nullableSound : ∀ {r} → NullableR r → ε ⊢ ⟦ r ⟧r
nullableSound εrN = id
nullableSound (⊕rN (_⊎_.inl rN)) = GSum.inl ∘g nullableSound rN
nullableSound (⊕rN (_⊎_.inr rN')) = GSum.inr ∘g nullableSound rN'
nullableSound (⊗rN rN rN') = nullableSound rN ,⊗ nullableSound rN' ∘g ⊗-unit-l⁻
nullableSound (⋆rN r) = NIL

δr : RegularExpression → ⟨ Alphabet ⟩ → RegularExpression
δr εr c = ⊥r
δr ⊥r c = ⊥r
δr (r ⊕r r') c = δr r c ⊕r δr r' c
δr ＂ d ＂r c with d ≡? c
... | yes p = εr
... | no ¬p = ⊥r
δr (r ⊗r r') c with decNullable r
... | _⊎_.inl x = δr r c ⊗r r' ⊕r δr r' c
... | _⊎_.inr x = δr r c ⊗r r'
δr (r *r) c = δr r c ⊗r r *r

δr-sound : ∀ r c → ⟦ δr r c ⟧r ⊢ ⟦ r ⟧r ⟜ literal c
δr-sound εr c = ⊥-elim
δr-sound ⊥r c = ⊥-elim
δr-sound ＂ d ＂r c with d ≡? c
... | yes Eq.refl = ⟜-intro ⊗-unit-r
... | no ¬p = ⊥-elim
δr-sound (r ⊗r r') c with decNullable r
... | _⊎_.inl nullr = GSum.⊕-elim
  (⟜-intro ((⟜-app ∘g id ,⊗ δr-sound r _) ,⊗ id ∘g ⊗-assoc))
  (⟜-intro (nullr ,⊗ id ∘g ⊗-unit-l⁻ ∘g ⟜-app ∘g id ,⊗ δr-sound r' _))
... | _⊎_.inr _ =
  ⟜-intro (id ∘g (⟜-app ∘g id ,⊗ δr-sound r _) ,⊗ id ∘g ⊗-assoc)
δr-sound (r ⊕r r') c = GSum.⊕-elim
  (⟜-intro (GSum.inl ∘g ⟜-app ∘g id ,⊗ δr-sound r _))
  (⟜-intro (GSum.inr ∘g ⟜-app ∘g id ,⊗ δr-sound r' _))
δr-sound (r *r) c = ⟜-intro
  ((CONS ∘g (⟜-app ∘g id ,⊗ δr-sound r _) ,⊗ id) ∘g ⊗-assoc)

-- completeness involves some more properties
