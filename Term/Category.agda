{- Monoidal Category of SetGrammars and Terms for a fixed hLevel -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term.Category (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet as LP
open import Term.Base Alphabet as Term

module _ (ℓ : Level) where
  open MonoidalCategory
  open TensorStr
  open MonoidalStr
  open Category
  open Functor
  open NatTrans
  open NatIso
  open isIso
  |GRAMMAR| : Category (ℓ-suc ℓ) ℓ
  |GRAMMAR| .ob = SetGrammar ℓ
  |GRAMMAR| .Hom[_,_] A B = Term ⟨ A ⟩ ⟨ B ⟩
  |GRAMMAR| .Category.id = Term.id
  |GRAMMAR| ._⋆_ = Term.seq
  |GRAMMAR| .⋆IdL _ = refl
  |GRAMMAR| .⋆IdR _ = refl
  |GRAMMAR| .⋆Assoc _ _ _ = refl
  |GRAMMAR| .isSetHom {y = B} = isSetΠ (λ w → isSet→ (B .snd w))

  GRAMMAR : MonoidalCategory (ℓ-suc ℓ) ℓ
  GRAMMAR .C = |GRAMMAR|
  GRAMMAR .monstr .tenstr .unit = ε* , isSetGrammarε*
  GRAMMAR .monstr .tenstr .─⊗─ .F-ob (A , B) =
    ⟨ A ⟩ LP.⊗ ⟨ B ⟩ , isSetGrammar⊗ (A .snd) (B .snd)
  GRAMMAR .monstr .tenstr .─⊗─ .F-hom (f , g) = f ,⊗ g
  GRAMMAR .monstr .tenstr .─⊗─ .F-id = id,⊗id≡id
  GRAMMAR .monstr .tenstr .─⊗─ .F-seq _ _ = sym ⊗-intro⊗-intro
  GRAMMAR .monstr .α .trans .N-ob ABC = ⊗-assoc
  GRAMMAR .monstr .α .trans .N-hom fgh = ⊗-assoc⊗-intro
  GRAMMAR .monstr .α .nIso ABC .inv = ⊗-assoc⁻
  GRAMMAR .monstr .α .nIso ABC .sec = ⊗-assoc∘⊗-assoc⁻≡id
  GRAMMAR .monstr .α .nIso ABC .ret = ⊗-assoc⁻∘⊗-assoc≡id
  GRAMMAR .monstr .η .trans .N-ob A = ⊗-unit*-l
  GRAMMAR .monstr .η .trans .N-hom f = sym (⊗-unit*-l⊗-intro f)
  GRAMMAR .monstr .η .nIso A .inv = ⊗-unit*-l⁻
  GRAMMAR .monstr .η .nIso A .sec = ⊗-unit*-l⁻l
  GRAMMAR .monstr .η .nIso A .ret = ⊗-unit*-ll⁻
  GRAMMAR .monstr .ρ .trans .N-ob A = ⊗-unit*-r
  GRAMMAR .monstr .ρ .trans .N-hom f = ⊗-unit*-r⊗-intro f
  GRAMMAR .monstr .ρ .nIso A .inv = ⊗-unit*-r⁻
  GRAMMAR .monstr .ρ .nIso A .sec = ⊗-unit*-r⁻r
  GRAMMAR .monstr .ρ .nIso A .ret = ⊗-unit*-rr⁻
  GRAMMAR .monstr .pentagon A B C D = ⊗-pentagon
  GRAMMAR .monstr .triangle A B = ⊗-triangle
