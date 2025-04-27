{-# OPTIONS --erased-cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term.Base (Alphabet : Type ℓ-zero) (@0 isSetAlphabet : isSet Alphabet) where

open import Cubical.Functions.Embedding

open import Grammar.Base Alphabet isSetAlphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

{-- Embed the linear typing rules
 -- These correspond to terms like x : A ⊢ M : B
 -- with the caveat that derivations
 -- x : A , y : B ⊢ M : C
 -- are represented as
 -- x : A ⊗ B ⊢ M : C
 --
 -- Likewise, we represent the empty context with the empty grammar
 -- ∙ ⊢ M : A
 -- is given as
 -- x : ε ⊢ M : A
 --
 -- Note, a derivation A ⊢ B is equivalent to
 -- a non-linear term of type ↑ (A ⊸ B)
 --
 -- where ↑ encodes the parses of a grammar in the empty context
 -- - ↑ A ≅ (ε ⊢ A)
 --
 -- and ⊸ is a linear function type
 --}
module _
  (A : Grammar ℓA)
  (B : Grammar ℓB)
  where
  Term : Type (ℓ-max ℓA ℓB)
  Term = ∀ w → A w → B w

  infix 1 Term
  syntax Term A g' = A ⊢ g'

id : A ⊢ A
id _ x = x

seq :
  A ⊢ B →
  B ⊢ C →
  A ⊢ C
seq e e' _ p = e' _ (e _ p)

_∘g_ :
  B ⊢ C →
  A ⊢ B →
  A ⊢ C
_∘g_ e e' = seq e' e

infixr 9 _∘g_
syntax seq e e' = e ⋆ e'

record Inverse
  {A : Grammar ℓA}
  {B : Grammar ℓB}
  (e : A ⊢ B) : Type (ℓ-max ℓA ℓB) where
  field
    inv : B ⊢ A
    is-left-inv : inv ∘g e ≡ id
    is-right-inv : e ∘g inv ≡ id

isMono :
  A ⊢ B → Typeω
isMono {A = A}{B = B} f =
  ∀ {ℓC}{C : Grammar ℓC} (e e' : C ⊢ A) →
    f ∘g e ≡ f ∘g e' → e ≡ e'

Mono∘g : (e : A ⊢ B) (e' : B ⊢ C) →
  isMono e' → isMono e → isMono (e' ∘g e)
Mono∘g e e' mon-e mon-e' f f' e'ef≡e'ef' =
  mon-e' f f' (mon-e (e ∘g f) (e ∘g f') e'ef≡e'ef')

@0 invMoveR :
  {f : A ⊢ B} {f⁻ : B ⊢ A}
  {f' : C ⊢ A} {f'' : C ⊢ B}
  → f⁻ ∘g f ≡ id
  → f ∘g f' ≡ f''
  → f' ≡ f⁻ ∘g f''
invMoveR {f = f}{f⁻}{f'}{f''} retr p =
  f' ≡⟨ cong (_∘g f') (sym retr) ⟩
  f⁻ ∘g f ∘g f' ≡⟨ cong (f⁻ ∘g_) p ⟩
  f⁻ ∘g f'' ∎
