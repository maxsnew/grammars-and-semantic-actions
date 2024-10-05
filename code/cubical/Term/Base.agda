open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Term.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

{-- Embed the linear typing rules
 -- These correspond to terms like x : g ⊢ M : g'
 -- with the caveat that derivations
 -- x : g , y : h ⊢ M : g'
 -- are represented as
 -- x : g ⊗ h ⊢ M : g'
 --
 -- Likewise, we represent the empty context with the empty grammar
 -- ∙ ⊢ M : g
 -- is given as
 -- x : ε-grammar ⊢ M : g
 --}
module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  where
  Term : Type (ℓ-max ℓg ℓh)
  Term = ∀ w → g w → h w

  infix 1 Term
  syntax Term g g' = g ⊢ g'

id : g ⊢ g
id _ x = x

seq :
  g ⊢ h →
  h ⊢ k →
  g ⊢ k
seq e e' _ p = e' _ (e _ p)
-- e' (e p)

_∘g_ :
  h ⊢ k →
  g ⊢ h →
  g ⊢ k
_∘g_ e e' = seq e' e

infixr 9 _∘g_
syntax seq e e' = e ⋆ e'

isMono :
  g ⊢ h → Typeω
isMono {g = g}{h = h} f =
  ∀ {ℓk}{k : Grammar ℓk} (e e' : k ⊢ g) →
    f ∘g e ≡ f ∘g e' → e ≡ e'

Mono∘g : (e : g ⊢ h) (e' : h ⊢ k) →
  isMono e' → isMono e → isMono (e' ∘g e)
Mono∘g e e' mon-e mon-e' f f' e'ef≡e'ef' =
  mon-e' f f' (mon-e (e ∘g f) (e ∘g f') e'ef≡e'ef')
