{-# OPTIONS --guardedness #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum

module Grammar.Search (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet hiding (nil)
open import Grammar.Maybe Alphabet as Maybe using (Maybe)
open import Term Alphabet

private
  variable
    ℓG ℓH : Level
    g : Grammar ℓG
    h : Grammar ℓH

record Search (g : Grammar ℓG) (w : String) : Type ℓG where
  coinductive
  field
    viewSearch :
      -- done, no more results
      (⊤
      -- here's one more result and there may be more
      ⊕ ((g & Search g)
      -- still searching
      ⊕ Search g)) w

open Search

view : Search g ⊢ ⊤ ⊕ ((g & Search g) ⊕ Search g)
view _ = viewSearch

unfold :
  (h ⊢ ⊤ ⊕ ((g & h) ⊕ h))
  → h ⊢ Search g
unfold f w x .viewSearch with f w x
... | inl _ = inl _
... | inr (inl (g-p , h-p)) = inr (inl (g-p , unfold f _ h-p))
... | inr (inr h-p) = inr (inr (unfold f _ h-p))

nil : ⊤ ⊢ Search g
nil = unfold ⊕-inl

-- cons : (g & Search g) ⊢ Search g
-- cons = {!!}

-- -- left biased search: we exhaustively search the left before
-- -- moving to the right
-- append : Search g & Search g ⊢ Search g
-- append = {!!}

-- -- state := (Search g & Search h) ⊕ Search h
-- ext : g ⊢ Search h
--   → Search g ⊢ Search h
-- ext {h = h} f =
--   unfold (⊕-elim
--     -- we still have some gs left
--     {!!}
--     -- we are just producing hs now
--     (⊕-elim ⊕-inl (⊕-elim {!!} {!!}) ∘g view)
--     -- (⊕-elim ⊕-inl (⊕-inr ∘g {!!}) ∘g view)
--     )
--   ∘g ⊕-inl {h = Search h} ∘g &-intro id (nil {g = h} ∘g ⊤-intro)
