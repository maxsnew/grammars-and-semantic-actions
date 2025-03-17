{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Benchmark.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod

open import Cubical.Data.List
open import Cubical.Data.Bool using (true ; false)

open import Examples.Dyck
  hiding (LP ; RP)
  renaming ([ to LP ; ] to RP)

open import Grammar Alphabet renaming (NIL to *NIL)
open import Parser Alphabet

open Parser DyckParser

iterChar : ⟨ Alphabet ⟩ → ℕ → String
iterChar c zero = []
iterChar c (suc n) = c ∷ (iterChar c n)

{-# TERMINATING #-}
-- make a big balanced string
mkInput : ℕ → String
mkInput 0 = []
mkInput 1 = LP ∷ RP ∷ []
mkInput (suc (suc n)) with n mod 2
... | 0 = iterChar LP n ++ mkInput (suc n) ++ iterChar RP n
... | 1 = mkInput (suc n) ++ mkInput n
... | (suc (suc m)) = [] -- should never happen
                                     -- becuase n mod 4 < 4

-- It takes up to 25 seconds to generate these strings and
-- verify their lengths
-- _ : length (mkInput 10) ≡ 92
-- _ = refl
-- _ : length (mkInput 20) ≡ 3068
-- _ = refl
-- _ : length (mkInput 25) ≡ 24524
-- _ = refl
-- _ : length (mkInput 27) ≡ 49096
-- _ = refl
-- _ : length (mkInput 29) ≡ 98244
-- _ = refl
-- _ : length (mkInput 31) ≡ 196544
-- _ = refl

opaque
  unfolding run ⊕-elim inr mkstring ⊗-intro ⊸-intro ⟜-intro ⌈w⌉→string ⊕ᴰ-distL ⊕ᴰ-distR
  -- Uncomment these individually to run
  --
  -- Each benchmark below is run with the length checks above
  -- commented out. Those are only there to sanity check size

  -- immediate
  _ : accept? (mkInput 10) ≡ true
  _ = refl

  -- 10s
  -- _ : accept? (mkInput 25) ≡ true
  -- _ = refl

  -- 10s
  -- _ : accept? (mkInput 25 ++ [ RP ]) ≡ false
  -- _ = refl

  -- In principle, this one could be faster but
  -- the structure of the current code iterates
  -- through all of the input, even after going
  -- to a fail state
  -- 10s
  -- _ : accept? ([ RP ] ++ mkInput 25) ≡ false
  -- _ = refl

  -- 20s
  -- _ : accept? (mkInput 27) ≡ true
  -- _ = refl

  -- 20s
  -- _ : accept? ([ RP ] ++ mkInput 27) ≡ false
  -- _ = refl

  -- 35s
  -- _ : accept? (mkInput 29) ≡ true
  -- _ = refl

  -- 1m3s seconds
  -- _ : accept? (mkInput 31) ≡ true
  -- _ = refl
