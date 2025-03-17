{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Section2.Figure5 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet
open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq

open import Examples.Section2.Alphabet
open import Grammar Alphabet
open import Automata.NFA.Base Alphabet
open import Term Alphabet


open NFA

-- 3 states
State : Type
State = Fin 3

pattern s0 = fzero
pattern s1 = fsuc fzero
pattern s2 = fsuc (fsuc fzero)

-- Handwritten NFA for (＂ a ＂ * ⊗ b) ⊕ c
-- in the style given in Figure 5
module Handwritten where
  data Tag : (s : State) → Type where
    stop : Tag s2
    1to1 : Tag s1
    1to2 : Tag s1
    0to2 : Tag s0
    0to1 : Tag s0

  -- Defining the type of traces syntactically
  -- by specifying a strictly positive functor on Grammars
  --
  -- Note, by leveraging the equivalence between
  -- ↑ (A ⊸ B) and A ⊢ B,
  -- the constructors are represented below without
  -- explicit mention to ⊸
  TraceTy : State → Functor State
  TraceTy s0 = ⊕e (Tag s0) λ where
    -- 0to2 : ↑ (＂ c ＂ ⊸ Trace s2 ⊸ Trace s0)
    0to2 → k ＂ c ＂ ⊗e Var s2
    -- 0to1 : ↑ (Trace s1 ⊸ s0)
    0to1 → Var s1
  TraceTy s1 = ⊕e (Tag s1) λ where
    -- 1to1 : ↑ (＂ a ＂ ⊸ Trace s1 ⊸ Trace s1)
    1to1 → k ＂ a ＂ ⊗e Var s1
    -- 1to2 : ↑ (＂ b ＂ ⊸ Trace s2 ⊸ Trace s1)
    1to2 → k ＂ b ＂ ⊗e Var s2
  TraceTy s2 = ⊕e (Tag s2) λ where
    -- stop : ↑ (Trace s2)
    stop → k ε

  -- The type of traces is the least fixed point
  -- for the above functor
  Trace : State → Grammar ℓ-zero
  Trace = μ TraceTy

  -- Application of each of the constructors
  -- NOTE: the lifts here are artefacts of the
  -- way that we define Functor
  0TO2 : ＂ c ＂ ⊗ Trace s2 ⊢ Trace s0
  0TO2 = roll ∘g σ 0to2 ∘g liftG ,⊗ liftG

  0TO1 : Trace s1 ⊢ Trace s0
  0TO1 = roll ∘g σ 0to1 ∘g liftG

  1TO1 : ＂ a ＂ ⊗ Trace s1 ⊢ Trace s1
  1TO1 = roll ∘g σ 1to1 ∘g liftG ,⊗ liftG

  1TO2 : ＂ b ＂ ⊗ Trace s2 ⊢ Trace s1
  1TO2 = roll ∘g σ 1to2 ∘g liftG ,⊗ liftG

  STOP : ε ⊢ Trace s2
  STOP = roll ∘g σ stop ∘g liftG

  -- The function given in Figure 5
  -- Renamed to avoid a clash with the primitive k
  -- we use when declaring inductive types via
  -- functors, as above
  k' : ＂ a ＂ ⊗ ＂ b ＂ ⊢ Trace s0
  k' =
    0TO1 -- turn Trace 1 into Trace 0
         -- i.e. s0 ---[ ε ]---> s1
    ∘g 1TO1 -- turn ＂ a ＂ ⊗ Trace s1 into Trace s1
            -- i.e. s1 ---[ a ]---> s1
    ∘g id ,⊗ 1TO2 -- turn the ＂ b ＂ ⊗ Trace s2 into Trace s1
                  -- i.e. s1 ---[ b ]---> s2
    ∘g ⊗-assoc⁻ -- Reassociate (＂ a ＂ ⊗ ＂ b ＂) ⊗ Trace s2 to
                --             ＂ a ＂ ⊗ (＂ b ＂ ⊗ Trace s2)
    ∘g id ,⊗ STOP -- parse that ε as Trace s2
                  -- i.e. accept at s2
    ∘g ⊗-unit-r⁻ -- insert an ε on the right

-- We also built a library ranging over all NFA specifications
-- We can equivalently reason about the traces of the
-- automaton defined using the library found in NFA.Base
module UsingLibrary where

  -- Identify the labelled transitions with Fin 3
  pattern 0to2 = fzero
  pattern 1to1 = fsuc fzero
  pattern 1to2 = fsuc (fsuc fzero)

  -- Identify the ε transitions with Fin 1
  pattern 0to1 = fzero

  the-nfa : NFA ℓ-zero
  the-nfa .Q = State , isFinSetFin
  the-nfa .init = s0
  the-nfa .isAcc s0 = false
  the-nfa .isAcc s1 = false
  the-nfa .isAcc s2 = true
  the-nfa .transition = Fin 3 , isFinSetFin -- 3 labelled transitions
  the-nfa .src 0to2 = s0
  the-nfa .dst 0to2 = s2
  the-nfa .label 0to2 = c 
  the-nfa .src 1to1 = s1
  the-nfa .dst 1to1 = s1
  the-nfa .label 1to1 = a
  the-nfa .src 1to2 = s1
  the-nfa .dst 1to2 = s2
  the-nfa .label 1to2 = b
  the-nfa .ε-transition = Fin 1 , isFinSetFin -- only a single ε transition
  the-nfa .ε-src 0to1 = s0
  the-nfa .ε-dst 0to1 = s1

  open Accepting the-nfa

  k' : ＂ a ＂ ⊗ ＂ b ＂ ⊢ Trace s0
  k' =
    STEPε 0to1 -- turn Trace 1 into Trace 0
               -- i.e. s0 ---[ ε ]---> s1
    ∘g STEP 1to1 -- turn ＂ a ＂ ⊗ Trace s1 into Trace s1
                 -- i.e. s1 ---[ a ]---> s1
    ∘g id ,⊗ STEP 1to2 -- turn the ＂ b ＂ ⊗ Trace s2 into Trace s1
                       -- i.e. s1 ---[ b ]---> s2
    ∘g ⊗-assoc⁻ -- Reassociate (＂ a ＂ ⊗ ＂ b ＂) ⊗ Trace s2 to
                --             ＂ a ＂ ⊗ (＂ b ＂ ⊗ Trace s2)
    ∘g id ,⊗ STOP {q = s2} Eq.refl -- parse that ε as Trace s2
                                   -- i.e. accept at s2
    ∘g ⊗-unit-r⁻ -- insert an ε on the right

-- We can further show that the two presentations of traces
-- are equivalent
module Equivalence where
  ULNFA : NFA ℓ-zero
  ULNFA = UsingLibrary.the-nfa

  module UL = Accepting ULNFA

  HTrace ULTrace : State → Grammar ℓ-zero
  HTrace = Handwritten.Trace
  ULTrace = UL.Trace

  -- Build an algebra structure that interprets HTrace inside of ULTrace
  H→ULAlg : Algebra Handwritten.TraceTy ULTrace
  H→ULAlg s0 = ⊕ᴰ-elim λ where
    Handwritten.0to2 → UL.STEP UsingLibrary.0to2 ∘g lowerG ,⊗ lowerG
    Handwritten.0to1 → UL.STEPε UsingLibrary.0to1 ∘g lowerG
  H→ULAlg s1 = ⊕ᴰ-elim λ where
    Handwritten.1to1 → UL.STEP UsingLibrary.1to1 ∘g lowerG ,⊗ lowerG
    Handwritten.1to2 → UL.STEP UsingLibrary.1to2 ∘g lowerG ,⊗ lowerG
  H→ULAlg s2 = ⊕ᴰ-elim λ where
    Handwritten.stop → UL.STOP Eq.refl ∘g lowerG

  -- Recurse over an HTrace according to the above
  -- algebra structure to build a ULTrace
  H→UL : ∀ s → HTrace s ⊢ ULTrace s
  H→UL = rec _ H→ULAlg

  -- Build an algebra structure that interprets ULTrace inside of HTrace
  UL→HAlg : Algebra UL.TraceTy HTrace
  UL→HAlg s0 = ⊕ᴰ-elim λ where
    (UL.step UsingLibrary.0to2 Eq.refl) → Handwritten.0TO2 ∘g (lowerG ∘g lowerG) ,⊗ lowerG
    (UL.step UsingLibrary.1to1 ()) -- absurd because src(1to1) ≢ 0
    (UL.step UsingLibrary.1to2 ()) -- absurd because src(1to2) ≢ 0
    (UL.stepε UsingLibrary.0to1 Eq.refl) → Handwritten.0TO1 ∘g lowerG
  UL→HAlg s1 = ⊕ᴰ-elim λ where
    (UL.step UsingLibrary.0to2 ())
    (UL.step UsingLibrary.1to1 Eq.refl) → Handwritten.1TO1 ∘g (lowerG ∘g lowerG) ,⊗ lowerG
    (UL.step UsingLibrary.1to2 Eq.refl) → Handwritten.1TO2 ∘g (lowerG ∘g lowerG) ,⊗ lowerG
    (UL.stepε UsingLibrary.0to1 ())
  UL→HAlg s2 = ⊕ᴰ-elim λ where
    (UL.stop Eq.refl) → Handwritten.STOP ∘g lowerG ∘g lowerG
    (UL.step UsingLibrary.0to2 ())
    (UL.step UsingLibrary.1to1 ())
    (UL.step UsingLibrary.1to2 ())
    (UL.stepε UsingLibrary.0to1 ())

  -- Recurse over a ULTrace according to the above
  -- algebra structure to build an HTrace
  UL→H : ∀ s → ULTrace s ⊢ HTrace s
  UL→H = rec _ UL→HAlg

  open StrongEquivalence

  opaque
    unfolding ⊗-intro
    -- Strong equivalence between HTrace and ULTrace
    HTrace≅ULTrace : ∀ s → HTrace s ≅ ULTrace s
    HTrace≅ULTrace s .fun = H→UL s
    HTrace≅ULTrace s .inv = UL→H s
    HTrace≅ULTrace s .sec =
      -- Inductively prove that H→UL s ∘g UL→H s ≡ id
      --
      -- Here we use our equalizer types, and in particular
      -- the function "equalizer-ind".
      --
      -- The type equalizer (H→UL s ∘g UL→H s) id
      -- is defined in Grammar.Equalizer.Base
      --
      --        equalizer (H→UL s ∘g UL→H s) id
      --                      |
      --                      | eq-π
      --                      ↓
      --                   ULTrace
      --                    |   |
      --   H→UL s ∘g UL→H s |   | id
      --                    ↓   ↓
      --                   ULTrace
      --
      -- It may be thought of as the subset of ULTrace that
      -- are equal when acted upon by (H→UL s ∘g UL→H s) and id
      --
      -- equalizer-ind builds the structure of a
      -- ULTrace-algebra for equalizer (H→UL s ∘g UL→H s) id
      -- which enables a map
      --              ϕ
      --    ULTrace ----> equalizer (H→UL s ∘g UL→H s) id
      --
      -- By defintion of the equalizer, there is also a map
      --                                     eq-π
      --    equalizer (H→UL s ∘g UL→H s) id ------> ULTrace
      --
      -- eq-π and ϕ are each ULTrace-algebra homomorphisms.
      -- Because ULTrace is the *initial* ULTrace-algebra,
      -- eq-π ∘ ϕ ≡ id.
      --
      -- By building a section of the equalizer in this manner,
      -- we have shown that *all* inhabitants of ULTrace
      -- agree when acted upon by (H→UL s ∘g UL→H s) and id
      -- That is, we have shown H→UL s ∘g UL→H s ≡ id
      equalizer-ind UL.TraceTy
        ULTrace
        (λ s → H→UL s ∘g UL→H s)
        (λ _ → id)
        (λ where
          s0 → ⊕ᴰ≡ _ _ λ where
            (UL.step UsingLibrary.0to2 Eq.refl) → λ i →
              UL.STEP UsingLibrary.0to2
              ∘g id ,⊗ eq-π-pf _ _ i
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            (UL.step UsingLibrary.1to1 ())
            (UL.step UsingLibrary.1to2 ())
            (UL.stepε UsingLibrary.0to1 Eq.refl) → λ i →
              UL.STEPε UsingLibrary.0to1
              ∘g eq-π-pf _ _ i
              ∘g lowerG
          s1 → ⊕ᴰ≡ _ _ λ where
            (UL.step UsingLibrary.0to2 ())
            (UL.step UsingLibrary.1to1 Eq.refl) → λ i →
              UL.STEP UsingLibrary.1to1
              ∘g id ,⊗ eq-π-pf _ _ i
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            (UL.step UsingLibrary.1to2 Eq.refl) → λ i →
              UL.STEP UsingLibrary.1to2
              ∘g id ,⊗ eq-π-pf _ _ i
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            (UL.stepε UsingLibrary.0to1 ())
          s2 → ⊕ᴰ≡ _ _ λ where
            (UL.stop Eq.refl) → refl
            (UL.step UsingLibrary.0to2 ())
            (UL.step UsingLibrary.1to1 ())
            (UL.step UsingLibrary.1to2 ())
            (UL.stepε UsingLibrary.0to1 ())
        )
        s
    HTrace≅ULTrace s .ret =
      -- We induct over HTraces now, using the same strategy
      -- as above, to prove that (UL→H s ∘g H→UL s) ≡ id
      equalizer-ind Handwritten.TraceTy
        HTrace
        (λ s → UL→H s ∘g H→UL s)
        (λ _ → id)
        (λ where
          s0 → ⊕ᴰ≡ _ _ λ where
            Handwritten.0to2 → λ i →
              Handwritten.0TO2
              ∘g id ,⊗ eq-π-pf _ _ i
              ∘g lowerG ,⊗ lowerG
            Handwritten.0to1 → λ i →
              Handwritten.0TO1
              ∘g eq-π-pf _ _ i
              ∘g lowerG
          s1 → ⊕ᴰ≡ _ _ λ where
            Handwritten.1to1 → λ i →
              Handwritten.1TO1
              ∘g id ,⊗ eq-π-pf _ _ i
              ∘g lowerG ,⊗ lowerG
            Handwritten.1to2 → λ i →
              Handwritten.1TO2
              ∘g id ,⊗ eq-π-pf _ _ i
              ∘g lowerG ,⊗ lowerG
          s2 → ⊕ᴰ≡ _ _ λ where
            Handwritten.stop → refl
        )
        s
