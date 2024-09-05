{- Some presentations of the Dyck grammar of balanced parentheses and hopefully some parsers? -}

module Examples.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List hiding (init)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinSet

data Bracket : Type where
  [ ] : Bracket

BracketRep : Bracket ≃ Bool
BracketRep = isoToEquiv (iso
  (λ { [ → true ; ] → false })
  (λ { false → ] ; true → [ })
  (λ { false → refl ; true → refl })
  λ { [ → refl ; ] → refl })

isFinBracket : isFinSet Bracket
isFinBracket = EquivPresIsFinSet (invEquiv BracketRep) isFinSetBool

Alphabet : hSet _
Alphabet = (Bracket , isFinSet→isSet isFinBracket)

open import Grammar Alphabet
open import Grammar.Maybe Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.KleeneStar Alphabet
open import Term Alphabet

private
  variable
    ℓg : Level
    g : Grammar ℓg


Str = KL* ⊕Σ₀

-- TODO : put this some place better
String→KL* : (w : String) → KL* ⊕Σ₀ w
String→KL* [] = nil _ refl
String→KL* (x ∷ w) =
  cons _ ((((x ∷ []) , w) , refl) , ((x , refl) , (String→KL* w)))

consLit : (c : ⟨ Alphabet ⟩) → literal c ⊗ KL* ⊕Σ₀ ⊢ KL* ⊕Σ₀
consLit c _ (split , lit , p) =
  KL*.cons _ (split , (c , lit) , p)

open StrongEquivalence

-- LL(1) Dyck grammar:
-- S → ε
--   | [ S ] S
data Balanced : Grammar ℓ-zero where
  nil : ε-grammar ⊢ Balanced
  balanced : literal [ ⊗ (Balanced ⊗ (literal ] ⊗ Balanced)) ⊢ Balanced

startsWith : Bracket → Grammar ℓ-zero
startsWith c = literal c & Str

data Balanced' : Grammar ℓ-zero where
  nil : ε-grammar ⊢ Balanced'
  balanced :
    startsWith [ &
      (literal [ ⊗ Balanced' ⊗ literal ] ⊗ Balanced')
      ⊢ Balanced'

open *r-Algebra

-- Pattern matching on these characters should be fine,
-- as this is at the boundary of linear and non-linear
-- and we pattern match on a nonlinear variable
unpackLit : (c : Bracket) → ⊕Σ₀ ⊢ Maybe (literal c)
unpackLit [ _ ([ , lit) = just {g = literal [} _ lit
unpackLit ] _ ([ , lit) = nothing {g = literal [}{h = literal ]} _ lit
unpackLit [ _ (] , lit) = nothing {g = literal ]}{h = literal [} _ lit
unpackLit ] _ (] , lit) = just {g = literal ]} _ lit

parseChar : (c : Bracket) → Str ⊢ Maybe (literal c ⊗ Str)
parseChar c =
  caseKL* ⊕Σ₀
    nothing
    (Maybe⊗l ∘g
    ⊗-intro (unpackLit c) (id {g = Str}))

mt : String
mt = []

s : String
s = [ ∷ ] ∷ []

s' : String
s' = [ ∷ ] ∷ ] ∷ ] ∷ [ ∷ []

s'' : String
s'' = ] ∷ ] ∷ ] ∷ [ ∷ []

s''' : String
s''' = [ ∷ [ ∷ ] ∷ ] ∷ [ ∷ ] ∷ []

-- Testing the above function is wacky bc of normalization
-- My hacky test is to check if it is a just or is a nothing, which
-- isn't a 100% proof of correctness but gives a sanity check

is-just : ∀ w → (g : Grammar ℓg) → Maybe g w → Bool
is-just w g p = Sum.rec (λ _ → true) (λ _ → false) p

_ :
  is-just s (literal [ ⊗ Str) (parseChar [ s (String→KL* s))
    ≡
  true
_ = refl

_ :
  is-just s' (literal [ ⊗ Str) (parseChar [ s' (String→KL* s'))
    ≡
  true
_ = refl

_ :
  is-just s'' (literal [ ⊗ Str) (parseChar [ s'' (String→KL* s''))
    ≡
  false
_ = refl

-- TODO need better bind syntax to make this easier to write/understand
{-# TERMINATING #-}
balanced-parser : Str ⊢ Maybe (Balanced ⊗ Str)
balanced-parser =
  -- caseKL* is maybe kinda sus, but is likely admissible. It just cases
  -- on if a Kleene star is a nil or a cons
  caseKL* ⊕Σ₀
    -- if empty
    (just ∘g ⊗-intro Balanced.nil KL*.nil ∘g ⊗-unit-r⁻)
    -- if non-empty
    (bind
      (bind
        (bind
          (bind
            (just ∘g
            -- ⊗-intro balanced id ∘g
            ⊗-intro {g = (((literal [ ⊗ Balanced) ⊗ literal ]) ⊗ Balanced)}
              {h = Balanced}{k = Str}{l = Str}
                (balanced ∘g
                ⊗-assoc⁻ ∘g
                ⊗-assoc⁻) -- align to the associativity of the Balanced constructor
                id ∘g
            ⊗-assoc)
            ∘g
          Maybe⊗r ∘g
          functoriality ((((literal [) ⊗ Balanced) ⊗ literal ]) ⊗r var) balanced-parser ∘g -- literal [ ⊗ Balanced ⊗ literal ] ⊗ Str
          ⊗-assoc)
          ∘g
        Maybe⊗r ∘g
        functoriality (((literal [) ⊗ Balanced) ⊗r var) (parseChar ]) ∘g
        ⊗-assoc) -- literal [ ⊗ Balanced ⊗ Str
        ∘g
      Maybe⊗r ∘g
      functoriality (literal [ ⊗r var) balanced-parser) -- literal [ ⊗ Str
      ∘g
    parseChar [ ∘g
    cons) -- this cons forgets that we were non empty by putting the string
          -- back together
          -- it can likely be refactored away

is-ε : Str ⊢ Maybe ε-grammar
is-ε = caseKL* ⊕Σ₀ just nothing

_ :
  is-just mt ε-grammar (is-ε mt (String→KL* mt))
    ≡
  true
_ = refl

_ :
  is-just s ε-grammar (is-ε s (String→KL* s))
    ≡
  false
_ = refl

balanced-parser' : Str ⊢ Maybe Balanced
balanced-parser' =
  bind (bind (just ∘g ⊗-unit-r) ∘g
       Maybe⊗r ∘g
       functoriality (Balanced ⊗r var) is-ε) ∘g
  balanced-parser

_ :
  is-just mt Balanced (balanced-parser' mt (String→KL* mt))
    ≡
  true
_ = refl

-- TODO : Some of these tests are failing
_ :
  is-just s Balanced (balanced-parser' s (String→KL* s))
    ≡
  false -- should be true
_ = refl

_ :
  is-just s' Balanced (balanced-parser' s' (String→KL* s'))
    ≡
  false
_ = refl

_ :
  is-just s'' Balanced (balanced-parser' s'' (String→KL* s''))
    ≡
  false
_ = refl

_ :
  is-just s''' Balanced (balanced-parser' s''' (String→KL* s'''))
    ≡
  false -- should be true
_ = refl
