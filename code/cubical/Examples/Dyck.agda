{- Some presentations of the Dyck grammar of balanced parentheses and hopefully some parsers? -}

module Examples.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_ ;_or_)
open import Cubical.Data.Nat as Nat
open import Cubical.Data.List hiding (init)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinSet

private
  variable
    ℓg : Level

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
open import String.More Alphabet
open import Parser Alphabet isFinBracket

-- a simple, but ambiguous grammar for balanced parentheses
data Dyck : Grammar ℓ-zero where
  none : ε-grammar ⊢ Dyck
  sequence  : Dyck ⊗ Dyck ⊢ Dyck
  bracketed : literal [ ⊗ Dyck ⊗ literal ] ⊢ Dyck

-- LL(1) Dyck grammar:
-- S → ε
--   | [ S ] S
data Balanced : Grammar ℓ-zero where
  nil : ε-grammar ⊢ Balanced
  balanced : literal [ ⊗ (Balanced ⊗ (literal ] ⊗ Balanced)) ⊢ Balanced

mt : String
mt = []

a : String
a = [ ∷ ] ∷ []

a' : String
a' = ] ∷ [ ∷ []

b : String
b = [ ∷ ] ∷ ] ∷ ] ∷ [ ∷ []

c : String
c = ] ∷ ] ∷ ] ∷ [ ∷ []

d : String
d = [ ∷ [ ∷ ] ∷ ] ∷ [ ∷ ] ∷ []

-- Testing the above function is wacky bc of normalization
-- My hacky test is to check if it is a just or is a nothing, which
-- isn't a 100% proof of correctness but gives a sanity check

is-just : ∀ w → (g : Grammar ℓg) → Maybe g w → Bool
is-just w g p = Sum.rec (λ _ → true) (λ _ → false) p

{-# TERMINATING #-} -- uh...
balanced-parser : Parser Balanced
balanced-parser =
  (fmap (⊗-intro balanced id) ∘g
   (parseChar [ then
   balanced-parser then
   parseChar ] then
   balanced-parser))
  or
  (fmap (⊗-intro Balanced.nil id) ∘g parseε)

_ :
  is-just mt (Balanced ⊗ string-grammar) (balanced-parser mt ⌈ mt ⌉)
    ≡
  true
_ = refl

_ :
  is-just a (Balanced ⊗ string-grammar) (balanced-parser a ⌈ a ⌉)
    ≡
  true
_ = refl

_ :
  is-just a' (Balanced ⊗ string-grammar) (balanced-parser a' ⌈ a' ⌉)
    ≡
  true
_ = refl

is-ε : string-grammar ⊢ Maybe ε-grammar
is-ε = caseKL* char just nothing

-- An intrinsically verified Dyck grammar parser
-- NOTE : This required the addition of a couple things that may be
-- problematic but are likely admissible
-- These are not included in this file, but the code presented here
-- makes use of
-- 1. caseKL*, defined in Grammar.KleeneStar, which cases on if a
--      Kleene star was an nil or a cons. Used in parseChar
-- 2. parseChar, defined in Parser. Which breaks some abstractions
--      to build a primitive character parser, and this is justified
--      when the alphabet is a FinSet
-- 3. ⊤→string, a term ⊤-grammar ⊢ string-grammar. Defined in Parser.
--      Used to define the _or_ parser combinator (also in Parser)
balanced-parser' : string-grammar ⊢ Maybe Balanced
balanced-parser' =
  fmap ⊗-unit-r ∘g
  μ ∘g
  fmap (Maybe⊗r ∘g (⊗-intro id is-ε)) ∘g
  balanced-parser

_ :
  is-just mt Balanced (balanced-parser' mt (⌈ mt ⌉))
    ≡
  true
_ = refl

_ :
  is-just a Balanced (balanced-parser' a (⌈ a ⌉))
    ≡
  true
_ = refl

_ :
  is-just a' Balanced (balanced-parser' a' (⌈ a' ⌉))
    ≡
  false
_ = refl

_ :
  is-just b Balanced (balanced-parser' b (⌈ b ⌉))
    ≡
  false
_ = refl

_ :
  is-just c Balanced (balanced-parser' c (⌈ c ⌉))
    ≡
  false
_ = refl

_ :
  is-just d Balanced (balanced-parser' d (⌈ d ⌉))
    ≡
  true
_ = refl

data BalancedStk : ∀ (n : ℕ) → Grammar ℓ-zero where
  eof : ε-grammar ⊢ BalancedStk zero
  open[ : ∀ {n} → literal [ ⊗ BalancedStk (suc n) ⊢ BalancedStk n
  close] : ∀ {n} → literal ] ⊗ BalancedStk n ⊢ BalancedStk (suc n)

  -- these are the cases for failure
  leftovers : ∀ {n} → ε-grammar ⊢ BalancedStk (suc n)
  unexpected] : literal ] ⊗ ⊤-grammar ⊢ BalancedStk 0

parseStk : string-grammar ⊢ LinΠ[ n ∈ ℕ ] BalancedStk n
parseStk = foldKL*r _ (record
  { the-ℓ = _ ; G = _
  ; nil-case = LinΠ-intro λ { zero
      → eof
    ; (suc n)
      → leftovers
    }
  
  ; cons-case = LinΠ-intro (λ n → ⟜-intro⁻ (LinΣ-elim (λ
      { [ → ⟜-intro {k = BalancedStk _}
        -- encountered an open paren, push onto the stack and continue
        (open[ ∘g ⊗-intro id (LinΠ-app (suc n)))
      ; ] → ⟜-intro {k = BalancedStk _} ((Nat.elim {A = λ n → _ ⊢ BalancedStk n}
      -- the stack is empty but we encountered a close bracket
      (unexpected] ∘g ⊗-intro id ⊤-intro)
      -- the stack is suc n, continue with n
      (λ n _ → close] ∘g ⊗-intro id (LinΠ-app n))
      n))
      })))
  })

-- the n is the number of open parentheses that this datatype closes
data BalancedStkTr : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero where
  eof : ε-grammar ⊢ BalancedStkTr zero true

  open[ : ∀ {n b} → literal [ ⊗ BalancedStkTr (suc n) b ⊢ BalancedStkTr n b
  close] : ∀ {n b} → literal ] ⊗ BalancedStkTr n b ⊢ BalancedStkTr (suc n) b

  leftovers : ∀ {n} → ε-grammar ⊢ BalancedStkTr (suc n) false
  unexpected] : literal ] ⊗ ⊤-grammar ⊢ BalancedStkTr 0 false


parseStkTr : string-grammar ⊢ LinΠ[ n ∈ ℕ ] LinΣ[ b ∈ Bool ] BalancedStkTr n b
parseStkTr = foldKL*r _ (record { the-ℓ = _ ; G = _
  ; nil-case = LinΠ-intro (λ
    { zero → LinΣ-intro true ∘g eof
    ; (suc n) → LinΣ-intro false ∘g leftovers })
  ; cons-case = LinΠ-intro (λ n → ⟜-intro⁻ (LinΣ-elim (λ
    { [ → ⟜-intro {k = Motive n}
        (-⊗-intro⁻ (LinΣ-elim (λ b → -⊗-intro {k = Motive n} (LinΣ-intro b ∘g open[))) ∘g ⊗-intro id (LinΠ-app (suc n)))
    ; ] → ⟜-intro {k = Motive n}
        (Nat.elim {A = λ n → _ ⊢ Motive n}
          (LinΣ-intro false ∘g unexpected] ∘g ⊗-intro id ⊤-intro)
          (λ n-1 _ →
        -⊗-intro⁻ (LinΣ-elim (λ b → -⊗-intro {k = Motive (suc n-1)}
          (LinΣ-intro b ∘g close]))
        ∘g LinΠ-app n-1))
          n)
    })))
  })
  where
    Motive : ℕ → Grammar _
    Motive = λ n → LinΣ[ b ∈ Bool ] BalancedStkTr n b

-- alternative: define this function by recursion
decide : ∀ n → BalancedStk n ⊢ LinΣ[ b ∈ Bool ] BalancedStkTr n b
decide = {!!}

exhibitTrace : Balanced ⊢ BalancedStkTr zero true
exhibitTrace = {!!} where
  Motive = BalancedStkTr zero true
  [nil] : ε-grammar ⊢ Motive
  [nil] = eof
  [balanced] : literal [ ⊗ (Motive ⊗ (literal ] ⊗ Motive)) ⊢ Motive
  [balanced] = {!!}
    ∘g ⊗-intro id (⊗-intro {l = BalancedStkTr 1 true} id (close] {n = zero}{b = true}))

-- idea: S(n) is a version of Dyck that closes n parens
mkParseTree : BalancedStkTr zero true ⊢ Balanced
mkParseTree = {!!} where
  -- ε        ⊢ S(0)
  -- [ S(n+1) ⊢ S(n)
  -- ] S(n)   ⊢ S(n+1)

  Motive : ℕ → Grammar _
  -- Motive = Nat.elim Balanced (λ _ B⟨n⟩ → literal [ -⊗ (Balanced -⊗ B⟨n⟩))
  Motive = Nat.elim Balanced (λ _ B⟨n⟩ → Balanced -⊗ (literal [ -⊗ B⟨n⟩))
  [eof] : ε-grammar ⊢ Motive zero
  [eof] = nil
  [open[] : ∀ {n} → literal [ ⊗ Motive (suc n) ⊢ Motive n
  [open[] = -⊗-app ∘g ⊗-intro id (-⊗-app ∘g ⊗-intro nil id ∘g ⊗-unit-l⁻)
  -- [open[] = ((-⊗-app ∘g ⊗-intro nil id) ∘g ⊗-unit-l⁻) ∘g -⊗-app
  [close]] : ∀ {n} → literal ] ⊗ Motive n ⊢ Motive (suc n)
  [close]] {n} =
    Nat.elim {A = λ n → (literal ] ⊗ Motive n) ⊢ Motive (suc n)}
    (-⊗-intro (-⊗-intro balanced))
    (λ n-1 rec → -⊗-intro (-⊗-intro (-⊗-intro (-⊗-intro {k = Motive n-1} {!!})))) n
  -- [close]] {n} = Nat.elim
  --                 {A = λ n → Term (literal ] ⊗ Motive n) (literal [ -⊗ Motive n)}
  --   (-⊗-intro {k = Motive zero} {!!})
  --   (λ n-1 rec → {!!})
  --   n

  --   -⊗-intro {k = Motive zero}
  --   (balanced ∘g ⊗-intro id ({!!} ∘g ⊗-intro (⊗-intro nil id ∘g ⊗-unit-l⁻) id))
  -- [close]] {suc n} = {!!}
  
