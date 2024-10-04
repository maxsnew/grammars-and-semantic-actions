{- Some presentations of the Dyck grammar of balanced parentheses,
   and hopefully some parsers? -}

module Examples.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_ ;_or_)
open import Cubical.Data.Nat as Nat
open import Cubical.Data.List hiding (init; rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.FinSet

private
  variable
    ℓg : Level

data Bracket : Type where
  [ ] : Bracket

opaque
  BracketRep : Bracket ≃ Bool
  BracketRep = isoToEquiv (iso
    (λ { [ → true ; ] → false })
    (λ { false → ] ; true → [ })
    (λ { false → refl ; true → refl })
    λ { [ → refl ; ] → refl })

  isFinBracket : isFinSet Bracket
  isFinBracket = EquivPresIsFinSet (invEquiv BracketRep) isFinSetBool

  isSetBracket : isSet Bracket
  isSetBracket = isFinSet→isSet isFinBracket

Alphabet : hSet _
Alphabet = (Bracket , isSetBracket)

open import Grammar Alphabet
open import Grammar.Maybe Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet

-- a simple, but ambiguous grammar for balanced parentheses
data Dyck : Grammar ℓ-zero where
  none : ε ⊢ Dyck
  sequence :
    Dyck ⊗' Dyck ⊢ Dyck
  bracketed :
    literal [ ⊗' Dyck ⊗' literal ] ⊢ Dyck

-- Dyck grammar, an LL(0) grammar:
-- S → ε
--   | [ S ] S
data Balanced : Grammar ℓ-zero where
  nil : ε ⊢ Balanced
  balanced :
    literal [ ⊗' Balanced ⊗' literal ] ⊗' Balanced ⊢ Balanced

module BALANCED where
  record Algebra ℓ : Type (ℓ-suc ℓ) where
    field
      U : Grammar ℓ
      [nil] : ε ⊢ U
      [balanced] : literal [ ⊗ U ⊗ literal ] ⊗ U ⊢ U

  open Algebra public
  opaque
    unfolding _⊗_
    InitialAlgebra : Algebra ℓ-zero
    InitialAlgebra .U = Balanced
    InitialAlgebra .[nil] = nil
    InitialAlgebra .[balanced] = balanced

  record Hom {ℓ}{ℓ'} (G : Algebra ℓ)(H : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      fun : U G ⊢ U H
      fun-nil : fun ∘g G .[nil] ≡ H .[nil]
      fun-balanced :
        fun ∘g G .[balanced] ≡ H .[balanced] ∘g (id ,⊗ fun ,⊗ id ,⊗ fun)
  open Hom public

  opaque
    unfolding ⊗-intro
    idHom : {G : Algebra ℓg} → Hom G G
    idHom .fun = λ w z → z
    idHom .fun-nil = refl
    idHom .fun-balanced = refl

    _∘hom_ : ∀ {ℓ ℓ' ℓ''} {G : Algebra ℓ}{G' : Algebra ℓ'}{G'' : Algebra ℓ''}
      → Hom G' G'' → Hom G G' → Hom G G''
    (ϕ ∘hom ψ) .fun = ϕ .fun ∘g ψ .fun
    (ϕ ∘hom ψ) .fun-nil = cong (ϕ .fun ∘g_) (ψ .fun-nil) ∙ ϕ .fun-nil
    (ϕ ∘hom ψ) .fun-balanced =
      cong (ϕ .fun ∘g_) (ψ .fun-balanced)
      ∙ cong (_∘g id ,⊗ ψ .fun ,⊗ id ,⊗ ψ .fun) (ϕ .fun-balanced)

  opaque
    unfolding _⊗_ InitialAlgebra
    {-# TERMINATING #-}
    rec : ∀ (G : Algebra ℓg) → Hom InitialAlgebra G
    rec G .fun = go where
      go : Balanced ⊢ (U G)
      go w (nil .w x) = [nil] G w x
      go w (balanced .w x) = (G .[balanced] ∘g (id ,⊗ go ,⊗ id ,⊗ go)) w x
    rec G .fun-nil = refl
    rec G .fun-balanced = refl

  opaque
    unfolding literal _⊗_ ⊗-intro InitialAlgebra rec
    ind : ∀ {G : Algebra ℓg} → (ϕ : Hom InitialAlgebra G) → ϕ .fun ≡ rec G .fun
    ind {G = G} ϕ = funExt λ w → funExt go where
      go : ∀ {w} → (x : Balanced w) → ϕ .fun w x ≡ rec G .fun w x
      go (nil _ x) = funExt⁻ (funExt⁻ (ϕ .fun-nil) _) _
      go (balanced _ x) = funExt⁻ (funExt⁻ (ϕ .fun-balanced) _) _
        -- lol, lmao even
        ∙ λ i → G .[balanced] _
        (x .fst ,
        x .snd .fst ,
        x .snd .snd .fst ,
        go (x .snd .snd .snd .fst) i ,
        x .snd .snd .snd .snd .fst ,
        x .snd .snd .snd .snd .snd .fst ,
        go (x .snd .snd .snd .snd .snd .snd) i)

data RR1 : Grammar ℓ-zero where
  nil :  ε ⊢ RR1
  balanced :
    RR1 ⊗' literal [ ⊗' RR1 ⊗' literal ] ⊢ RR1

data BalancedStk : ∀ (n : ℕ) → Grammar ℓ-zero where
  eof : ε ⊢ BalancedStk zero
  -- ∀ w → ε w → BalancedStk zero w
  open[ : ∀ {n} →
    literal [ ⊗' BalancedStk (suc n) ⊢ BalancedStk n
  close] : ∀ {n} →
    literal ] ⊗' BalancedStk n ⊢ BalancedStk (suc n)
  -- these are the cases for failure
  leftovers : ∀ {n} → ε ⊢ BalancedStk (suc n)
  unexpected] :
    literal ] ⊗' ⊤ ⊢ BalancedStk 0

opaque
  unfolding _⊗_ ε
  parseStk : string ⊢ LinΠ[ n ∈ ℕ ] BalancedStk n
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
-- the bool is whether the trace is accepting or rejecting
data BalancedStkTr : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero where
  eof : ε ⊢ BalancedStkTr zero true
  open[ : ∀ {n b} →
    literal [ ⊗' BalancedStkTr (suc n) b ⊢ BalancedStkTr n b
  close] : ∀ {n b} →
    literal ] ⊗' BalancedStkTr n b ⊢ BalancedStkTr (suc n) b
  leftovers : ∀ {n} → ε ⊢ BalancedStkTr (suc n) false
  unexpected] :
    literal ] ⊗' ⊤ ⊢ BalancedStkTr 0 false

opaque
  unfolding _⊗_
  parseStkTr : string ⊢ LinΠ[ n ∈ ℕ ] LinΣ[ b ∈ Bool ] BalancedStkTr n b
  parseStkTr = foldKL*r _ (record { the-ℓ = ℓ-zero ; G = _
    ; nil-case = LinΠ-intro (λ
      { zero → LinΣ-intro true ∘g eof
      ; (suc n) → LinΣ-intro false ∘g leftovers })
    ; cons-case = LinΠ-intro (λ n → ⟜-intro⁻ (LinΣ-elim (λ
      { [ → ⟜-intro {k = Motive n}
          (⊸-intro⁻ (LinΣ-elim
            (λ b → ⊸-intro {k = Motive n} (LinΣ-intro b ∘g open[))) ∘g
              ⊗-intro id (LinΠ-app (suc n)))
      ; ] → ⟜-intro {k = Motive n}
          (Nat.elim {A = λ n → _ ⊢ Motive n}
            (LinΣ-intro false ∘g unexpected] ∘g ⊗-intro id ⊤-intro)
            (λ n-1 _ →
          ⊸-intro⁻ (LinΣ-elim (λ b → ⊸-intro {k = Motive (suc n-1)}
            (LinΣ-intro b ∘g close]))
          ∘g LinΠ-app n-1))
            n)
      })))
    })
    where
      Motive : ℕ → Grammar ℓ-zero
      Motive = λ n → LinΣ[ b ∈ Bool ] BalancedStkTr n b

  -- alternative: define this function by recursion
  -- decide : ∀ n → BalancedStk n ⊢ LinΣ[ b ∈ Bool ] BalancedStkTr n b
  -- decide = {!!}

  -- to turn an LL(0) tree of balanced parens into a trace, turn each
  -- subtree into a function that appends onto a balanced stack trace of
  -- arbitrary state without changing it.
  opaque
    unfolding BALANCED.InitialAlgebra
    exhibitTrace : Balanced ⊢ BalancedStkTr zero true
    exhibitTrace =
      (((⟜-app ∘g id ,⊗ eof) ∘g ⊗-unit-r⁻) ∘g LinΠ-app zero)
      ∘g BALANCED.fun (BALANCED.rec alg)
      where
      alg : BALANCED.Algebra ℓ-zero
      alg .BALANCED.U = LinΠ[ n ∈ ℕ ] (BalancedStkTr n true ⟜ BalancedStkTr n true)
      alg .BALANCED.[nil] = LinΠ-intro λ n → ⟜-intro-ε id
      alg .BALANCED.[balanced] = LinΠ-intro λ n → ⟜-intro {k = BalancedStkTr n true}
        ((open[ ∘g ⊗-intro id (⟜-app ∘g ⊗-intro (LinΠ-app (suc n)) (close]
        ∘g ⊗-intro id (⟜-app ∘g ⊗-intro (LinΠ-app n) id) ∘g ⊗-assoc⁻) ∘g ⊗-assoc⁻))
        ∘g ⊗-assoc⁻)

  -- to translate from BST(0) to S we need to generalize the inductive hypothesis
  -- and pick a motive for BST(n) such that we can extract an S from a BST(0).
  --
  -- Idea: BST(n) is a term with some balanced parens, but n unmatched ]'s in it.
  -- We can define this as an alternating sequence of S and ] with n ]'s in it:
  --     S (] S)^n
  -- We can view this as a "stack" of parses marked by ] "delimiters"
  -- mkParseTree : BalancedStkTr zero true ⊢ Balanced
  -- mkParseTree = {!!} where
  --   Stk : ℕ → Grammar _
  --   Stk = Nat.elim ε-grammar λ _ Stk⟨n⟩ → literal ] ⊗ Balanced ⊗ Stk⟨n⟩
  --   -- our state is a "current" Balanced expr that we are building, as
  --   -- well as a stack of ]-separated balanced exprs that are waiting to
  --   -- be completed
  --   Motive : ℕ → Grammar _
  --   Motive n = Balanced ⊗ Stk n
  --   -- we initialize the current expression to be the empty parse
  --   [eof] : ε-grammar ⊢ Motive zero
  --   [eof] = ⊗-intro nil id ∘g ⊗-unit-l⁻
  --   -- when we see a close paren, we push it and the current expression
  --   -- onto the stack and initialize the new current exp to be empty
  --   [close] : ∀ {n} → literal ] ⊗ Motive n ⊢ Motive (suc n)
  --   [close] {n} = ⊗-intro nil id ∘g ⊗-unit-l⁻
  --   -- when we see an open paren, we combine the current balanced exp
  --   -- with the top frame which we pop off of the stack
  --   [open] : ∀ {n} → literal [ ⊗ Motive (suc n) ⊢ Motive n
  --   [open] = ⊗-intro balanced id ∘g ⊗-assoc ∘g
  --     ⊗-intro id (⊗-assoc ∘g ⊗-intro id ⊗-assoc)

  --   done : Motive 0 ⊢ Balanced
  --   done = ⊗-unit-r

  -- -- TODO: show this is a *strong* equivalence!

open import String.Unicode
open import String.SubAlphabet
open import Cubical.Data.Empty as Empty
open import Cubical.Functions.Embedding

pick-char : Bool → ⟨ Unicode ⟩
pick-char true = '('
pick-char false = ')'

pick-char-inj : ∀ {b b' : Bool} → pick-char b ≡ pick-char b' → b ≡ b'
pick-char-inj {false} {false} _ = refl
pick-char-inj {false} {true} x =
  Empty.rec (mkUnicodeCharPath-no ')' '(' refl x)
pick-char-inj {true} {false} x =
  Empty.rec (mkUnicodeCharPath-no '(' ')' refl x)
pick-char-inj {true} {true} _ = refl

isEmbedding-pick-char : isEmbedding pick-char
isEmbedding-pick-char = injEmbedding (Unicode .snd) pick-char-inj

Bracket' : hSet ℓ-zero
Bracket' =
  UnicodeSubAlphabet (Bool , isSetBool) (pick-char , isEmbedding-pick-char)
    isFinSetBool


BracketIso : Iso Bracket ⟨ Bracket' ⟩
BracketIso .Iso.fun [ = '(' , (true , refl)
BracketIso .Iso.fun ] = ')' , (false , refl)
BracketIso .Iso.inv (c , true , _) = [
BracketIso .Iso.inv (c , false , _) = ]
BracketIso .Iso.rightInv (c , true , fib) i =
  -- idek anymore
  fib i , (true , isSetUnicodeChar _ _ (λ j → fib (i ∧ j)) (λ j → fib (i ∧ j)) i)
BracketIso .Iso.rightInv (c , false , fib) i =
  fib i , (false , isSetUnicodeChar _ _ (λ j → fib (i ∧ j)) (λ j → fib (i ∧ j)) i)
BracketIso .Iso.leftInv [ = refl
BracketIso .Iso.leftInv ] = refl

test : UnicodeString
-- Also tested with a string that was about 21k characters long
-- Took 30 seconds to parse,
-- and correctly fails when the string is unbalanced
test = "()((((())))()()()()(())()())()()"

test' : List ⟨ Bracket' ⟩
test' = toString (Bool , isSetBool) (pick-char , isEmbedding-pick-char) isFinSetBool test

w : String
w = Cubical.Data.List.map (BracketIso .Iso.inv) test'

test-parse : (LinΣ[ b ∈ Bool ] BalancedStkTr 0 b) w
test-parse = (LinΠ-app 0 ∘g parseStkTr) w (⌈w⌉→string {w = w} w (internalize w))

opaque
  unfolding ⟜-app _⟜_ ⟜-intro ⊸-app _⊸_ ⊸-app parseStkTr KL*r-elim ⌈w⌉→string
  _ : test-parse .fst ≡ true
  _ = refl
