{- Some presentations of the Dyck grammar of balanced parentheses,
   and hopefully some parsers? -}

{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
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
open import Term Alphabet

-- a simple, but ambiguous grammar for balanced parentheses
data Dyck : Grammar ℓ-zero where
  none : ε ⊢ Dyck
  sequence  : Dyck ⊗ Dyck ⊢ Dyck
  bracketed : literal [ ⊗ Dyck ⊗ literal ] ⊢ Dyck

-- Dyck grammar, an LL(0) grammar:
-- S → ε
--   | [ S ] S
data Balanced : Grammar ℓ-zero where
  nil : ε ⊢ Balanced
  balanced : literal [ ⊗ Balanced ⊗ literal ] ⊗ Balanced ⊢ Balanced

module BALANCED where
  record Algebra ℓ : Type (ℓ-suc ℓ) where
    field
      U : Grammar ℓ
      [nil] : ε ⊢ U
      [balanced] : literal [ ⊗ U ⊗ literal ] ⊗ U ⊢ U

  open Algebra public
  InitialAlgebra : Algebra _
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

  {-# TERMINATING #-}
  rec : ∀ (G : Algebra ℓg) → Hom InitialAlgebra G
  rec G .fun = go where
    go : Balanced ⊢ (U G)
    go w (nil .w x) = [nil] G w x
    go w (balanced .w x) = (G .[balanced] ∘g (id ,⊗ go ,⊗ id ,⊗ go)) w x
  rec G .fun-nil = refl
  rec G .fun-balanced = refl

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
  nil : ε ⊢ RR1
  balanced : RR1 ⊗ literal [ ⊗ RR1 ⊗ literal ] ⊢ RR1

data BalancedStk : ∀ (n : ℕ) → Grammar ℓ-zero where
  eof : ε ⊢ BalancedStk zero
  open[ : ∀ {n} → literal [ ⊗ BalancedStk (suc n) ⊢ BalancedStk n
  close] : ∀ {n} → literal ] ⊗ BalancedStk n ⊢ BalancedStk (suc n)

  -- these are the cases for failure
  leftovers : ∀ {n} → ε ⊢ BalancedStk (suc n)
  unexpected] : literal ] ⊗ ⊤ ⊢ BalancedStk 0

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

  open[ : ∀ {n b} → literal [ ⊗ BalancedStkTr (suc n) b ⊢ BalancedStkTr n b
  close] : ∀ {n b} → literal ] ⊗ BalancedStkTr n b ⊢ BalancedStkTr (suc n) b

  leftovers : ∀ {n} → ε ⊢ BalancedStkTr (suc n) false
  unexpected] : literal ] ⊗ ⊤ ⊢ BalancedStkTr 0 false

module BALANCEDSTKTR where
  record Algebra ℓ : Type (ℓ-suc ℓ) where
    field
      U : ℕ → Bool → Grammar ℓ
      [eof] : ε ⊢ U zero true
      [open] : ∀ {n b} → literal [ ⊗ U (suc n) b ⊢ U n b
      [close] : ∀ {n b} → literal ] ⊗ U n b ⊢ U (suc n) b
      [leftovers] : ∀ {n} → ε ⊢ U (suc n) false
      [unexpected] : literal ] ⊗ ⊤ ⊢ U zero false

  open Algebra public
  InitialAlgebra : Algebra _
  InitialAlgebra .U = BalancedStkTr
  InitialAlgebra .[eof] = eof
  InitialAlgebra .[open] = open[
  InitialAlgebra .[close] = close]
  InitialAlgebra .[leftovers] = leftovers
  InitialAlgebra .[unexpected] = unexpected]

  record Hom {ℓ}{ℓ'} (G : Algebra ℓ)(H : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      fun : ∀ {n b} → G .U n b ⊢ H .U n b
      fun-eof : fun ∘g G .[eof] ≡ H .[eof]
      fun-open[ : ∀ {n b} →
        fun {n = n} ∘g (G .[open] {n = n}{b = b}) ≡
          H .[open] ∘g id ,⊗ fun {n = suc n}
      fun-close] : ∀ {n b} →
        fun {n = suc n} ∘g G .[close] {n = n}{b = b} ≡ H .[close] ∘g id ,⊗ fun {n = n}
      fun-leftovers : ∀ {n} →
        fun ∘g (G .[leftovers] {n = n}) ≡ H .[leftovers]
      fun-unexpected] :
        fun ∘g (G .[unexpected]) ≡ H .[unexpected]
  open Hom public

  idHom : {G : Algebra ℓg} → Hom G G
  idHom .fun = id
  idHom .fun-eof = refl
  idHom .fun-open[ = refl
  idHom .fun-close] = refl
  idHom .fun-leftovers = refl
  idHom .fun-unexpected] = refl

  _∘hom_ : ∀ {ℓ ℓ' ℓ''} {G : Algebra ℓ}{G' : Algebra ℓ'}{G'' : Algebra ℓ''}
    → Hom G' G'' → Hom G G' → Hom G G''
  (ϕ ∘hom ψ) .fun = ϕ .fun ∘g ψ .fun
  (ϕ ∘hom ψ) .fun-eof = cong (ϕ .fun ∘g_) (ψ .fun-eof) ∙ ϕ .fun-eof
  (ϕ ∘hom ψ) .fun-open[ =
    cong (ϕ .fun ∘g_) (ψ .fun-open[) ∙
    cong (_∘g id ,⊗ ψ .fun) (ϕ .fun-open[)
  (ϕ ∘hom ψ) .fun-close] =
    cong (ϕ .fun ∘g_) (ψ .fun-close]) ∙
    cong (_∘g id ,⊗ ψ .fun) (ϕ .fun-close])
  (ϕ ∘hom ψ) .fun-leftovers =
    cong (ϕ .fun ∘g_) (ψ .fun-leftovers) ∙
    ϕ .fun-leftovers
  (ϕ ∘hom ψ) .fun-unexpected] =
    cong (ϕ .fun ∘g_) (ψ .fun-unexpected]) ∙
    ϕ .fun-unexpected]

  {-# TERMINATING #-}
  rec' : ∀ (G : Algebra ℓg) {n b} → BalancedStkTr n b ⊢ G .U n b
  rec' G w (eof .w x) = G .[eof] w x
  rec' G w (open[ .w x) =
    (G .[open] ∘g id ,⊗ rec' G) w x
  rec' G w (close] .w x) =
    (G .[close] ∘g id ,⊗ rec' G) w x
  rec' G w (leftovers .w x) = G .[leftovers] w x
  rec' G w (unexpected] .w x) = G .[unexpected] w x

  rec : ∀ (G : Algebra ℓg) → Hom InitialAlgebra G
  rec G .fun = rec' G
  rec G .fun-eof = refl
  rec G .fun-open[ = refl
  rec G .fun-close] = refl
  rec G .fun-leftovers = refl
  rec G .fun-unexpected] = refl

parseStkTr : string ⊢ LinΠ[ n ∈ ℕ ] LinΣ[ b ∈ Bool ] BalancedStkTr n b
parseStkTr = foldKL*r _ (record { the-ℓ = _ ; G = _
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
    Motive : ℕ → Grammar _
    Motive = λ n → LinΣ[ b ∈ Bool ] BalancedStkTr n b

-- alternative: define this function by recursion
-- decide : ∀ n → BalancedStk n ⊢ LinΣ[ b ∈ Bool ] BalancedStkTr n b
-- decide = {!!}

-- to turn an LL(0) tree of balanced parens into a trace, turn each
-- subtree into a function that appends onto a balanced stack trace of
-- arbitrary state without changing it.
exhibitTrace : Balanced ⊢ BalancedStkTr zero true
exhibitTrace =
  (((⟜-app ∘g id ,⊗ eof) ∘g ⊗-unit-r⁻) ∘g LinΠ-app zero)
  ∘g BALANCED.fun (BALANCED.rec alg)
  where
  alg : BALANCED.Algebra _
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
mkParseTree : BalancedStkTr zero true ⊢ Balanced
mkParseTree =
  done ∘g
  BALANCEDSTKTR.rec
    (record
      { U = Motive'
      ; [eof] = [eof]
      ; [open] = λ {n} → λ {
          {false} → ⊤-intro
        ; {true} → [open] {n} }
      ; [close] = λ {n} → λ {
          {false} → ⊤-intro
        ; {true} → [close] {n} }
      ; [leftovers] = ⊤-intro
      ; [unexpected] = ⊤-intro
      })
    .BALANCEDSTKTR.Hom.fun
  where
  Stk : ℕ → Grammar _
  Stk = Nat.elim ε λ _ Stk⟨n⟩ → literal ] ⊗ Balanced ⊗ Stk⟨n⟩
  -- our state is a "current" Balanced expr that we are building, as
  -- well as a stack of ]-separated balanced exprs that are waiting to
  -- be completed
  Motive : ℕ → Grammar _
  Motive n = Balanced ⊗ Stk n

  Motive' : ℕ → Bool → Grammar _
  Motive' n false = ⊤
  Motive' n true = Motive n

  -- we initialize the current expression to be the empty parse
  [eof] : ε ⊢ Motive zero
  [eof] = ⊗-intro nil id ∘g ⊗-unit-l⁻
  -- when we see a close paren, we push it and the current expression
  -- onto the stack and initialize the new current exp to be empty
  [close] : ∀ {n} → literal ] ⊗ Motive n ⊢ Motive (suc n)
  [close] {n} = ⊗-intro nil id ∘g ⊗-unit-l⁻
  -- when we see an open paren, we combine the current balanced exp
  -- with the top frame which we pop off of the stack
  [open] : ∀ {n} → literal [ ⊗ Motive (suc n) ⊢ Motive n
  [open] = ⊗-intro balanced id ∘g ⊗-assoc ∘g
    ⊗-intro id (⊗-assoc ∘g ⊗-intro id ⊗-assoc)

  done : Motive 0 ⊢ Balanced
  done = ⊗-unit-r

open StrongEquivalence
BalancedStkTr≅string :
  ∀ n →
  StrongEquivalence
    (LinΣ[ b ∈ Bool ] BalancedStkTr n b)
    string
BalancedStkTr≅string n .fun =
  LinΣ-elim (λ b →
    BALANCEDSTKTR.rec
      (record
        { U = λ _ _ → string
        ; [eof] = KL*.nil
        ; [open] = KL*.cons ∘g LinΣ-intro [ ,⊗ id
        ; [close] = KL*.cons ∘g LinΣ-intro ] ,⊗ id
        ; [leftovers] = KL*.nil
        ; [unexpected] = KL*.cons ∘g LinΣ-intro ] ,⊗ ⊤→string
        })
      .BALANCEDSTKTR.Hom.fun)
BalancedStkTr≅string n .inv = LinΠ-app n ∘g parseStkTr
BalancedStkTr≅string n .sec = {!!} -- string to string
BalancedStkTr≅string n .ret = {!!}

unambiguous-BalancedStkTr : ∀ n → unambiguous (LinΣ[ b ∈ Bool ] BalancedStkTr n b)
unambiguous-BalancedStkTr n = unambiguous≅ (sym-strong-equivalence (BalancedStkTr≅string n)) unambiguous-string

module _ {ℓS}{ℓH}{A : Type ℓS} {h : A → Grammar ℓH} where
  unambiguousΣ : unambiguous (LinΣ[ a ∈ A ] h a) → (a : A) → unambiguous (h a)
  unambiguousΣ unambigΣ a e e' p = {!!}

-- TODO: show this is a *strong* equivalence!
Balanced≅ : StrongEquivalence Balanced (BalancedStkTr zero true)
Balanced≅ .fun = exhibitTrace
Balanced≅ .inv = mkParseTree
Balanced≅ .sec = unambiguousΣ (unambiguous-BalancedStkTr zero) true _ _ {!!}
Balanced≅ .ret = {!!} -- use ind
