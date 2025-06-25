{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.BinOp.Grammars where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe hiding (rec)
open import Cubical.Data.Nat as Nat hiding (_+_)
open import Cubical.Data.FinSet
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Examples.BinOp.Alphabet

open import Grammar Alphabet hiding (_+)
open import Parser Alphabet
open import Term Alphabet
open import SemanticAction.Base Alphabet
open import Automata.Deterministic.Lookahead Alphabet

open StrongEquivalence

private
  variable
    ℓ ℓ' ℓA ℓB : Level

module AST where
  data Exp : Type ℓ-zero where
    num : ℕ → Exp
    add : Exp → Exp → Exp

module Ambiguous where
  data Tag : Type ℓ-zero where
    num add parens : Tag

  ExpF : Functor Unit
  ExpF = ⊕e Tag (λ where
    num → k anyNum
    add → Var _ ⊗e k ＂ PLUS ＂ ⊗e Var _
    parens → k ＂ LP ＂ ⊗e Var _ ⊗e k ＂ RP ＂)

  -- TODO: come up with a better interface for writing semantic
  -- actions e.g., "pure" algebras
  semAct : SemanticAction (λ _ → ExpF) (λ _ → AST.Exp)
  semAct _ = ⊕ᴰ-elim λ where
    num → Pure-intro AST.num ∘g lowerG
    add → (⊕ᴰ-elim (λ er → Pure-intro (λ el → AST.add el er) ∘g ⊕ᴰ-distL .StrongEquivalence.fun)
      ∘g ⊕ᴰ-distR .StrongEquivalence.fun)
      ∘g lowerG ,⊗ (⊕ᴰ-distR .StrongEquivalence.fun ∘g (id ,⊗ lowerG))
    parens → (Pure-intro (λ e → e) ∘g ⊕ᴰ-distR .StrongEquivalence.fun) ∘g id ,⊗ (⊕ᴰ-distL .StrongEquivalence.fun ∘g lowerG ,⊗ id)

module RightAssoc where
  data NT : Type ℓ-zero where
    Exp Atom : NT
  data Tag : (N : NT) → Type ℓ-zero where
    done add : Tag Exp
    num parens : Tag Atom

  BinOpF : NT → Functor NT
  BinOpF Exp = ⊕e (Tag Exp) λ where
    done → Var Atom
    add → Var Atom ⊗e k (literal PLUS) ⊗e Var Exp
  BinOpF Atom = ⊕e (Tag Atom) λ where
    num → k anyNum
    parens → k (literal LP) ⊗e Var Exp ⊗e k (literal RP)

  -- Now lets define a composable translation from RightAssoc BinOp expressions to Ambiguous Expressions
  -- To define this composably we start with a translation of carriers:
  Transform : NT → Functor Unit
  Transform Exp = Var _
  Transform Atom = Var _

  -- Next we lift this transform to a functor of algebras
  module _ {X : Unit → Grammar ℓ}(α : Algebra (λ _ → Ambiguous.ExpF) X) where
    un-assoc-alg' : Algebra BinOpF λ nt → ⟦ Transform nt ⟧ X
    un-assoc-alg' Exp = ⊕ᴰ-elim λ where
      done → lowerG
      add → liftG ∘g α _ ∘g σ Ambiguous.add ∘g lowerG ,⊗ id ,⊗ lowerG
    un-assoc-alg' Atom = ⊕ᴰ-elim λ where
      num → liftG ∘g α _ ∘g σ Ambiguous.num
      parens → liftG ∘g α _ ∘g σ Ambiguous.parens ∘g id ,⊗ lowerG ,⊗ id

  module _ {A : Unit → Grammar ℓA}(α : Algebra (λ _ → Ambiguous.ExpF) A)
           {B : Unit → Grammar ℓB}(β : Algebra (λ _ → Ambiguous.ExpF) B)
           (ϕ : Homomorphism (λ _ → Ambiguous.ExpF) α β)
           where
    opaque
      unfolding ⊗-intro
      un-assoc-alg'-functorial : isHomo BinOpF (un-assoc-alg' α) (un-assoc-alg' β)
        λ x → map (Transform x) (ϕ .fst)
      un-assoc-alg'-functorial Exp = ⊕ᴰ≡ _ _ (λ where
        done → refl
        add → (λ i → liftG ∘g ϕ .snd _ i ∘g σ Ambiguous.add ∘g lowerG ,⊗ id ,⊗ lowerG))
      un-assoc-alg'-functorial Atom = ⊕ᴰ≡ _ _ λ where
        num → λ i → liftG ∘g ϕ .snd _ i ∘g σ Ambiguous.num
        parens → λ i → liftG ∘g ϕ .snd _ i ∘g σ Ambiguous.parens ∘g id ,⊗ lowerG ,⊗ id
         
  -- TODO: RightAssoc is weakly equivalent to the ambiguous version (in fact a retract)
  module _ {X : Grammar ℓ} (ϕ : Algebra (λ _ → Ambiguous.ExpF) (λ _ → X)) where
    X' : NT → Grammar ℓ
    X' Exp = X
    X' Atom = X

    un-assoc-alg : Algebra BinOpF X'
    un-assoc-alg Exp = ⊕ᴰ-elim λ where
      done → lowerG
      add → ϕ _ ∘g σ Ambiguous.add
    un-assoc-alg Atom = ⊕ᴰ-elim λ where
      num → ϕ _ ∘g σ Ambiguous.num
      parens → ϕ _ ∘g σ Ambiguous.parens

module LeftFactorized where
  data NT : Type ℓ-zero where
    Exp dE/dA Atom : NT

  data Tag : NT → Type ℓ-zero where
    done add : Tag dE/dA
    num parens : Tag Atom

  BinOpF : NT → Functor NT
  BinOpF Exp = Var Atom ⊗e Var dE/dA
  BinOpF dE/dA = ⊕e (Tag dE/dA) λ where
    done → k ε
    add → k (literal PLUS) ⊗e Var Exp
  BinOpF Atom = ⊕e (Tag Atom) λ where
    num → k anyNum
    parens → k (literal LP) ⊗e Var Exp ⊗e k (literal RP)

  Transform : NT → Functor (RightAssoc.NT)
  Transform Exp = Var RightAssoc.Exp
  Transform dE/dA = ⊕e Bool λ where
    false → k ε*
    true →  k (literal* PLUS) ⊗e Var RightAssoc.Exp
  Transform Atom = Var RightAssoc.Atom

  module _ {A : RightAssoc.NT → Grammar ℓ} (α : Algebra RightAssoc.BinOpF A) where
    un-factorize-alg' : Algebra BinOpF λ nt → ⟦ Transform nt ⟧ A
    un-factorize-alg' Exp =
      ⊕ᴰ-elim (λ where
        false → liftG ∘g α RightAssoc.Exp ∘g σ RightAssoc.done
                ∘g ⊗-unit-r ∘g id ,⊗ (lowerG ∘g lowerG)
        true → liftG ∘g α RightAssoc.Exp ∘g σ RightAssoc.add
               ∘g id ,⊗ mapLift lowerG ,⊗ id)
      ∘g ⊕ᴰ-distR .StrongEquivalence.fun
      ∘g lowerG ,⊗ lowerG
    un-factorize-alg' dE/dA = ⊕ᴰ-elim λ where
      done → σ false ∘g mapLift liftG
      add → σ true ∘g mapLift liftG ,⊗ lowerG
    un-factorize-alg' Atom = ⊕ᴰ-elim λ where
      num → mapLift (α RightAssoc.Atom ∘g σ RightAssoc.num ∘g liftG)
      parens → liftG ∘g α RightAssoc.Atom ∘g σ RightAssoc.parens
               ∘g id ,⊗ lowerG ,⊗ id

  module _ {A : RightAssoc.NT → Grammar ℓA}(α : Algebra RightAssoc.BinOpF A)
           {B : RightAssoc.NT → Grammar ℓB}(β : Algebra RightAssoc.BinOpF B)
           (ϕ : Homomorphism RightAssoc.BinOpF α β)
           where
    opaque
      unfolding ⊗-intro ⊕ᴰ-distR
      un-factorize-alg'-homo : isHomo BinOpF (un-factorize-alg' α) (un-factorize-alg' β)
        λ x → map (Transform x) (ϕ .fst)
      un-factorize-alg'-homo Exp   = {!⊕ᴰ≡-distR _ _ ?!} -- TODO: need a version of ⊕ᴰ≡ combined with distributivity
        -- -- Correct, but yellow
        -- λ i → 
        -- ((⊕ᴰ≡ _ _ λ where
        -- false → λ i → liftG ∘g ϕ .snd RightAssoc.Exp i ∘g σ RightAssoc.done
        --         ∘g ⊗-unit-r ∘g id ,⊗ (lowerG ∘g lowerG)
        -- true → λ i → liftG ∘g ϕ .snd RightAssoc.Exp i ∘g σ RightAssoc.add
        --        ∘g id ,⊗ mapLift lowerG ,⊗ id) i)
        -- ∘g ⊕ᴰ-distR .StrongEquivalence.fun ∘g lowerG ,⊗ lowerG
      un-factorize-alg'-homo dE/dA = ⊕ᴰ≡ _ _ λ where
        done → refl
        add → refl
      un-factorize-alg'-homo Atom  = ⊕ᴰ≡ _ _ λ where
        num → λ i → mapLift (ϕ .snd RightAssoc.Atom i ∘g σ RightAssoc.num ∘g liftG)
        parens → λ i → liftG ∘g ϕ .snd RightAssoc.Atom i ∘g σ RightAssoc.parens
                       ∘g id ,⊗ lowerG ,⊗ id
  

  -- TODO: RightAssoc.BinOp Exp is strongly equivalent to BinOp Exp
  -- and analogous for RightAssoc.BinOp Atom
  module _ {X : RightAssoc.NT → Grammar ℓ} (ϕ : Algebra RightAssoc.BinOpF X) where
    X' : NT → Grammar ℓ
    X' Exp = X RightAssoc.Exp
    -- TODO: might need to use this instead
    -- X' dE/dA = ε ⊕ literal PLUS ⊗ X RightAssoc.Exp
    -- TODO: make this even more de-forested by eliminating this as well?
    X' dE/dA = X RightAssoc.Exp ⟜ X RightAssoc.Atom
    X' Atom = X RightAssoc.Atom

    un-factorize-alg : Algebra BinOpF X'
    un-factorize-alg Exp = ⟜-app ∘g lowerG ,⊗ lowerG
    un-factorize-alg dE/dA = ⊕ᴰ-elim λ where
      done → ⟜-intro (ϕ RightAssoc.Exp ∘g σ RightAssoc.done ∘g liftG ∘g ⊗-unit-r ∘g id ,⊗ lowerG)
      add → ⟜-intro (ϕ RightAssoc.Exp ∘g σ RightAssoc.add ∘g liftG ,⊗ id)
    un-factorize-alg Atom = ⊕ᴰ-elim λ where
      num    → ϕ RightAssoc.Atom ∘g σ RightAssoc.num
      parens → ϕ RightAssoc.Atom ∘g σ RightAssoc.parens

    -- un-factorize : ∀ nt → BinOp nt ⊢ X' nt
    -- un-factorize nt = {!!}
module LookaheadAutomaton where
  data State : Type ℓ-zero where
    Opening Closing Adding : ℕ → State
    fail : State

  aut : DeterministicAutomaton State
  aut .DeterministicAutomaton.init = Opening 0
  aut .DeterministicAutomaton.isAcc (Opening opens) = false
  aut .DeterministicAutomaton.isAcc (Closing opens) = false
  aut .DeterministicAutomaton.isAcc (Adding zero) = true
  aut .DeterministicAutomaton.isAcc (Adding (suc opens)) = false
  aut .DeterministicAutomaton.isAcc fail = false
  aut .DeterministicAutomaton.δ fail c g = fail
  aut .DeterministicAutomaton.δ (Opening opens) [ g = Opening (suc opens)
  aut .DeterministicAutomaton.δ (Opening opens) ] g = fail
  aut .DeterministicAutomaton.δ (Opening opens) + g = fail
  aut .DeterministicAutomaton.δ (Opening opens) (num x) (just ]) = Closing opens
  aut .DeterministicAutomaton.δ (Opening opens) (num x) nothing = Adding opens
  aut .DeterministicAutomaton.δ (Opening opens) (num x) (just +) = Adding opens
  aut .DeterministicAutomaton.δ (Opening opens) (num x) (just [) = fail
  aut .DeterministicAutomaton.δ (Opening opens) (num x) (just (num x₁)) = fail
  aut .DeterministicAutomaton.δ (Closing zero) ] g = fail
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] (just ]) = Closing opens
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] nothing = Adding opens
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] (just +) = Adding opens
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] (just [) = fail
  aut .DeterministicAutomaton.δ (Closing (suc opens)) ] (just (num x)) = fail
  aut .DeterministicAutomaton.δ (Closing opens) [ g = fail
  aut .DeterministicAutomaton.δ (Closing opens) + g = fail
  aut .DeterministicAutomaton.δ (Closing opens) (num x) g = fail
  aut .DeterministicAutomaton.δ (Adding opens) [ g = fail
  aut .DeterministicAutomaton.δ (Adding opens) ] g = fail
  aut .DeterministicAutomaton.δ (Adding opens) + g = Opening opens
  aut .DeterministicAutomaton.δ (Adding opens) (num x) g = fail

  TransformClosing : ℕ → Functor LeftFactorized.NT
  TransformClosing zero = k ε
  TransformClosing (suc n) =
    k (literal RP)
    ⊗e Var LeftFactorized.dE/dA
    ⊗e TransformClosing n

  Transform : State → Functor LeftFactorized.NT
  Transform (Opening x) = Var LeftFactorized.Exp ⊗e TransformClosing x
  Transform (Closing x) = TransformClosing x
  Transform (Adding x) = Var LeftFactorized.dE/dA ⊗e TransformClosing x
  Transform fail = k ⊥

  -- module _ {A : LeftFactorized.NT → Grammar ℓ}
  --          (α : Algebra LeftFactorized.BinOpF A)
  --          where
  --   mkParseTreeAlg' : Algebra (DeterministicAutomaton.TraceF aut true) λ q → ⟦ Transform q ⟧ A
  --   mkParseTreeAlg' (Opening x) = {!!}
  --   mkParseTreeAlg' (Closing x) = {!!}
  --   mkParseTreeAlg' (Adding x) = {!!}
  --   mkParseTreeAlg' fail = {!!}

  module _ (X : LeftFactorized.NT → Grammar ℓ) (ϕ : Algebra LeftFactorized.BinOpF X) where
    -- Can we refunctionalize this?
    -- I.e., can we get rid of the Kleene *?
    [Closing] : ℕ → Grammar ℓ
    [Closing] zero = ε*
    [Closing] (suc n) = literal RP ⊗ X LeftFactorized.dE/dA ⊗ [Closing] n

    X' : State → Grammar ℓ
    X' (Opening opens) = X LeftFactorized.Exp ⊗ [Closing] opens
    X' (Closing opens) = [Closing] opens
    X' (Adding opens)  = X LeftFactorized.dE/dA ⊗ [Closing] opens
    X' fail = ⊥* -- TODO: make this better?

    [Opening] [Adding] : ℕ → Grammar _
    [Opening] n = X' (Opening n)
    [Adding] n = X' (Adding n)

    {- It would be nice if we didn't have to deal with the guards when writing the algebra, they aren't ever used -}
    mkParseTreeAlg : Algebra (DeterministicAutomaton.TraceF aut true) X'
    mkParseTreeAlg (Opening x) = ⊕ᴰ-elim (λ where
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim (λ where
        (lift ([ , g)) → (ϕ LeftFactorized.Exp ∘g (liftG ∘g ϕ LeftFactorized.Atom ∘g σ LeftFactorized.parens) ,⊗ id) ,⊗ id ∘g (((((liftG ∘g lowerG) ∘g lowerG) ,⊗ liftG ,⊗ liftG) ,⊗ liftG ∘g ⊗-assoc3) ,⊗ id ∘g ⊗-assoc4) ∘g id ,⊗ (lowerG ∘g π₁)
        (lift (] , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (+ , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (num n , just [)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (num n , just ])) → (ϕ LeftFactorized.Exp ∘g (liftG ∘g (ϕ LeftFactorized.Atom ∘g σ LeftFactorized.num ∘g mapLift (mkAnyNum ∘g lowerG))) ,⊗ (liftG ∘g (ϕ LeftFactorized.dE/dA ∘g σ LeftFactorized.done ∘g liftG )) ∘g ⊗-unit-r⁻) ,⊗ (lowerG ∘g π₁)
        (lift (num n , nothing)) → ((ϕ LeftFactorized.Exp ∘g (liftG ∘g ϕ LeftFactorized.Atom ∘g σ LeftFactorized.num ∘g mapLift mkAnyNum) ,⊗ liftG) ,⊗ id ∘g ⊗-assoc) ∘g lowerG ,⊗ (lowerG ∘g π₁)
        (lift (num n , just +))  → ((ϕ LeftFactorized.Exp ∘g (liftG ∘g ϕ LeftFactorized.Atom ∘g σ LeftFactorized.num ∘g mapLift mkAnyNum) ,⊗ liftG) ,⊗ id ∘g ⊗-assoc) ∘g lowerG ,⊗ (lowerG ∘g π₁)
        (lift (num n , just (num m))) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁))) -- impossible
    mkParseTreeAlg (Closing zero) = ⊕ᴰ-elim λ where
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim λ where
        (lift ([ , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (] , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (+ , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (num x , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
    mkParseTreeAlg (Closing (suc x)) = ⊕ᴰ-elim λ where
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim λ where
        (lift (] , just ])) → (lowerG ∘g lowerG) ,⊗ ((ϕ LeftFactorized.dE/dA ∘g σ LeftFactorized.done ∘g liftG) ,⊗ (lowerG ∘g π₁) ∘g ⊗-unit-l⁻)
        (lift (] , nothing)) → (lowerG ∘g lowerG) ,⊗ (lowerG ∘g π₁) -- this and the next are the same
        (lift (] , just +)) → (lowerG ∘g lowerG) ,⊗ (lowerG ∘g π₁)
        (lift (] , just [)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (] , just (num x))) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift ([ , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (+ , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (num x , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible

    -- Annoying: the step cases are the same here
    mkParseTreeAlg (Adding zero) = ⊕ᴰ-elim λ where
      DeterministicAutomaton.Tag.stop → ⊕ᴰ-elim λ { (lift Eq.refl) →
        (ϕ LeftFactorized.dE/dA ∘g σ LeftFactorized.done ∘g liftG ∘g lowerG ∘g lowerG) ,⊗ liftG ∘g ⊗-unit-r⁻ }
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim λ where
        (lift (+ , g)) → ((ϕ LeftFactorized.dE/dA ∘g σ LeftFactorized.add ∘g mapLift lowerG ,⊗ liftG) ,⊗ id ∘g ⊗-assoc) ∘g id ,⊗ (lowerG ∘g π₁) -- ez
        (lift ([ , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (] , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (num x , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
    mkParseTreeAlg (Adding (suc x)) = ⊕ᴰ-elim λ where
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim λ where
        (lift (+ , g)) → ((ϕ LeftFactorized.dE/dA ∘g σ LeftFactorized.add ∘g mapLift lowerG ,⊗ liftG) ,⊗ id ∘g ⊗-assoc) ∘g id ,⊗ (lowerG ∘g π₁) -- same as last ez
        (lift ([ , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (] , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
        (lift (num x , g)) → ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) -- impossible
      
    mkParseTreeAlg fail = ⊕ᴰ-elim (λ where
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim λ _ →
        ⊗⊥* ∘g id ,⊗ (lowerG ∘g π₁) )

    mkParseTree : ∀ q → DeterministicAutomaton.Trace aut true q ⊢ X' q
    mkParseTree q = rec (DeterministicAutomaton.TraceF aut true) mkParseTreeAlg q

    X'' : Bool → State → Grammar ℓ
    X'' false = λ _ → ⊤*
    X'' true = X'

    parseTreeAlg : ∀ b → Algebra (DeterministicAutomaton.TraceF aut b) (X'' b)
    parseTreeAlg false = λ _ → ⊤*-intro
    parseTreeAlg true = mkParseTreeAlg

    X''' : Bool → State → Grammar ℓ
    X''' false q = LiftG _ $ DeterministicAutomaton.Trace aut false q
    X''' true = X'
    parseTreeAlg' : ∀ b → Algebra (DeterministicAutomaton.TraceF aut b) (X''' b)
    -- TODO : this could be automatic/unsafeCoerce
    parseTreeAlg' false q = ⊕ᴰ-elim λ where
      DeterministicAutomaton.Tag.stop → ⊕ᴰ-elim (λ foo →
        mapLift (roll ∘g σ DeterministicAutomaton.Tag.stop ∘g σ foo ∘g liftG))
      DeterministicAutomaton.Tag.step → ⊕ᴰ-elim λ foo →
        liftG ∘g roll ∘g σ DeterministicAutomaton.Tag.step ∘g σ foo ∘g mapLift id ,⊗ mapLift lowerG ,&p mapLift id
    parseTreeAlg' true = mkParseTreeAlg

{- Let's start with one step of fusion, fusing the pipeline

  String
  ⊢ &[ q ] ⊕[ b ] Trace q b
  ⊢ ⊕[ b ] Trace Init b
  ⊢ ⊕{ true → Factorized ⊗ ε* ; false → Trace q false }
  ⊢ ⊕{ true → Factorized ; false → Trace q false }
  
  since the translation from Trace Init true ⊢ Factorized ⊗ ε* is just the instantiation of a more general transformation Trace Init q true ⊢ ⟦ q ⟧, this is equivalent to:

  String
  ⊢ &[ q ] ⊕[ b ] Trace q b
  ⊢ &[ q ] ⊕{ true → ⟦ q ⟧ ; false → Trace q false }
  ⊢ ⊕{ true → Factorized ⊗ ε* ; false → Trace q false }  
  ⊢ ⊕{ true → Factorized ; false → Trace q false }

  String
  ⊢ &[ q ] ⊕{ true → ⟦ q ⟧ ; false → Trace q false }
  ⊢ ⊕{ true → Factorized ⊗ ε* ; false → Trace q false }  
  ⊢ ⊕{ true → Factorized ; false → Trace q false }
-}

LFExp : Grammar ℓ-zero
LFExp = μ LeftFactorized.BinOpF LeftFactorized.Exp

open LookaheadAutomaton using (aut; mkParseTreeAlg; mkParseTree; parseTreeAlg')
open DeterministicAutomaton hiding (parse)

the-type : Bool → Grammar _
the-type true = LFExp
the-type false = DeterministicAutomaton.Trace aut false (aut .init)
parseLF-unfused parseLF-fused : string ⊢ ⊕ᴰ the-type

parseLF-unfused =
  map⊕ᴰ (λ where
    false → id
    true →
      (⊗-unit-r ∘g id ,⊗ lowerG) ∘g
      mkParseTree (μ LeftFactorized.BinOpF) (initialAlgebra LeftFactorized.BinOpF) (init aut))
  ∘g π (aut .init)
  ∘g DeterministicAutomaton.parse aut

-- parseLF-unfused' =   map⊕ᴰ (λ where
--     false → lowerG
--     true → (⊗-unit-r ∘g id ,⊗ lowerG)) ∘g
--   π (aut .init) ∘g
--   map&ᴰ (λ q → map⊕ᴰ (λ where
--     false → id
--     true → mkParseTree (μ LeftFactorized.BinOpF) (initialAlgebra LeftFactorized.BinOpF) q)) ∘g
--   DeterministicAutomaton.parse aut

parseLF-fused =
  map⊕ᴰ (λ where
    false → lowerG
    true → (⊗-unit-r ∘g id ,⊗ lowerG)) ∘g
  π (aut .init) ∘g
  DeterministicAutomaton.parse-alg aut (parseTreeAlg' (μ LeftFactorized.BinOpF) (initialAlgebra LeftFactorized.BinOpF))

fusion-correctness : parseLF-unfused ≡ parseLF-fused
fusion-correctness = {!!}

-- the-type' : LookaheadAutomaton.State → Bool → Grammar ℓ-zero
-- the-type' q false = DeterministicAutomaton.Trace aut false (aut .init)
-- the-type' q true = LookaheadAutomaton.X''' {!!} {!!} q
parseLF-unfused' parseLF-fused' : string ⊢ &[ q ∈ LookaheadAutomaton.State ] ⊕[ b ∈ Bool ]
  (LookaheadAutomaton.X''' _ (initialAlgebra LeftFactorized.BinOpF) b q)
parseLF-fused' =
  DeterministicAutomaton.parse-alg aut (parseTreeAlg' (μ LeftFactorized.BinOpF) (initialAlgebra LeftFactorized.BinOpF))

parseLF-unfused' =
  map&ᴰ (λ q → map⊕ᴰ (λ where
    false → liftG
    true → mkParseTree _ (initialAlgebra LeftFactorized.BinOpF) q))
  ∘g DeterministicAutomaton.parse aut

fusion-correctness' : parseLF-unfused' ≡ parseLF-fused'
fusion-correctness' = {!!}

-- to-traceAlg :
--   ∀ {X : Grammar ℓ}
--   → Algebra (λ _ → Ambiguous.ExpF) (λ _ → X)
--   → ∀ b → Algebra (DeterministicAutomaton.TraceF LookaheadAutomaton.aut b) {!!}
-- to-traceAlg {X = X} ϕ =
--   LookaheadAutomaton.parseTreeAlg _ $
--   LeftFactorized.un-factorize-alg   $
--   RightAssoc.un-assoc-alg {X = X} $ ϕ
  

-- -- A parsing pipeline without the semantic action
-- amb-alg : ∀ b → Algebra (DeterministicAutomaton.TraceF LookaheadAutomaton.aut b) _
-- amb-alg =
--   LookaheadAutomaton.parseTreeAlg _ $
--   LeftFactorized.un-factorize-alg   $
--   RightAssoc.un-assoc-alg $
--   initialAlgebra (λ _ → Ambiguous.ExpF)

-- -- A completely deforested parsing pipeline
-- full-alg : ∀ b → Algebra (DeterministicAutomaton.TraceF LookaheadAutomaton.aut b) _
-- full-alg =
--   LookaheadAutomaton.parseTreeAlg _ $
--   LeftFactorized.un-factorize-alg   $
--   RightAssoc.un-assoc-alg $
--   Ambiguous.semAct

-- -- forested-parse' parse' : string ⊢ &ᴰ
-- --                    (λ q →
-- --                       ⊕ᴰ
-- --                       (λ b →
-- --                          LookaheadAutomaton.X''
-- --                          (LeftFactorized.X' (RightAssoc.un-assoc-alg Ambiguous.semAct))
-- --                          (LeftFactorized.un-factorize-alg
-- --                           (RightAssoc.un-assoc-alg Ambiguous.semAct))
-- --                          b q))
-- -- parse' = DeterministicAutomaton.parse-alg
-- --        LookaheadAutomaton.aut
-- --        (LookaheadAutomaton.parseTreeAlg _
-- --          (LeftFactorized.un-factorize-alg (RightAssoc.un-assoc-alg Ambiguous.semAct)))

-- -- forested-parse' = {!!}

-- parse : string ⊢ Pure AST.Exp ⊕ ⊤
-- parse = (⊗-unit-r ∘g id ,⊗ lowerG) ,⊕p ⊤-intro
--   ∘g DeterministicAutomaton.parse-alg' LookaheadAutomaton.aut full-alg

-- parse' : string ⊢ μ (λ _ → Ambiguous.ExpF) _ ⊕ ⊤
-- parse' = (⊗-unit-r ∘g id ,⊗ lowerG) ,⊕p ⊤-intro
--   ∘g DeterministicAutomaton.parse-alg' LookaheadAutomaton.aut amb-alg

-- parse-sound : parse ≡ (rec _ Ambiguous.semAct _ ,⊕p id) ∘g parse'
-- parse-sound = {!!}

-- {- Specification-}
-- -- 1. A semantic type X (in this case AST.Exp)
-- -- 2. A grammar functor F : Functor Unit, with an alg : Algebra F (Pure X)
-- {- A sound and complete parser with semantic values in X would then be -}
-- -- 1. The parsing function p : string ⊢ X ⊕ ⊤
-- -- 2. p is sound if it factorizes via some p' : μ F ⊕ ⊤ as
-- --    p ≡ fold alg ⊕ id ∘g p'
