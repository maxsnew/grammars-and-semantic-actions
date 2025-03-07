{- Grammar for one associative binary operation with constants and parens -}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.BinOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Nat as Nat
open import Cubical.Data.FinSet
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma

-- TODO need to make this work with opaqueness
-- data Tok : Type where
--   LP RP : Tok   -- parens
--   * : Tok       -- the binary operation
--   num : ℕ → Tok -- constants

-- Alphabet : hSet _
-- Alphabet = Tok , isSetRetract encode decode dex≡x (isSet⊎ isSetFin isSetℕ)
--   where
--   open import Cubical.Data.Sum as Sum
--   open import Cubical.Data.Fin as Fin
--   Tok' = Fin 3 ⊎ ℕ
--   encode : Tok → Tok'
--   encode LP = inl 0
--   encode RP = inl 1
--   encode * = inl 2
--   encode (num x) = inr x
--   decode : Tok' → Tok
--   decode (inl (0 , snd₁)) = LP
--   decode (inl (1 , snd₁)) = RP
--   decode (inl (suc (suc fst₁) , snd₁)) = *
--   decode (inr x) = num x
--   dex≡x : ∀ x → decode (encode x) ≡ x
--   dex≡x LP = refl
--   dex≡x RP = refl
--   dex≡x * = refl
--   dex≡x (num x) = refl

-- open import Grammar Alphabet
-- open import Grammar.Equivalence Alphabet
-- open import Term Alphabet

-- anyNum : Grammar _
-- anyNum = LinΣ[ n ∈ ℕ ] literal (num n)
-- module LL⟨1⟩ where
--   Exp : Grammar ℓ-zero
--   data Atom : Grammar ℓ-zero

--   Exp = Atom ⊗' (KL* (literal * ⊗' Atom))
--   data Atom where
--     num : ∀ {n} → literal (num n) ⊢ Atom
--     parens :
--       literal LP ⊗' Exp ⊗' literal RP ⊢ Atom

--   -- This grammar is LL(1) because after you match a close paren, you
--   -- need to look ahead one token to know if you continue matching
--   -- close parens or have finished parsing the Atom.
--   opaque
--     unfolding _⊗_
--     num' : ∀ {n} → ε ⊢ Atom ⊸ literal (num n)
--     num' {n} = ⊸-intro-ε {k = Atom} (num {n})
--     parens' : ε ⊢ Atom ⊸ literal RP ⊸ Exp ⊸ literal LP
--     parens' = ⊸3-intro-ε parens

--   record Algebra ℓ : Type (ℓ-suc ℓ) where
--     field
--       UE : Grammar ℓ
--       UAs : Grammar ℓ
--       UA : Grammar ℓ

--       [mkExp] : UA ⊗ UAs ⊢ UE
--       [nil] : ε ⊢ UAs
--       [cons] : (literal * ⊗ UA) ⊗ UAs ⊢ UAs
--       [num] : ∀ {n} → literal (num n) ⊢ UA
--       [parens] : literal LP ⊗ UE ⊗ literal RP ⊢ UA

--   open Algebra
--   opaque
--     unfolding _⊗_
--     initialAlgebra : Algebra ℓ-zero
--     initialAlgebra .UE = Exp
--     initialAlgebra .UAs = KL* (literal * ⊗ Atom)
--     initialAlgebra .UA = Atom
--     initialAlgebra .[mkExp] = id
--     initialAlgebra .[nil] = nil
--     initialAlgebra .[cons] = cons
--     initialAlgebra .[num] = num
--     initialAlgebra .[parens] = parens
--   record Hom {ℓ}{ℓ'} (A : Algebra ℓ) (B : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
--     field
--       fE : A .UE ⊢ B .UE
--       fAs : A .UAs ⊢ B .UAs
--       fA : A .UA ⊢ B .UA

--   -- this can be avoided by doing manual recursion for rAs
--   opaque
--     unfolding _⊗_ initialAlgebra
--     fold : ∀ {ℓ}(A : Algebra ℓ) → Hom initialAlgebra A
--     fold A = record { fE = rE ; fAs = rAs ; fA = rA } where
--       rE : Exp ⊢ A .UE
--       rAs : KL* (literal * ⊗ Atom) ⊢ A .UAs
--       rA : Atom ⊢ A .UA
--       rE _ (sp , a , as) = A .[mkExp] _ (sp , rA _ a , rAs _ as)
--       rAs _ (KL*.nil _ x) = A .[nil] _ x
--       rAs _ (KL*.cons _ (sp1 , (sp2 , star , a) , as)) = A .[cons] _ (sp1 , (sp2 , star , rA _ a) , rAs _ as)
--       rA _ (num _ x) = A .[num] _ x
--       rA _ (parens _ (sp1 , lp , sp2 , e , rp)) = A .[parens] _ (sp1 , lp , sp2 , rE _ e , rp)

-- module Automaton where
--   -- TODO: we should be able to generalize this definition to an
--   -- (infinite state) deterministic automaton with guarded
--   -- transitions.

--   -- the stack is a number,
--   -- the number of open parens that are closed by the term

--   -- Exp is for when we are parsing a single expression, Suffix is
--   -- when we are parsing the sequence of multiplications after an
--   -- expression

--   -- the boolean is whether it is an accepting or rejecting trace

--   -- three cases: Opening, Closing, Multiplying

--   -- Opening: at the start of an expression, the term starts with a
--   -- sequence of 0 or more opening parens, which we count. Ends when
--   -- we see a number, then we use lookahead to determine whether to
--   -- parse closing parens or start parsing a multiplication sequence
--   data Opening : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
--   -- Closing: parse as many closing parens as you can, eventually
--   -- use lookahead to decide when to start parsing multiplication sequence
--   data Closing : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
--   -- Parse a sequence of * Exps
--   data Multiplying : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
--   DoneOpening : ∀ (n : ℕ) (b : Bool) → Grammar ℓ-zero
--   DoneOpening n b =
--     ((ε ⊕' (literal * ⊕' literal LP ⊕' anyNum) ⊗' ⊤) &' Multiplying n b)
--     ⊕' ((literal RP ⊗' ⊤) &' Closing n b)
--   data Opening where
--     left : ∀ {n b} → literal LP ⊗' Opening (suc n) b ⊢ Opening n b
--     num  : ∀ {n b} →
--       (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗' DoneOpening n b ⊢ Opening n b
--     unexpected : ∀ {n} → ε ⊕' (literal RP ⊕' literal *) ⊗' ⊤ ⊢ Opening n false

--   data Closing where
--     rightClose : ∀ {n b} →
--       literal RP ⊗' DoneOpening n b ⊢ Closing (suc n) b
--     rightUnmatched : literal RP ⊗' ⊤ ⊢ Closing 0 false
--     unexpected : ∀ {n} → ε ⊕' (literal * ⊕' literal LP ⊕' anyNum) ⊗' ⊤ ⊢ Closing n false

--   data Multiplying where
--     done : ε ⊢ Multiplying 0 true
--     times : ∀ {n b} → literal * ⊗' Opening n b ⊢ Multiplying n b
--     unmatched : ∀ {n} → ε ⊢ Multiplying (suc n) false
--     unexpected : ∀ {n} →
--       (literal LP ⊕' literal RP ⊕' anyNum) ⊗' ⊤ ⊢ Multiplying n false

--   -- note this is for the true cases, the tautological one would also
--   -- have false cases but we would just use ⊥ for them.
--   --
--   -- because of this we are getting a `warning: -W[no]UnsupportedIndexedMatch`
--   record Algebra ℓ : Type (ℓ-suc ℓ) where
--     field
--       UO : ℕ → Grammar ℓ
--       UC : ℕ → Grammar ℓ
--       UM : ℕ → Grammar ℓ
--     UDO : ℕ → Grammar ℓ
--     UDO n = ((ε ⊕ (literal * ⊕ literal LP ⊕ anyNum) ⊗ ⊤) & UM n)
--       ⊕ ((literal RP ⊗ ⊤) & UC n)
--     field
--       [left] : ∀ {n} → literal LP ⊗ UO (suc n) ⊢ UO n
--       [num]  : ∀ {n} → (LinΣ[ m ∈ ℕ ] literal (num m)) ⊗ UDO n ⊢ UO n
--       [rightClose] : ∀ {n} → literal RP ⊗ UDO n ⊢ UC (suc n)
--       [done] : ε ⊢ UM 0
--       [times] : ∀ {n} → literal * ⊗ UO n ⊢ UM n

--   open Algebra
--   opaque
--     unfolding _⊗_ _⊕_ _&_
--     initialAlgebra : Algebra ℓ-zero
--     initialAlgebra .UO n = Opening n true
--     initialAlgebra .UC n = Closing n true
--     initialAlgebra .UM n = Multiplying n true
--     initialAlgebra .[left] = left
--     initialAlgebra .[num] = num
--     initialAlgebra .[rightClose] = rightClose
--     initialAlgebra .[times] = times
--     initialAlgebra .[done] = done

--   record Hom {ℓ}{ℓ'} (A : Algebra ℓ) (B : Algebra ℓ') : Type (ℓ-max ℓ ℓ') where
--     field
--       fO : ∀ n → A .UO n ⊢ B .UO n
--       fC : ∀ n → A .UC n ⊢ B .UC n
--       fM : ∀ n → A .UM n ⊢ B .UM n
--       -- TODO: the equations

--   opaque
--     unfolding _⊗_ _⊕_ _&_ initialAlgebra
--     -- TODO these defs need indexed pattern matching
--     fold : ∀ {ℓ} (A : Algebra ℓ) → Hom initialAlgebra A
--     fold A = record { fO = rO ; fC = rC ; fM = rM } where
--       rO : ∀ n → Opening n true ⊢ A .UO n
--       rC : ∀ n → Closing n true ⊢ A .UC n
--       rM : ∀ n → Multiplying n true ⊢ A .UM n
--       rDO : ∀ n → DoneOpening n true ⊢ UDO A n
--       rO n w (left _ (sp , lp , o)) = A .[left] w (sp , (lp , rO _ _ o))
--       rO n w (num _ (sp , m , doo)) = A .[num] _ (sp , m , rDO _ _ doo)
--       rC _ w (rightClose _ (sp , rp , doo)) = A .[rightClose] _ (sp , rp , rDO _ _ doo)
--       rM _ w (done _ x) = A .[done] _ x
--       rM _ w (times _ (sp , star , o)) = A .[times] _ (sp , star , rO _ _ o)
--       rDO n w (inl x) = inl ((x .fst) , (rM _ _ (x .snd)))
--       rDO n w (inr x) = inr (x .fst , rC _ _ (x .snd))
--     Peek : Maybe Tok → Grammar ℓ-zero
--     Peek = Maybe.rec ε (λ c → literal c ⊗ ⊤)

--     Goal : Grammar ℓ-zero
--     Goal = LinearΣ Peek & LinΠ[ n ∈ ℕ ]
--       (LinearΣ (Opening n)
--       & LinearΣ (Closing n)
--       & LinearΣ (Multiplying n))

--     -- TODO typechecking this parse term is very slow
--     -- Should probably split it into several pieces
-- --     opaque
-- --       -- unfolding LL⟨1⟩.fold LL⟨1⟩.num' LL⟨1⟩.parens' LL⟨1⟩.initialAlgebra _⊗_ _⊕_ _&_ _⇒_ ⊕-elim ⇒-intro ⇐-intro ⟜-intro ⟜-app ⊸-intro ⊸-app KL*r-elim fold initialAlgebra ⊗-intro &-intro &-π₁ &-π₂ ⊕-inl ⊕-inr ⇒-app
-- --       parse' : string ⊢ LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- --         (LinearΣ (Opening n)
-- --         & LinearΣ (Closing n)
-- --         & LinearΣ (Multiplying n))
-- --       parse' = foldKL*r char
-- --         (record {
-- --           the-ℓ = ℓ-zero
-- --         ; G = LinearΣ Peek & LinΠ[ n ∈ ℕ ]
-- --               (LinearΣ (Opening n)
-- --               & LinearΣ (Closing n)
-- --               & LinearΣ (Multiplying n))
-- --         ; nil-case =
-- --           LinΣ-intro Maybe.nothing
-- --           ,& LinΠ-intro λ n →
-- --             (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- --             ,& (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- --             ,& Nat.elim {A = λ n → Term ε (LinearΣ (Multiplying n))} (LinΣ-intro true ∘g done) (λ n-1 _ → LinΣ-intro false ∘g unmatched) n
-- --         ; cons-case =
-- --           (⊸-intro⁻ (LinΣ-elim (λ tok → ⊸-intro {k = LinearΣ Peek}
-- --             (LinΣ-intro {A = Maybe Tok} (just tok) ∘g id ,⊗ ⊤-intro))))
-- --           ,& LinΠ-intro λ n →
-- --             {!!}
-- --         })
-- --       -- foldKL*r _ (record { the-ℓ = _ ; G = _
-- --       --   ; nil-case =
-- --       --     LinΣ-intro Maybe.nothing
-- --       --     ,& LinΠ-intro λ n →
-- --       --     (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- --       --     ,& (LinΣ-intro false ∘g unexpected ∘g ⊕-inl)
-- --       --     ,& Nat.elim {A = λ n → Term ε (LinearΣ (Multiplying n))} (LinΣ-intro true ∘g done) (λ n-1 _ → LinΣ-intro false ∘g unmatched) n
-- --       --   ; cons-case =
-- --       --     (⊸-intro⁻ (LinΣ-elim (λ tok → ⊸-intro {k = LinearΣ Peek}
-- --       --       (LinΣ-intro {A = Maybe Tok} (just tok) ∘g id ,⊗ ⊤-intro))))
-- --       --     ,& LinΠ-intro λ n →
-- --       --       (⊸-intro⁻
-- --       --         (LinΣ-elim λ
-- --       --         { (num x) → ⊸-intro {k = LinearΣ (Opening n)} (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- --       --           -- goto closing
-- --       --           { (just RP) → ⇒-intro (⇐-intro⁻ (((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ ⊕-inr))) ∘g &-π₁) ∘g &-π₂))
-- --       --           ; nothing → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g ⊕-inl ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --           ; (just *) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --           ; (just LP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --           ; (just (num y)) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g num ∘g LinΣ-intro x ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro y) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --           }))
-- --       --           ∘g id ,⊗ id ,&p LinΠ-app n)
-- --       --           --  (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- --       --         ; LP → ⊸-intro {k = LinearΣ (Opening n)} (⟜-intro⁻ (((LinΣ-elim (λ b → ⟜-intro {k = LinearΣ (Opening n)} (LinΣ-intro b ∘g left)) ∘g &-π₁)) ∘g LinΠ-app (suc n) ∘g &-π₂))
-- --       --         ; RP → ⊸-intro {k = LinearΣ (Opening n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro)
-- --       --         ; * → ⊸-intro {k = LinearΣ (Opening n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inr ∘g ⊕-inr ,⊗ ⊤-intro)
-- --       --         })
-- --       --       )
-- --       --       -- ⊸-intro⁻
-- --       --       ,& ⊸-intro⁻ (LinΣ-elim λ
-- --       --        { RP → ⊸-intro {k = LinearΣ (Closing n)} (Nat.elim {A = λ n → Term (literal RP ⊗ Goal) (LinearΣ (Closing n))}
-- --       --          -- empty stack
-- --       --          (LinΣ-intro false ∘g rightUnmatched ∘g id ,⊗ ⊤-intro)
-- --       --          -- popped
-- --       --          (λ n-1 _ → (⟜-intro⁻ (⇒-intro⁻ (LinΣ-elim λ
-- --       --            { (just RP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ ⊕-inr))) ∘g &-π₁ ∘g &-π₂))
-- --       --            ; nothing → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g ⊕-inl ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --            ; (just *) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --            ; (just LP) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --            ; (just (num x)) → ⇒-intro (⇐-intro⁻ ((LinΣ-elim λ b → ⇐-intro (⟜-intro {k = LinearΣ (Closing _)} (LinΣ-intro b ∘g rightClose ∘g id ,⊗ (⊕-inl ∘g (⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ id) ,&p id)))) ∘g &-π₂ ∘g &-π₂))
-- --       --            })) ∘g id ,⊗ id ,&p LinΠ-app n-1))
-- --       --          n)
-- --       --        ; LP → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- --       --          unexpected ∘g ⊕-inr ∘g (⊕-inr ∘g ⊕-inl) ,⊗ ⊤-intro)
-- --       --        ; * → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- --       --          unexpected ∘g ⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro)
-- --       --        ; (num x) → ⊸-intro {k = LinearΣ (Closing n)} (LinΣ-intro false ∘g
-- --       --          unexpected ∘g ⊕-inr ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ ⊤-intro)
-- --       --        })
-- --       --       ,&
-- --       --      (⊸-intro⁻ (LinΣ-elim λ
-- --       --        { * → ⊸-intro {k = LinearΣ (Multiplying n)} (⟜-intro⁻ ((((LinΣ-elim λ b → ⟜-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro b ∘g times)) ∘g &-π₁) ∘g LinΠ-app n) ∘g &-π₂))
-- --       --        ; LP → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g ⊕-inl ,⊗ ⊤-intro)
-- --       --        ; RP → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g (⊕-inr ∘g ⊕-inl) ,⊗ ⊤-intro)
-- --       --        ; (num x) → ⊸-intro {k = LinearΣ (Multiplying n)} (LinΣ-intro false ∘g unexpected ∘g (⊕-inr ∘g ⊕-inr ∘g LinΣ-intro x) ,⊗ ⊤-intro) }))
-- --       --   })

-- -- --     parse : string ⊢ LinΣ[ b ∈ Bool ] Opening zero b
-- -- --     parse = ((&-π₁ ∘g LinΠ-app zero) ∘g &-π₂) ∘g parse'

-- -- -- -- Soundness: i.e., that from every trace we can extract an LL(1) parse
-- -- -- module Soundness where
-- -- --   buildExp : Automaton.Opening 0 true ⊢ LL⟨1⟩.Exp
-- -- --   buildExp = ⊗-unit-r ∘g Automaton.Hom.fO (Automaton.fold alg) 0 where
-- -- --     open LL⟨1⟩ using (Exp; Atom)
-- -- --     open Automaton.Algebra
-- -- --     Stk : ℕ → Grammar ℓ-zero
-- -- --     Stk = Nat.elim ε
-- -- --       (λ _ Stk⟨n⟩ → literal RP ⊗ KL* (literal * ⊗ Atom) ⊗ Stk⟨n⟩)
-- -- --     alg : Automaton.Algebra ℓ-zero
-- -- --     alg .UO n = Exp ⊗ Stk n
-- -- --     alg .UC n = Stk n
-- -- --     alg .UM n = KL* (literal * ⊗ Atom) ⊗ Stk n
-- -- --     alg .[left] = ⊗-assoc ∘g ⊸3⊗ LL⟨1⟩.parens'
-- -- --     alg .[num] {n} = ⟜-intro⁻ (⊕-elim
-- -- --       -- the next thing was multiplying
-- -- --       (⟜-intro {k = Exp ⊗ Stk n} (⊗-assoc ∘g (LinΣ-elim λ _ → Atom.num) ,⊗ &-π₂))
-- -- --       -- the next thing was closing
-- -- --       (⟜-intro {k = Exp ⊗ Stk n} ((LinΣ-elim λ _ → Atom.num ,⊗ nil ∘g ⊗-unit-r⁻) ,⊗ &-π₂)))
-- -- --     alg .[rightClose] {n} = ⟜-intro⁻ (⊕-elim
-- -- --       -- next is multiplying
-- -- --       (⟜-intro {k = Stk (suc n)} (id ,⊗ &-π₂))
-- -- --       -- next is more closing
-- -- --       (⟜-intro {k = Stk (suc n)} (id ,⊗ (⊸0⊗ nil ∘g &-π₂))))
-- -- --     alg .[times] = ⊸2⊗ cons' ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc⁻
-- -- --     alg .[done] = ⊸0⊗ nil

-- -- -- -- Completeness i.e., that every LL(1) parse has a trace. Though
-- -- -- -- completeness would be that every LL(1) parse corresponds to one we
-- -- -- -- extract from the previous function

-- -- -- -- kind of would want a truly dependent linear type here
-- -- -- -- to formulate it that way...
-- -- -- module Completeness where
-- -- --   open LL⟨1⟩.Hom
-- -- --   mkTrace : LL⟨1⟩.Exp ⊢ Automaton.Opening 0 true
-- -- --   mkTrace = (⊸-app ∘g id ,⊗ (⊕-inl ∘g ⊕-inl ,& Automaton.done) ∘g ⊗-unit-r⁻) ∘g LinΠ-app 0 ∘g LL⟨1⟩.fold the-alg .fE where
-- -- --     open LL⟨1⟩.Algebra
-- -- --     the-alg : LL⟨1⟩.Algebra ℓ-zero
-- -- --     -- need to update the motive: a UAs should also produce a proof that it starts with ε or *
-- -- --     the-alg .UE = LinΠ[ n ∈ ℕ ] (Automaton.Opening n true ⊸ Automaton.DoneOpening n true)
-- -- --     the-alg .UAs = LinΠ[ n ∈ ℕ ] (Automaton.DoneOpening n true ⊸ Automaton.DoneOpening n true)
-- -- --     the-alg .UA = LinΠ[ n ∈ ℕ ] (Automaton.Opening n true ⊸ Automaton.DoneOpening n true)
-- -- --     the-alg .[mkExp] = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- --       (((⊸-app ∘g LinΠ-app n ,⊗ (⊸-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻))
-- -- --     the-alg .[nil] = LinΠ-intro λ n → ⊸-intro-ε id
-- -- --     the-alg .[cons] = LinΠ-intro λ n → ⊸-intro {k = Automaton.DoneOpening n true}
-- -- --       (((((⊕-inl ∘g (⊕-inr ∘g ⊕-inl ,⊗ ⊤-intro) ,& Automaton.times) ∘g id ,⊗ ⊸-app) ∘g ⊗-assoc⁻) ∘g (id ,⊗ LinΠ-app n) ,⊗ (⊸-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻)
-- -- --     the-alg .[num] {m} = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- --       (Automaton.num ∘g LinΣ-intro m ,⊗ id)
-- -- --     the-alg .[parens] = LinΠ-intro λ n → ⊸-intro {k = Automaton.Opening n true}
-- -- --       ((Automaton.left ∘g id ,⊗ (⊸-app {g = Automaton.Opening (suc n) true} ∘g LinΠ-app (suc n) ,⊗ (⊕-inr ∘g (id ,⊗ ⊤-intro) ,& Automaton.rightClose)∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
