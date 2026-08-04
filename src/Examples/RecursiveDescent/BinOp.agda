{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.RecursiveDescent.BinOp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (uncurry)

open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Examples.BinOp
open LL⟨1⟩

open import Grammar Alphabet renaming (NIL to *NIL) hiding (_+ ; Δ)
open import Grammar.Maybe.Base Alphabet hiding (μ)
open import Grammar.SemanticAction Alphabet
open import Grammar.Later.Base Alphabet
open import Grammar.Later.Properties Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Parser.Base Alphabet hiding (Parser)
open import Parser.RecursiveDescent Alphabet
open import Term Alphabet

open StrongEquivalence


-- `ATOM ⊗ ＂ + ＂` is non-nullable: the right factor is a literal.
+-after-atom-¬null : ⟨ ¬Nullable (ATOM ⊗ ＂ + ＂) ⟩
+-after-atom-¬null = ¬Nullable⊗r (disjoint-ε-literal +)

-- After parsing an ATOM, peek the leftover and either consume `+ E`
-- (tail recursion) or terminate with `just (DONE atom, leftover)`.
after-atom : (▷ (MaybeLeft EXP)) & (ATOM ⊗ string) ⊢ MaybeLeft EXP
after-atom =
  ⊕-elim
    -- ε leftover: just (DONE atom, ε).
    (just ∘g (DONE ,⊗ *NIL) ∘g π₂)
    -- char ⊗ string leftover: dispatch on the leftover's first char.
    (⊕ᴰ-elim next-tail
     ∘g &⊕ᴰ-distR≅ .fun
     ∘g id ,&p ⊕ᴰ-distR .fun
     ∘g id ,&p (id ,⊗ ⊕ᴰ-distL .fun))
  ∘g &⊕-distL
  ∘g id ,&p ⊗⊕-distL
  ∘g id ,&p (id ,⊗ unroll-string≅ .fun)
  where
    -- For non-`+` leftovers, return the atom as DONE and let the
    -- offending char remain in the string leftover.
    terminate : ∀ (c : Tok) →
      (▷ (MaybeLeft EXP)) & (ATOM ⊗ literal c ⊗ string) ⊢ MaybeLeft EXP
    terminate _ = just ∘g DONE ,⊗ string-intro ∘g π₂

    next-tail : ∀ (c : Tok) →
      (▷ (MaybeLeft EXP)) & (ATOM ⊗ literal c ⊗ string) ⊢ MaybeLeft EXP
    next-tail [ = terminate [
    next-tail ] = terminate ]
    next-tail (num m) = terminate (num m)
    next-tail + =
      -- Consume the dynamic prefix `ATOM ⊗ +` via ▷-app-NE; the
      -- recursive call parses the tail E from the post-+ string.
      fmap (ADD ,⊗ id
            ∘g ⊗-assoc
            ∘g id ,⊗ ⊗-assoc
            ∘g ⊗-assoc⁻)
      ∘g Maybe⊗r
      ∘g ▷-app-NE +-after-atom-¬null
      ∘g &-swap
      ∘g id ,&p reshape
      where
        reshape : ATOM ⊗ ＂ + ＂ ⊗ string ⊢ (ATOM ⊗ ＂ + ＂) ⊗ ⊤
        reshape = id ,⊗ ⊤-intro ∘g ⊗-assoc

-- num atom: assemble NUM n, then dispatch via after-atom.
num-atom : ∀ (n : ℕ) → (▷ (MaybeLeft EXP)) & (＂ num n ＂ ⊗ string) ⊢ MaybeLeft EXP
num-atom n = after-atom ∘g id ,&p ((NUM ∘g σ n) ,⊗ id)

paren-atom : (▷ (MaybeLeft EXP)) & (＂ [ ＂ ⊗ string) ⊢ MaybeLeft EXP
paren-atom =
  ⊕-elim
    post-inner-paren
    (nothing ∘g ⊤-intro)
  ∘g &⊕-distL
  ∘g id ,&p Maybe⊗r
  ∘g id ,&p (⊗-unit-r ,⊗ id)
  ∘g id ,&p (id ,⊗ π₂)
  ∘g id ,&p ▷-app-NE-keep-⌈⌉ (([ ∷ []) , ¬cons≡nil)
  ∘g id ,&p ((⊗-assoc ∘g id ,⊗ ⊗-unit-l⁻) ,&p id)
  ∘g π₁ ,& &-swap
  where
    -- Inner E parsed successfully. The leftover must begin with `]`;
    -- on any other token (or end of string) fail.
    post-inner-paren : ▷ (MaybeLeft EXP) & (＂ [ ＂ ⊗ EXP ⊗ string) ⊢ MaybeLeft EXP
    post-inner-paren =
      ⊕-elim
        (nothing ∘g ⊤-intro)
        (⊕ᴰ-elim leftover-char
         ∘g &⊕ᴰ-distR≅ .fun
         ∘g id ,&p ⊕ᴰ-distR .fun
         ∘g id ,&p (id ,⊗ ⊕ᴰ-distR .fun)
         ∘g id ,&p (id ,⊗ id ,⊗ ⊕ᴰ-distL .fun))
      ∘g &⊕-distL
      ∘g id ,&p ⊗⊕-distL
      ∘g id ,&p (id ,⊗ ⊗⊕-distL)
      ∘g id ,&p (id ,⊗ id ,⊗ unroll-string≅ .fun)
      where
        leftover-char : ∀ (c : Tok) →
          ▷ (MaybeLeft EXP) & (＂ [ ＂ ⊗ EXP ⊗ literal c ⊗ string) ⊢ MaybeLeft EXP
        leftover-char [       = nothing ∘g ⊤-intro
        leftover-char +       = nothing ∘g ⊤-intro
        leftover-char (num n) = nothing ∘g ⊤-intro
        leftover-char ] =
          -- Assemble PARENS from `[ ⊗ E ⊗ ]`, then dispatch via after-atom.
          after-atom
          ∘g id ,&p (PARENS ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc)

per-char : ∀ (c : Tok) → (▷ (MaybeLeft EXP)) & (literal c ⊗ string) ⊢ MaybeLeft EXP
per-char (num n) = num-atom n
per-char [       = paren-atom
per-char ]       = nothing ∘g ⊤-intro
per-char +       = nothing ∘g ⊤-intro

step' : (▷ (MaybeLeft EXP)) & string ⊢ MaybeLeft EXP
step' =
  ⊕-elim
    -- ε input fails: EXP doesn't admit ε.
    (nothing ∘g ⊤-intro)
    (⊕ᴰ-elim per-char
     ∘g &⊕ᴰ-distR≅ .fun
     ∘g id ,&p ⊕ᴰ-distL .fun)
  ∘g &⊕-distL
  ∘g id ,&p unroll-string≅ .fun

step : ▷ (MaybeLeft EXP) ⊢ MaybeLeft EXP
step = step' ∘g id ,& string-intro

parseEXP : Parser EXP
parseEXP = fixP step

recognizeEXP : string ⊢ Maybe EXP
recognizeEXP = parse parseEXP

data BinOpAST : Nonterminal → Type where
  ast-num    : ℕ → BinOpAST Atom
  ast-parens : BinOpAST Exp → BinOpAST Atom
  ast-done   : BinOpAST Atom → BinOpAST Exp
  ast-add    : BinOpAST Atom → BinOpAST Exp → BinOpAST Exp

abstractify-alg : Algebra BinOpTy (λ n → Δ (BinOpAST n))
abstractify-alg Exp = ⊕ᴰ-elim λ where
  done →
    -- ⟦ Var Atom ⟧ = LiftG (Δ (BinOpAST Atom)).
    semact-map ast-done (semact-lift semact-Δ)
  add →
    -- ⟦ Var Atom ⊗e k ＂+＂ ⊗e Var Exp ⟧ =
    --   LiftG (Δ AtomAST) ⊗ LiftG ＂+＂ ⊗ LiftG (Δ ExpAST)
    semact-map (uncurry ast-add)
      (semact-concat
        (semact-lift semact-Δ)
        (semact-right (semact-lift semact-Δ)))
abstractify-alg Atom = ⊕ᴰ-elim λ where
  num →
    -- ⟦ k anyNum ⟧ = LiftG (⊕[ n ∈ ℕ ] ＂num n＂). Extract the ℕ.
    semact-map ast-num
      (semact-lift (semact-⊕ᴰ' (λ n → semact-pure n)))
  parens →
    -- ⟦ k ＂[＂ ⊗e Var Exp ⊗e k ＂]＂ ⟧ =
    --   LiftG ＂[＂ ⊗ LiftG (Δ ExpAST) ⊗ LiftG ＂]＂
    semact-map ast-parens
      (semact-right (semact-left (semact-lift semact-Δ)))

abstractify : EXP ⊢ Δ (BinOpAST Exp)
abstractify = semact-rec abstractify-alg Exp

pretty-parse : string ⊢ Maybe (Δ (BinOpAST Exp))
pretty-parse = fmap abstractify ∘g recognizeEXP

partial-parse : string ⊢ Maybe (Δ (BinOpAST Exp × String))
partial-parse = fmap (semact-concat abstractify semact-string) ∘g parseEXP

module pretty = RunIncompleteParser pretty-parse
module partial = RunIncompleteParser partial-parse

-- ===== parse? tests =====

opaque
  unfolding unfoldRecursiveDescentDefs

  -- Successes

  _ : pretty.parse? (num 1 ∷ [])
  _ = Sum.inl (ast-done (ast-num 1) , tt) , refl

  _ : pretty.parse? (num 1 ∷ + ∷ num 2 ∷ [])
  _ = Sum.inl (ast-add (ast-num 1) (ast-done (ast-num 2)) , tt) , refl

  _ : pretty.parse? (num 1 ∷ + ∷ num 2 ∷ + ∷ num 3 ∷ [])
  _ = Sum.inl (ast-add (ast-num 1) (ast-add (ast-num 2) (ast-done (ast-num 3))) ,
               tt) , refl

  _ : pretty.parse? ([ ∷ num 1 ∷ ] ∷ [])
  _ = Sum.inl (ast-done (ast-parens (ast-done (ast-num 1))) , tt) , refl

  _ : pretty.parse? ([ ∷ num 1 ∷ + ∷ num 2 ∷ ] ∷ [])
  _ = Sum.inl
       (ast-done (ast-parens (ast-add (ast-num 1) (ast-done (ast-num 2))))
        , tt) , refl

  _ : pretty.parse? ([ ∷ num 1 ∷ + ∷ num 2 ∷ ] ∷ + ∷ num 3 ∷ [])
  _ = Sum.inl
       (ast-add (ast-parens (ast-add (ast-num 1) (ast-done (ast-num 2))))
        (ast-done (ast-num 3))
        , tt) , refl

  _ : pretty.parse? ([ ∷ [ ∷ num 1 ∷ ] ∷ ] ∷ [])
  _ = Sum.inl
       (ast-done
        (ast-parens (ast-done (ast-parens (ast-done (ast-num 1)))))
        , tt) , refl

  -- Failures

  _ : pretty.parse? []
  _ = Sum.inr _ , refl

  _ : pretty.parse? (+ ∷ [])
  _ = Sum.inr _ , refl

  _ : pretty.parse? (] ∷ [])
  _ = Sum.inr _ , refl

  _ : pretty.parse? (num 1 ∷ + ∷ [])
  _ = Sum.inr _ , refl

  _ : pretty.parse? ([ ∷ [])
  _ = Sum.inr _ , refl

  _ : pretty.parse? ([ ∷ num 1 ∷ [])
  _ = Sum.inr _ , refl

  _ : pretty.parse? ([ ∷ ] ∷ [])
  _ = Sum.inr _ , refl

  -- Partial successes with nonempty leftover input

  _ : partial.parse? (num 1 ∷ num 2 ∷ [])
  _ = Sum.inl ((ast-done (ast-num 1) , num 2 ∷ []) , tt) , refl

  _ : partial.parse? (num 1 ∷ ] ∷ [])
  _ = Sum.inl ((ast-done (ast-num 1) , ] ∷ []) , tt) , refl

  _ : partial.parse? ([ ∷ num 1 ∷ ] ∷ num 2 ∷ [])
  _ = Sum.inl ((ast-done (ast-parens (ast-done (ast-num 1))) , num 2 ∷ []) , tt) , refl

  _ : partial.parse? (num 1 ∷ + ∷ num 2 ∷ ] ∷ [])
  _ = Sum.inl ((ast-add (ast-num 1) (ast-done (ast-num 2)) , ] ∷ []) , tt) , refl

  -- Partial parser failures

  _ : partial.parse? (+ ∷ num 1 ∷ [])
  _ = Sum.inr _ , refl

  _ : partial.parse? (] ∷ num 1 ∷ [])
  _ = Sum.inr _ , refl
