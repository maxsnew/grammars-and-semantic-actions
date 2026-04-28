{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Benchmark.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq
import Cubical.Data.Maybe as MaybeD
import Cubical.Data.Empty as Empty

open import Cubical.Relation.Nullary.Base using (yes ; no)

open import Cubical.Data.List hiding (rec)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Foundations.Function using (uncurry)

import Agda.Builtin.String as AS

open import Examples.Dyck
  hiding (LP ; RP)
  renaming ([ to LP ; ] to RP)

open import Grammar Alphabet hiding (Δ) renaming (NIL to *NIL)
open import Grammar.SemanticAction Alphabet
open import Term Alphabet
open import Parser Alphabet

import String.Unicode               as Uni
import Automata.Implicit            as AImp
import Automata.Implicit.RegExp     as IRE
import Lex.Det.Base                 as LexD
import Parser.RecursiveDescent      as PRD
import Grammar.SequentialUnambiguity.Nullable as Null

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
data DyckAST : Type where
  mt : DyckAST
  bal : DyckAST → DyckAST → DyckAST

open StrongEquivalence
abstractify : Dyck ⊢ Δ DyckAST
abstractify = semact-rec alg _
  where
  alg : Algebra DyckTy (λ _ → Δ DyckAST)
  alg _ = ⊕ᴰ-elim λ where
    nil' → semact-pure mt
    balanced' →
      semact-map (uncurry bal)
        (semact-right
          (semact-concat
            (semact-lift semact-Δ)
            (semact-right (semact-lift semact-Δ))))

flatten : DyckAST → String
flatten mt = []
flatten (bal tr tr') = [ LP ] ++ flatten tr ++ [ RP ] ++ flatten tr'

abstractifyPreservesString-motive =
  ⊕[ (w , tr , e) ∈ (Σ[ w ∈ String ] Σ[ tr ∈ DyckAST ] flatten tr ≡ w) ] ⌈ w ⌉
abstractifyPreservesString : Dyck ⊢ abstractifyPreservesString-motive
abstractifyPreservesString = rec DyckTy alg _
  where
  help : ∀ w w' tr tr' e e' → (＂ LP ＂ ⊗ ⌈ w ⌉) ⊗ ＂ RP ＂ ⊗ ⌈ w' ⌉ ⊢ abstractifyPreservesString-motive
  help w w' tr tr' e e' = σ (w'' , tr'' , e'') ∘g id ,⊗ ⌈⌉-++ w (RP ∷ w') ∘g ⊗-assoc⁻
    where
    w'' = [ LP ] ++ w ++ [ RP ] ++ w'
    tr'' = bal tr tr'
    e'' : flatten tr'' ≡ w''
    e'' = cong₂ (λ u v → LP ∷ u ++ RP ∷ v) e e'

  alg : Algebra DyckTy (λ _ → abstractifyPreservesString-motive)
  alg _ = ⊕ᴰ-elim (λ {
      nil' → σ ([] , mt , refl) ∘g lowerG
    ; balanced' →
       ⊕ᴰ-elim (λ (w' , tr' , e') → ⊕ᴰ-elim (λ (w , tr , e) → help w w' tr tr' e e') ∘g ⊕ᴰ-distL .fun)
       ∘g ⊕ᴰ-distR .fun
       ∘g ⊕ᴰ-distR .fun ,⊗ id
       ∘g ⊗-assoc
       ∘g id ,⊗ id ,⊗ ⊕ᴰ-distR .fun
       ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ lowerG
    })

private
  module AImpU = AImp Uni.Unicode
  module IREU  = IRE  Uni.Unicode
  module LexDU = LexD Uni.Unicode
  module PRDU  = PRD  Uni.Unicode
  module NullU = Null Uni.Unicode

  open AImpU using (ImplicitDeterministicAutomaton ; fail)

  M-LP-uni : ImplicitDeterministicAutomaton ℓ-zero
  M-LP-uni = IREU.litAut Uni.DiscreteUnicodeChar '['

  M-RP-uni : ImplicitDeterministicAutomaton ℓ-zero
  M-RP-uni = IREU.litAut Uni.DiscreteUnicodeChar ']'

  notBothNull-uni :
    (M-LP-uni .ImplicitDeterministicAutomaton.null ≡ false)
    Sum.⊎
    (M-RP-uni .ImplicitDeterministicAutomaton.null ≡ false)
  notBothNull-uni = Sum.inl refl

  LP≢RP : '[' ≡ ']' → Empty.⊥
  LP≢RP = Uni.mkUnicodeCharPath-no '[' ']' refl

  disjointFirsts-uni :
    ∀ (c' : Uni.UnicodeChar) →
      (fail ≡ M-LP-uni .ImplicitDeterministicAutomaton.δᵢ c')
      Sum.⊎
      (fail ≡ M-RP-uni .ImplicitDeterministicAutomaton.δᵢ c')
  disjointFirsts-uni c'
    with Uni.DiscreteUnicodeChar '[' c' | Uni.DiscreteUnicodeChar ']' c'
  ... | no  _ | _     = Sum.inl refl
  ... | yes _ | no  _ = Sum.inr refl
  ... | yes p | yes q = Empty.rec (LP≢RP (p ∙ sym q))

  UM-uni : ImplicitDeterministicAutomaton ℓ-zero
  UM-uni =
    IREU.⊕Aut Uni.DiscreteUnicodeChar
      M-LP-uni M-RP-uni
      notBothNull-uni disjointFirsts-uni

  ¬nullTrace-uni :
    ⟨ NullU.¬Nullable (LexDU.TraceDA UM-uni true (LexDU.q₀DA UM-uni)) ⟩
  ¬nullTrace-uni = LexDU.¬Nullable-TraceDA-init UM-uni refl

  ruleLP-uni : LexDU.LexRule Bracket
  ruleLP-uni = record { autom = M-LP-uni ; action = λ _ → MaybeD.just LP }

  ruleRP-uni : LexDU.LexRule Bracket
  ruleRP-uni = record { autom = M-RP-uni ; action = λ _ → MaybeD.just RP }

  lexicon-uni : LexDU.Lexicon Bracket
  lexicon-uni = ruleLP-uni ∷ ruleRP-uni ∷ []

-- Tokenize a builtin Unicode string into a `Bracket` sequence.
-- Returns `nothing` if any character is neither `[` nor `]`.
tokenizeUnicode : AS.String → MaybeD.Maybe String
tokenizeUnicode s =
  LexDU.runLex UM-uni ¬nullTrace-uni lexicon-uni (AS.primStringToList s)

-- Partial-but-total view: falls back to the empty token list when
-- tokenization fails.  Convenient inside parser test sites because
-- the existing `D.parse?` / `prettyD.parse?` queries can be applied
-- directly: `prettyD.parse? (fromString "[][]")`.
fromString : AS.String → String
fromString s = MaybeD.rec [] (λ toks → toks) (tokenizeUnicode s)

opaque
  unfolding unfoldGrammarDefs LexDU.runLex LexDU.ruleAction
            PRDU.unfoldRecursiveDescentDefs
  eval-lex-uni : Unit
  eval-lex-uni = tt

module D where
  open RunParser DyckParser public

  tokenize-and-accept? : AS.String → Bool
  tokenize-and-accept? s = accept? (fromString s)

  tokenize-and-parse? : AS.String → Type _
  tokenize-and-parse? s = parse? (fromString s)

module prettyD where
  open RunIncompleteParser (abstractify ,⊕p id ∘g DyckParser .Parser.fun) public

  tokenize-and-parse? : AS.String → Type _
  tokenize-and-parse? s = parse? (fromString s)

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
  unfolding unfoldParserDefs genBALANCED
  -- Uncomment these individually to run
  --
  -- Each benchmark below is run with the length checks above
  -- commented out. Those are only there to sanity check size

  -- immediate
  -- _ : D.accept? (mkInput 10) ≡ true
  -- _ = refl

  -- 10s
  _ : D.accept? (mkInput 25) ≡ true
  _ = refl

  -- 10s
  -- _ : D.accept? (mkInput 25 ++ [ RP ]) ≡ false
  -- _ = refl

  -- In principle, this one could be faster but
  -- the structure of the current code iterates
  -- through all of the input, even after going
  -- to a fail state
  -- 10s
  -- _ : D.accept? ([ RP ] ++ mkInput 25) ≡ false
  -- _ = refl

  -- 20s
  -- _ : D.accept? (mkInput 27) ≡ true
  -- _ = refl

  -- 20s
  -- _ : D.accept? ([ RP ] ++ mkInput 27) ≡ false
  -- _ = refl

  -- 35s
  -- _ : D.accept? (mkInput 29) ≡ true
  -- _ = refl

  -- 1m3s seconds
  -- _ : D.accept? (mkInput 31) ≡ true
  -- _ = refl

  -- We can also check against specific trees
  -- the below is written by starting with ? , refl and then C-u C-u C-c C-s to
  -- solve for the normalized parse trees

  _ : D.parse? (mkInput 0)
  _ = (Sum.inl (μ.roll [] (nil' , lift Eq.refl))) , refl

  _ : prettyD.parse? (mkInput 0)
  _ = Sum.inl (mt , tt) , refl

  _ : D.parse? (mkInput 4)
  _ = Sum.inl
       (μ.roll (LP ∷ LP ∷ LP ∷ RP ∷ LP ∷ RP ∷ RP ∷ RP ∷ [])
        (balanced' ,
         ((LP ∷ [] , LP ∷ LP ∷ RP ∷ LP ∷ RP ∷ RP ∷ RP ∷ []) , Eq.refl) ,
         lift Eq.refl ,
         ((LP ∷ LP ∷ RP ∷ LP ∷ RP ∷ RP ∷ [] , RP ∷ []) , Eq.refl) ,
         lift
         (μ.roll (LP ∷ LP ∷ RP ∷ LP ∷ RP ∷ RP ∷ [])
          (balanced' ,
           ((LP ∷ [] , LP ∷ RP ∷ LP ∷ RP ∷ RP ∷ []) , Eq.refl) ,
           lift Eq.refl ,
           ((LP ∷ RP ∷ LP ∷ RP ∷ [] , RP ∷ []) , Eq.refl) ,
           lift
           (μ.roll (LP ∷ RP ∷ LP ∷ RP ∷ [])
            (balanced' ,
             ((LP ∷ [] , RP ∷ LP ∷ RP ∷ []) , Eq.refl) ,
             lift Eq.refl ,
             (([] , RP ∷ LP ∷ RP ∷ []) , Eq.refl) ,
             lift (μ.roll [] (nil' , lift Eq.refl)) ,
             ((RP ∷ [] , LP ∷ RP ∷ []) , Eq.refl) ,
             lift Eq.refl ,
             lift
             (μ.roll (LP ∷ RP ∷ [])
              (balanced' ,
               ((LP ∷ [] , RP ∷ []) , Eq.refl) ,
               lift Eq.refl ,
               (([] , RP ∷ []) , Eq.refl) ,
               lift (μ.roll [] (nil' , lift Eq.refl)) ,
               ((RP ∷ [] , []) , Eq.refl) ,
               lift Eq.refl , lift (μ.roll [] (nil' , lift Eq.refl))))))
           ,
           ((RP ∷ [] , []) , Eq.refl) ,
           lift Eq.refl , lift (μ.roll [] (nil' , lift Eq.refl))))
         ,
         ((RP ∷ [] , []) , Eq.refl) ,
         lift Eq.refl , lift (μ.roll [] (nil' , lift Eq.refl)))) , refl

  _ : prettyD.parse? (mkInput 4)
  _ = Sum.inl (bal (bal (bal mt (bal mt mt)) mt) mt , tt) , refl

  _ : prettyD.parse? (mkInput 10)
  _ = Sum.inl
       (bal
        (bal
         (bal
          (bal
           (bal
            (bal
             (bal
              (bal
               (bal
                (bal
                 (bal
                  (bal
                   (bal
                    (bal
                     (bal
                      (bal
                       (bal
                        (bal (bal (bal (bal mt (bal mt mt)) mt) (bal mt (bal mt mt))) mt)
                        mt)
                       mt)
                      (bal (bal (bal mt (bal mt mt)) mt) (bal mt (bal mt mt))))
                     mt)
                    mt)
                   mt)
                  mt)
                 mt)
                (bal
                 (bal
                  (bal
                   (bal (bal (bal (bal mt (bal mt mt)) mt) (bal mt (bal mt mt))) mt)
                   mt)
                  mt)
                 (bal (bal (bal mt (bal mt mt)) mt) (bal mt (bal mt mt)))))
               mt)
              mt)
             mt)
            mt)
           mt)
          mt)
         mt)
        mt
        , tt) , refl

  -- -- The corresponding non-pretty printed parse tree for Dyck
  -- -- takes 3000 lines to display
  -- _ : D.parse? (mkInput 10)
  -- _ = Sum.inl _ , refl

-- Same parser, but now ran on the output of a lexing pass over Unicode string

opaque
  unfolding unfoldParserDefs genBALANCED eval-lex-uni

  _ : tokenizeUnicode "" ≡ MaybeD.just []
  _ = refl

  _ : tokenizeUnicode "[]" ≡ MaybeD.just (LP ∷ RP ∷ [])
  _ = refl

  _ : tokenizeUnicode "[[]]" ≡ MaybeD.just (LP ∷ LP ∷ RP ∷ RP ∷ [])
  _ = refl

  _ : tokenizeUnicode "[][[]]" ≡ MaybeD.just (LP ∷ RP ∷ LP ∷ LP ∷ RP ∷ RP ∷ [])
  _ = refl

  _ : D.tokenize-and-accept? "" ≡ true
  _ = refl

  _ : D.tokenize-and-accept? "[]" ≡ true
  _ = refl

  _ : D.tokenize-and-accept? "[][]" ≡ true
  _ = refl

  _ : D.tokenize-and-accept? "[[]]" ≡ true
  _ = refl

  _ : D.tokenize-and-accept? "][" ≡ false
  _ = refl

  _ : D.tokenize-and-accept? "[" ≡ false
  _ = refl

  _ : prettyD.tokenize-and-parse? "[]"
  _ = Sum.inl (bal mt mt , tt) , refl

  _ : prettyD.tokenize-and-parse? "[][]"
  _ = Sum.inl (bal mt (bal mt mt) , tt) , refl

  _ : prettyD.tokenize-and-parse? "[[]]"
  _ = Sum.inl (bal (bal mt mt) mt , tt) , refl

  _ : prettyD.tokenize-and-parse? "[[][]]"
  _ = Sum.inl (bal (bal mt (bal mt mt)) mt , tt) , refl
