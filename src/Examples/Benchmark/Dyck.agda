{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Benchmark.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod
import Cubical.Data.Sum as Sum
import Cubical.Data.Equality as Eq

open import Cubical.Data.List hiding (rec)
open import Cubical.Data.Bool using (true ; false)

open import Examples.Dyck
  hiding (LP ; RP)
  renaming ([ to LP ; ] to RP)

open import Grammar Alphabet renaming (NIL to *NIL)
open import Term Alphabet
open import Parser Alphabet

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

-- TODO need to pull in Nathan's old semantic-actions branch and give a generic
-- interface for semantic actions
ΔDyckAST : Grammar _
ΔDyckAST = ⊕[ tr ∈ DyckAST ] ⊤

mkAST : ∀ {ℓA}{A : Grammar ℓA} → DyckAST → A ⊢ ΔDyckAST
mkAST tr = σ tr ∘g ⊤-intro

open StrongEquivalence
abstractify : Dyck ⊢ ΔDyckAST
abstractify = rec DyckTy alg _
  where
  alg : Algebra DyckTy (λ _ → ΔDyckAST)
  alg _ = ⊕ᴰ-elim (λ {
      nil' → mkAST mt
    ; balanced' →
       ⊕ᴰ-elim (λ tr' → ((⊕ᴰ-elim λ tr → mkAST (bal tr tr')) ∘g ⊕ᴰ-distR .fun) ∘g id ,⊗ ⊕ᴰ-distR .fun)
       ∘g ⊕ᴰ-distR .fun
       ∘g id ,⊗ ⊕ᴰ-distL .fun
       ∘g id ,⊗ id ,⊗ ⊕ᴰ-distR .fun
       ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ lowerG })

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

module D = RunParser DyckParser
module prettyD = RunIncompleteParser (abstractify ,⊕p id ∘g DyckParser .Parser.fun)

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
  _ = Sum.inl (bal mt (bal mt (bal (bal mt mt) mt)) , tt) , refl

  _ : prettyD.parse? (mkInput 10)
  _ = Sum.inl
       (bal mt
        (bal mt
         (bal mt
          (bal mt
           (bal mt
            (bal mt
             (bal mt
              (bal mt
               (bal
                (bal (bal (bal (bal mt mt) mt) (bal mt (bal (bal mt mt) mt)))
                 (bal mt
                  (bal mt
                   (bal mt
                    (bal (bal (bal mt mt) mt) (bal mt (bal (bal mt mt) mt)))))))
                (bal mt
                 (bal mt
                  (bal mt
                   (bal mt
                    (bal mt
                     (bal (bal (bal (bal mt mt) mt) (bal mt (bal (bal mt mt) mt)))
                      (bal mt
                       (bal mt
                        (bal mt
                         (bal (bal (bal mt mt) mt)
                          (bal mt (bal (bal mt mt) mt))))))))))))))))))))
        , tt) , refl

  -- The corresponding non-pretty printed parse tree for Dyck takes 3000 lines to display
  _ : D.parse? (mkInput 10)
  _ = Sum.inl _ , refl
