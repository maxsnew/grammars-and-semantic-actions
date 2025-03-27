{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool hiding (_⊕_ ;_or_)
import Cubical.Data.Equality as Eq
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Maybe hiding (rec)
open import Cubical.Data.Sum as Sum using (_⊎_ ; isSet⊎)
open import Cubical.Data.FinSet
open import Cubical.Data.Unit

private
  variable
    ℓA : Level

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

open import Grammar Alphabet renaming (NIL to *NIL)
open import Grammar.Coherence Alphabet
open import Automata.Deterministic Alphabet
open import Parser Alphabet
open import Term Alphabet

open StrongEquivalence

data DyckTag : Type ℓ-zero where
  nil' balanced' : DyckTag

isSetDyckTag : isSet DyckTag
isSetDyckTag = isSetRetract enc dec retr isSetBool where
  enc : DyckTag → Bool
  enc nil' = false
  enc balanced' = true
  dec : Bool → DyckTag
  dec false = nil'
  dec true = balanced'
  retr : (x : DyckTag) → dec (enc x) ≡ x
  retr nil' = refl
  retr balanced' = refl

DyckTy : Unit → Functor Unit
DyckTy _ = ⊕e DyckTag (λ
  { nil' → k ε
  ; balanced' → (k (literal [)) ⊗e (Var _) ⊗e (k (literal ]) ⊗e (Var _)) })

Dyck : Grammar ℓ-zero
Dyck = μ DyckTy _

isSetGrammarDyck : isSetGrammar Dyck
isSetGrammarDyck = isSetGrammarμ DyckTy
  (λ _ → isSetDyckTag ,
    (λ { nil' → isSetGrammarε
       ; balanced' → isSetGrammarLiteral _ , (tt* , (isSetGrammarLiteral _ , tt*)) }))
  tt

NIL : ε ⊢ Dyck
NIL = roll ∘g σ nil' ∘g liftG

BALANCED : literal [ ⊗ Dyck ⊗ literal ] ⊗ Dyck ⊢ Dyck
BALANCED = roll ∘g σ balanced' ∘g liftG ,⊗ liftG ,⊗ liftG ,⊗ liftG

appendAlg : Algebra DyckTy λ _ → Dyck ⊸ Dyck
appendAlg tt = ⊕ᴰ-elim λ
  { nil' → ⊸-intro ⊗-unit-l ∘g lowerG
  ; balanced' → ⊸-intro (BALANCED
    ∘g lowerG ,⊗ (⊸-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻)
       ,⊗ lowerG ,⊗ (⊸-app ∘g lowerG ,⊗ id)
    ∘g ⊗-assoc⁻4)
  }

append' : Dyck ⊢ Dyck ⊸ Dyck
append' = rec _ appendAlg _

append : Dyck ⊗ Dyck ⊢ Dyck
append = ⊸-intro⁻ append'

append-nil-r' : ⊸-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g append' ≡ id
append-nil-r' =
  ind-id' DyckTy (compHomo DyckTy (initialAlgebra DyckTy) appendAlg (initialAlgebra DyckTy)
    ((λ _ → ⊸-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) , λ _ → pf)
    (recHomo DyckTy appendAlg))
    _
  where
    opaque
      unfolding ⊗-intro ⊗-unit-r⁻ ⊗-assoc⁻
      pf : (⊸-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ∘g appendAlg _
         ≡ roll ∘g map (DyckTy _) (λ _ → ⊸-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻)
      pf = ⊕ᴰ≡ _ _ (λ
        { nil' →
        (⊸-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g ⊸-intro ⊗-unit-l ∘g lowerG)
          ≡⟨ (λ i → ⊸-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻⊗-intro {f = (⊸-intro ⊗-unit-l)} i ∘g lowerG) ⟩
        (⊸-app ∘g id ,⊗ NIL ∘g ⊸-intro ⊗-unit-l ,⊗ id ∘g ⊗-unit-r⁻ ∘g lowerG)
          ≡⟨ refl ⟩
        (⊸-app ∘g (⊸-intro ⊗-unit-l ,⊗ id) ∘g (id ,⊗ NIL) ∘g ⊗-unit-r⁻ ∘g lowerG)
          ≡⟨ cong (_∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g lowerG) (⊸-β ⊗-unit-l) ⟩
        (⊗-unit-l ∘g (id ,⊗ NIL) ∘g ⊗-unit-r⁻ ∘g lowerG)
          ≡⟨ cong (_∘g ⊗-unit-r⁻ ∘g lowerG) (sym (⊗-unit-l⊗-intro NIL)) ⟩
        (NIL ∘g ⊗-unit-l ∘g ⊗-unit-r⁻ ∘g lowerG)
          ≡⟨ cong (NIL ∘g_) (cong (_∘g lowerG) ⊗-unit-lr⁻) ⟩
        NIL ∘g lowerG
        ∎
        ; balanced' →
        cong ((⊸-app ∘g id ,⊗ NIL) ∘g_) ⊗-unit-r⁻⊗-intro
        ∙ cong (_∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) (⊸-β _)
        ∙ cong ((BALANCED
                 ∘g id ,⊗ (⊸-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ id ,⊗ (⊸-app ∘g id ,⊗ NIL)
                 ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ id) ∘g_)
               ⊗-assoc⁻4⊗-unit-r⁻
        })

-- Need this lemma for the retract property below
append-nil-r : append ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ≡ id
append-nil-r = goal where
  opaque
    unfolding ⊗-intro ⊗-unit-r⁻
    goal : append ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ≡ id
    goal = append-nil-r'

{--
-- An automaton to recognize the Dyck grammar. We show further down in this file that
-- the traces of this machine are *strongly equivalent* to the Dyck grammar. We combine that
-- equivalence with a parser for the traces through this machine to create a parser for
-- the Dyck grammar
--
-- There is a state in this machine for each natural number, along with one additional state
-- to serve as a "fail state". Here that is encoded with as Maybe ℕ where "nothing" corresponds
-- to the fail state
--
-- Intuitively, the natural number takes on the role of the stack. The state encodes the number
-- of opening parens that are not currently matched with a closing paren. Each natural number state
-- then measures how far away from being balanced the current partial parse is. Therefore,
-- only state 0 should be accepting.
--
--            [         [         [         [
--          →-→-→     →-→-→     →-→-→     →-→-→
--         /     \   /     \   /     \   /     \
--       0         1         2         3        ⋯
--       | \     /   \     /   \     /   \     /
--       ↓  ←-←-←     ←-←-←     ←-←-←     ←-←-←
--       |    ]         ]         ]         ]
--     ] ↓
--       |
--       ↓
--       |
--      fail
--
--}
DyckAut : DeterministicAutomaton (Maybe ℕ)
DyckAut .DeterministicAutomaton.init = just 0
DyckAut .DeterministicAutomaton.isAcc nothing = false
DyckAut .DeterministicAutomaton.isAcc (just zero) = true
DyckAut .DeterministicAutomaton.isAcc (just (suc n)) = false
DyckAut .DeterministicAutomaton.δ nothing c = nothing
DyckAut .DeterministicAutomaton.δ (just n) [ = just (suc n)
DyckAut .DeterministicAutomaton.δ (just zero) ] = nothing
DyckAut .DeterministicAutomaton.δ (just (suc n)) ] = just n

open DeterministicAutomaton DyckAut

LP = [
RP = ]

FAIL : string ⊢ Trace false nothing
FAIL = fold*r char
  (roll ∘g σ stop ∘g σ (lift Eq.refl) ∘g liftG ∘g liftG)
  (⊕ᴰ-elim (λ c → roll ∘g σ step ∘g σ (lift c) ∘g (liftG ∘g liftG) ,⊗ liftG) ∘g ⊕ᴰ-distL .fun)

EOF : ε ⊢ Trace true (just 0)
EOF = roll ∘g σ stop ∘g σ (lift Eq.refl) ∘g liftG ∘g liftG

OPEN : ∀ {n b} → literal [ ⊗ Trace b (just (suc n)) ⊢ Trace b (just n)
OPEN = roll ∘g σ step ∘g σ (lift [) ∘g (liftG ∘g liftG) ,⊗ liftG

CLOSE : ∀ {n b} → literal ] ⊗ Trace b (just n) ⊢ Trace b (just (suc n))
CLOSE = roll ∘g σ step ∘g σ (lift ]) ∘g (liftG ∘g liftG) ,⊗ liftG

LEFTOVERS : ∀ {n} → ε ⊢ Trace false (just (suc n))
LEFTOVERS = roll ∘g σ stop ∘g σ (lift Eq.refl) ∘g liftG ∘g liftG

UNEXPECTED : literal ] ⊗ Trace false nothing ⊢ Trace false (just 0)
UNEXPECTED = roll ∘g σ step ∘g σ (lift ]) ∘g (liftG ∘g liftG) ,⊗ liftG

failRejects : Trace true nothing ⊢ ⊥
failRejects = rec _ the-alg nothing
  where
  ⟦_⟧n : Maybe ℕ → Grammar ℓ-zero
  ⟦ nothing ⟧n = ⊥
  ⟦ just n ⟧n = ⊤

  the-alg : Algebra (TraceTy true) ⟦_⟧n
  the-alg nothing = ⊕ᴰ-elim λ where
    stop → ⊕ᴰ-elim λ ()
    step → ⊕ᴰ-elim λ _ → ⊗⊥ ∘g id ,⊗ lowerG
  the-alg (just x) = ⊤-intro

{-
  Next, we establish that Dyck and Trace true zero are strongly equivalent.

  To prove this inductively, we more generally prove that Trace true n
  is strongly equivalent to a "GenDyck n" that is an analogously
  "unbalanced" Dyck tree.
-}
GenDyck : ℕ → Grammar _
GenDyck 0         = Dyck
GenDyck (suc n-1) = Dyck ⊗ literal RP ⊗ GenDyck n-1

isSetGrammarGenDyck : ∀ n → isSetGrammar (GenDyck n)
isSetGrammarGenDyck zero = isSetGrammarDyck
isSetGrammarGenDyck (suc n) =
  isSetGrammar⊗ isSetGrammarDyck
    (isSetGrammar⊗ (isSetGrammarLiteral _) (isSetGrammarGenDyck n))

-- We extend the balanced constructor and append to our unbalanced
-- trees
opaque
  genBALANCED : ∀ n → literal LP ⊗ Dyck ⊗ literal RP ⊗ GenDyck n ⊢ GenDyck n
  genBALANCED zero   = BALANCED
  genBALANCED (suc n) = BALANCED ,⊗ id ∘g ⊗-assoc4

upgradeBuilder : ∀ n → (Dyck ⊸ Dyck) ⊢ GenDyck n ⊸ GenDyck n
upgradeBuilder zero = id
upgradeBuilder (suc n) = ⊸-intro (⊸-app ,⊗ id ∘g ⊗-assoc)

opaque
  unfolding ⊗-intro genBALANCED
  upgradeNilBuilder :
    ∀ n (f : Trace true (just n) ⊢ GenDyck n)
       → (⊸-app ∘g id ,⊗ f) ∘g
        (upgradeBuilder n ∘g ⊸-intro ⊗-unit-l) ,⊗ id
        ≡ f ∘g ⊗-unit-l
  upgradeNilBuilder zero f =
    cong (_∘g (id ,⊗ f)) (⊸-β _)
    ∙ sym (⊗-unit-l⊗-intro _)
  upgradeNilBuilder (suc n) f =
    cong (_∘g ((⊸-intro ⊗-unit-l)) ,⊗ f) (⊸-β _)
    ∙ cong ((⊸-app ,⊗ id) ∘g_) (cong (_∘g (id ,⊗ f)) (⊗-assoc⊗-intro {f' = id}{f'' = id}))
    ∙ ( (λ i → (⊸-β ⊗-unit-l i) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ f))
    ∙ cong (_∘g (id ,⊗ f)) (cong ((⊗-unit-l ,⊗ id) ∘g_) (sym (⊗-assoc⊗-intro {f' = id}{f'' = id})))
    ∙ cong (_∘g id ,⊗ f)
        (⊗-unit-l⊗-assoc isSetGrammarDyck
          (isSetGrammar⊗ (isSetGrammarLiteral _) (isSetGrammarGenDyck n)))
    ∙ sym (⊗-unit-l⊗-intro _)

  upgradeBalancedBuilder :
    ∀ n (f : Trace true (just n) ⊢ GenDyck n)
    → (⊸-app ∘g id ,⊗ f)
      ∘g (upgradeBuilder n ∘g ⊸-intro (
          BALANCED
          ∘g lowerG {ℓ-zero} ,⊗
             (⊸-app ∘g lowerG{ℓ-zero} ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗
             lowerG {ℓ-zero} ,⊗ (⊸-app ∘g lowerG {ℓ-zero} ,⊗ id)
          ∘g ⊗-assoc⁻4))
         ,⊗ id
      ≡ genBALANCED n
        ∘g id ,⊗ (⊸-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
        ∘g id ,⊗ id ,⊗ id ,⊗ ⊸-app
        ∘g lowerG ,⊗ (upgradeBuilder (suc n) ∘g lowerG) ,⊗
             lowerG ,⊗ ((upgradeBuilder n) ∘g lowerG) ,⊗ f
        ∘g ⊗-assoc⁻4
  upgradeBalancedBuilder zero f =
    cong (_∘g (id ,⊗ f)) (⊸-β _)
    ∙ (λ i → BALANCED
       ∘g lowerG ,⊗ (⊸-app ∘g id ,⊗ NIL
                     ∘g ⊗-unit-r⁻⊗-intro {f = lowerG} (~ i)) ,⊗ lowerG ,⊗ (⊸-app ∘g lowerG ,⊗ id)
       ∘g ⊗-assoc⁻4
       ∘g id ,⊗ f
      )
    ∙ (λ i → BALANCED ∘g
      lowerG ,⊗ (⊸-app ∘g id ,⊗ NIL) ,⊗ id ∘g
      id ,⊗ ⊗-assoc⊗-unit-l⁻ (~ i) ∘g
      id ,⊗ id ,⊗ id ,⊗ ⊸-app ∘g
      id ,⊗ lowerG ,⊗ lowerG ,⊗ (id ∘g lowerG) ,⊗ id
      ∘g ⊗-assoc⁻4
      ∘g id ,⊗ f)
    ∙ (λ i → BALANCED
      ∘g id ,⊗ ⊸-app ,⊗ id
      ∘g id ,⊗ ((id ,⊗ NIL) ,⊗ id)
      ∘g id ,⊗ (⊗-assoc ∘g id ,⊗ ⊗-unit-l⁻)  --
      ∘g id ,⊗ id ,⊗ id ,⊗ ⊸-app
      ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (id ∘g lowerG) ,⊗ id
      ∘g ⊗-assoc⁻4⊗-intro {f = id}{f' = id}{f'' = id}{f''' = id}{f'''' = f} i
      )
    ∙ (λ i → BALANCED
      ∘g id ,⊗ (⊸-app ,⊗ id)
      ∘g id ,⊗ ⊗-assoc⊗-intro {f = id}{f' = NIL}{f'' = id} (~ i)
      ∘g id ,⊗ (id ,⊗ ⊗-unit-l⁻)
      ∘g id ,⊗ id ,⊗ id ,⊗ ⊸-app
      ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (id ∘g lowerG) ,⊗ f ∘g ⊗-assoc⁻4
          )
    ∙ λ i → BALANCED
      ∘g id ,⊗ (⊸-β (⊸-app ,⊗ id ∘g ⊗-assoc) (~ i))
      ∘g id ,⊗ (id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
      ∘g id ,⊗ id ,⊗ id ,⊗ ⊸-app
      ∘g lowerG ,⊗ (lowerG) ,⊗ lowerG ,⊗ (id ∘g lowerG) ,⊗ f
      ∘g ⊗-assoc⁻4
  upgradeBalancedBuilder (suc n) f =
    (λ i →
      (⊸-β (⊸-app ,⊗ id ∘g ⊗-assoc) i) ∘g
        (⊸-intro (BALANCED ∘g lowerG ,⊗
                              (⊸-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗
                              lowerG ,⊗ (⊸-app ∘g lowerG ,⊗ id)
        ∘g ⊗-assoc⁻4))
        ,⊗ f)
    ∙ (λ i →
      ⊸-app ,⊗ id
      ∘g ⊗-assoc⊗-intro {f = ⊸-intro (BALANCED ∘g lowerG ,⊗
                             (⊸-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG ,⊗
                             (⊸-app ∘g lowerG ,⊗ id) ∘g ⊗-assoc⁻4)}{f' = id}{f'' = id} i
      ∘g id ,⊗ f)
    ∙ (λ i →
        (⊸-β (BALANCED
             ∘g lowerG ,⊗ (⊸-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗
                lowerG ,⊗ (⊸-app ∘g lowerG ,⊗ id) ∘g ⊗-assoc⁻4) i) ,⊗ id
        ∘g ⊗-assoc
        ∘g id ,⊗ f
      )
    ∙ (λ i →
       BALANCED ,⊗ id
       ∘g (lowerG ,⊗ (⊸-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG
                  ,⊗ (⊸-app ∘g lowerG ,⊗ id)) ,⊗ id
       ∘g ⊗-assoc⁻4⊗-assoc
          (isSetGrammarLift (isSetGrammarLiteral _))
          (isSetGrammarLift (isSetGrammar⊸ isSetGrammarDyck))
          (isSetGrammarLift (isSetGrammarLiteral _))
          (isSetGrammarLift (isSetGrammar⊸ isSetGrammarDyck))
          isSetGrammarDyck
          (isSetGrammar⊗ (isSetGrammarLiteral _) (isSetGrammarGenDyck n))
          i
       ∘g id ,⊗ f)
    ∙ (λ i → BALANCED ,⊗ id
        ∘g ⊗-assoc4⊗-intro {f = lowerG}{f' = ⊸-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻}{f'' = lowerG}
                           {f''' = (⊸-app ∘g lowerG ,⊗ id)}{f'''' = id} (~ i)
        ∘g id ,⊗ id ,⊗ id ,⊗ ⊗-assoc
        ∘g ⊗-assoc⁻4
        ∘g id ,⊗ f)
    ∙ (λ i → BALANCED ,⊗ id
        ∘g ⊗-assoc4
        ∘g lowerG ,⊗ (⊸-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗
             lowerG ,⊗ ((⊸-app ∘g lowerG ,⊗ id) ,⊗ id)
        ∘g id ,⊗ id ,⊗ id ,⊗ ⊗-assoc
        ∘g ⊗-assoc⁻4⊗-intro {f = id}{f' = id}{f'' = id}{f''' = id}{f'''' = f} i
        )
    ∙ (λ i → BALANCED ,⊗ id
        ∘g ⊗-assoc4
        ∘g lowerG ,⊗ ((⊸-app ∘g (id ,⊗ NIL) ∘g ⊗-unit-r⁻⊗-intro {f = lowerG} (~ i)) ,⊗
            lowerG ,⊗ ((⊸-app ∘g lowerG ,⊗ id) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ f))
        ∘g ⊗-assoc⁻4)
    ∙ (
      λ i → BALANCED ,⊗ id
        ∘g ⊗-assoc4
        ∘g id ,⊗ (⊸-app ,⊗ id)
        ∘g id ,⊗ ((id ,⊗ NIL) ,⊗ id)
        ∘g id ,⊗ ⊗-assoc⊗-unit-l⁻ (~ i)
        ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ ((⊸-app ∘g lowerG ,⊗ id) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ f)
        ∘g ⊗-assoc⁻4
      )
    ∙ (λ i →
        BALANCED ,⊗ id
        ∘g ⊗-assoc4
        ∘g id ,⊗ (⊸-app ,⊗ id)
        ∘g id ,⊗ (⊗-assoc⊗-intro {f = id}{f' = NIL}{f'' = id} (~ i))
        ∘g id ,⊗ (id ,⊗ ⊗-unit-l⁻)
        ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗
            (⊸-app ,⊗ id ∘g (⊗-assoc⊗-intro {f = lowerG}{f' = id}{f'' = id} (~ i)) ∘g id ,⊗ f)
        ∘g ⊗-assoc⁻4
      )
    ∙ λ i → (BALANCED ,⊗ id ∘g ⊗-assoc4) ∘g
      id ,⊗ (⊸-β (⊸-app ,⊗ id ∘g ⊗-assoc) (~ i) ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻)) ∘g
      lowerG ,⊗ (lowerG) ,⊗ lowerG ,⊗ (⊸-β (⊸-app ,⊗ id ∘g ⊗-assoc) (~ i) ∘g lowerG ,⊗ f)
      ∘g ⊗-assoc⁻4

genAppend' : Dyck ⊢ &[ n ∈ _ ] (GenDyck n ⊸ GenDyck n)
genAppend' = (&ᴰ-intro upgradeBuilder) ∘g append'

genAppend : ∀ n → Dyck ⊗ GenDyck n ⊢ GenDyck n
genAppend zero    = append
genAppend (suc _) = ⊸2⊗ (⊸2-intro-ε append)

GenDyck' : Maybe ℕ → Grammar ℓ-zero
GenDyck' nothing = ⊥
GenDyck' (just n) = GenDyck n

{- First, we construct a GenDyck n from a Trace n -}
genMkTreeAlg : Algebra (TraceTy true) GenDyck'
genMkTreeAlg nothing = ⊕ᴰ-elim λ where
  stop → ⊕ᴰ-elim (λ ())
  step → ⊕ᴰ-elim (λ (lift c) → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ lowerG)
genMkTreeAlg (just n) = ⊕ᴰ-elim λ where
  stop → Nat.elim {A = λ n → ⊕[ _ ∈ Lift (true Eq.≡ isAcc (just n)) ] (LiftG ℓ-zero ε*) ⊢ GenDyck n}
      (⊕ᴰ-elim λ where (lift Eq.refl) → NIL ∘g lowerG ∘g lowerG)
      (λ n' _ → ⊕ᴰ-elim λ ())
      n
  step → ⊕ᴰ-elim λ where
    (lift ]) → Nat.elim {A = λ n → ＂ ] ＂ ⊗ GenDyck' (δ (just n) ]) ⊢ GenDyck n}
        (⊥-elim ∘g ⊗⊥)
        (λ n' _ → NIL ,⊗ id ∘g ⊗-unit-l⁻)
        n
      ∘g (lowerG ∘g lowerG) ,⊗ lowerG
    (lift [) → genBALANCED n ∘g (lowerG ∘g lowerG) ,⊗ lowerG

genMkTree : ∀ n → Trace true (just n) ⊢ GenDyck n
genMkTree n = rec (TraceTy _) genMkTreeAlg (just n)

genMkTree' : (n : Maybe ℕ) → Trace true n ⊢ GenDyck' n
genMkTree' n = rec (TraceTy _) genMkTreeAlg _

mkTree : Trace true (just 0) ⊢ Dyck
mkTree = genMkTree 0

opaque
  unfolding ⊗-intro
  genMkTree-β-OPEN : ∀ {n} → genMkTree n ∘g OPEN ≡ genBALANCED n ∘g id ,⊗ genMkTree (suc n)
  genMkTree-β-OPEN {n} = refl

-- {-

--   Next, we extract the trace from an Dyck and then iterate this to
--   extract one from a GenDyck.

--   The trick to defining this by structural recursion is to map each
--   Dyck recursively to a "TraceBuilder", a linear function that
--   takes a trace to its right and "piles" the characters from the tree
--   onto the trace. Since an Dyck is balanced, it doesn't affect the
--   state n.

-- -}
TraceBuilder : Unit → Grammar ℓ-zero
TraceBuilder _ = &[ n ∈ ℕ ] (Trace true (just n) ⊸ Trace true (just n))

buildTraceAlg : Algebra DyckTy TraceBuilder
buildTraceAlg _ = ⊕ᴰ-elim λ where
  nil' → &ᴰ-intro λ n → ⊸-intro-ε id ∘g lowerG
  balanced' → &ᴰ-intro λ n → ⊸-intro (
      -- OPEN, making a Trace n
      OPEN
      -- build a Trace (suc n) with the left subtree
      ∘g id ,⊗ (⊸-app ∘g π (suc n) ,⊗ id)
      -- CLOSE, making a Trace (suc n)
      ∘g id ,⊗ id ,⊗ CLOSE
       -- build a Trace n with the right subtree
      ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-app ∘g π n ,⊗ id)
       -- reassoc the builder arg to the right, and lower everything else
      ∘g ⊗-assoc⁻4
      ∘g (lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ lowerG) ,⊗ id)

buildTrace : Dyck ⊢ TraceBuilder _
buildTrace = rec DyckTy buildTraceAlg _

-- we then extend the builder to generalized trees, which *adds*
-- closed parens to the trace.
genBuildTrace : ∀ m → GenDyck m ⊢ &[ n ∈ _ ] (Trace true (just n) ⊸ Trace true (just (m + n)))
genBuildTrace zero = buildTrace
genBuildTrace (suc m) =
  &ᴰ-intro λ n → ⊸-intro
  -- build using the left subtree
  ((⊸-app ∘g (π (suc (m + n)) ∘g buildTrace) ,⊗ id)
  -- CLOSE the trace, to make is (suc (m + n))
  ∘g id ,⊗ CLOSE
  -- recursively build using the right subtree
  ∘g id ,⊗ id ,⊗ (⊸-app ∘g (π n ∘g genBuildTrace m) ,⊗ id)
  -- reassoc everything
  ∘g ⊗-assoc⁻3
  )

{-

  Here is the informal inductive argument
  d : Dyck ⊢ (λ& n → λ⊸ t → genMkTree n (buildTrace n d t))
                ≡ (λ& n → λ⊸ t → genAppend' n d (genMkTree n t))

  By induction on d

  n:ℕ ; e : ε , t : Trace n ⊢
    genMkTree n (buildTrace n (nil(e)) t)
    ≡ genMkTree n t
    ≡ genAppend' n nil(e) (genMkTree n t)  [ by defn of genAppend' ]

  n:ℕ ; lp : LP , d₁ : Dyck , rp : RP , d₂ : Dyck ⊢
    genMkTree n (buildTrace n (balanced(lp, d₁, rp, d₂)) t)
    ≡ genMkTree n (open lp (buildTrace (suc n) d₁ (close rp (buildTrace n d₂ t))))                [ defn of buildTrace ]
    ≡ genBALANCED n lp (genMkTree (suc n) (buildTrace (suc n) d₁ (close rp (buildTrace n d₂ t)))) [ defn of genMkTree and buildTrace ]
    ≡ genBALANCED n lp (genAppend' (suc n) d₁ (genMkTree (suc n) (close rp (buildTrace n d₂ t)))) [ by inductive hypothese for d₁ ]
    ≡ genBALANCED n lp (genAppend' (suc n) d₁ (nil(), rp, genMkTree n (buildTrace n d₂ t)))       [ defn of genMkTree ]
    ≡ genBALANCED n lp (genAppend' (suc n) d₁ (nil(), rp, genMkTree n (buildTrace n d₂ t)))       [ defn of genMkTree ]
    ≡ genBALANCED n lp ((append d₁ nil()), rp, genMkTree n (buildTrace n d₂ t))                   [ by append-nil-r ]
    ≡ genBALANCED n lp (d₁, rp, genMkTree n (buildTrace n d₂ t))                                  [ by inductive hypothesis for d₂ ]
    ≡ genBALANCED n lp (d₁, rp, genAppend' n d₂ (genMkTree n t))                                                [ defn of genAppend' ]
    ≡ genAppend' n (balanced(lp, d₁, rp, d₂)) (genMkTree n t)

  We use equalizers to give us this induction principle. It's not
  clear whether you can prove this "directly" using the initial
  algebra properties without using equalizers.
-}

lhs rhs : Dyck ⊢ &[ n ∈ _ ] (Trace true (just n) ⊸ GenDyck n)
lhs = (&ᴰ-intro λ n → ⊸-intro (genMkTree n ∘g ⊸-app) ∘g π n) ∘g buildTrace
rhs = ((&ᴰ-intro λ n → ⊸-intro (⊸-app ∘g id ,⊗ genMkTree n) ∘g π n) ∘g genAppend')

opaque
  unfolding ⊗-intro
  pf : lhs ∘g roll ∘g map (DyckTy _) (λ _ → eq-π lhs rhs) ≡
       rhs ∘g roll ∘g map (DyckTy _) (λ _ → eq-π _ _)
  pf = ⊕ᴰ≡ _ _ λ where
    nil' → &ᴰ≡ _ _ λ n →
      ⊸-intro-natural
      ∙ cong ⊸-intro ((λ i → genMkTree n ∘g ⊸-β ⊗-unit-l i ∘g lowerG ,⊗ id)
                    ∙ (λ i → upgradeNilBuilder n (genMkTree n) (~ i) ∘g lowerG ,⊗ id))
      ∙ sym ⊸-intro-natural
    balanced' → &ᴰ≡ _ _ λ n →
      ⊸-intro-natural
      ∙ cong ⊸-intro (
          (λ i → genMkTree n
            ∘g ⊸-β (OPEN
              ∘g id ,⊗ (⊸-app ∘g π (suc n) ,⊗ id)
              ∘g id ,⊗ id ,⊗ CLOSE
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-app ∘g π n ,⊗ id)
              ∘g ⊗-assoc⁻4
              ∘g (lowerG ,⊗ lowerG {ℓ-zero} ,⊗ lowerG ,⊗ lowerG {ℓ-zero}) ,⊗ id) i
              ∘g (id ,⊗ (liftG {ℓ-zero} ∘g buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id
                     ,⊗ ((liftG {ℓ-zero} ∘g buildTrace ∘g eq-π lhs rhs ∘g lowerG))) ,⊗ id)
          ∙ (λ i → genMkTree-β-OPEN i
              ∘g id ,⊗ (⊸-app ∘g π (suc n) ,⊗ id)
              ∘g id ,⊗ id ,⊗ CLOSE
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-app ∘g π n ,⊗ id)
              ∘g ⊗-assoc⁻4
              ∘g (lowerG ,⊗ lowerG {ℓ-zero} ,⊗ lowerG ,⊗ lowerG {ℓ-zero}) ,⊗ id
              ∘g (id ,⊗ (liftG {ℓ-zero} ∘g buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id
                     ,⊗ ((liftG {ℓ-zero} ∘g buildTrace ∘g eq-π lhs rhs ∘g lowerG))) ,⊗ id
              )
          ∙ (λ i → genBALANCED n
              ∘g id ,⊗ genMkTree (suc n)
              ∘g id ,⊗ (⊸-app ∘g π (suc n) ,⊗ id)
              ∘g id ,⊗ id ,⊗ CLOSE
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-app ∘g π n ,⊗ id)
              ∘g ⊗-assoc⁻4⊗-intro {f = lowerG}
                                  {f' = buildTrace ∘g eq-π lhs rhs ∘g lowerG}{f'' = lowerG}
                                  {f''' = buildTrace ∘g eq-π lhs rhs ∘g lowerG}{f'''' = id} i
              )
          ∙ (λ i → genBALANCED n
              ∘g id ,⊗ (⊸-β (genMkTree (suc n) ∘g ⊸-app) (~ i) ∘g
                            (π (suc n) ∘g (buildTrace ∘g eq-π lhs rhs)) ,⊗ id)
              ∘g id ,⊗ id ,⊗ CLOSE
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-app ∘g π n ,⊗ id)
              ∘g (lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id)
              ∘g ⊗-assoc⁻4)
          ∙ (λ i → genBALANCED n
              ∘g id ,⊗ (⊸-app ∘g (π (suc n) ∘g eq-π-pf lhs rhs i) ,⊗ id)
              ∘g id ,⊗ id ,⊗ CLOSE
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-app ∘g π n ,⊗ id)
              ∘g (lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id)
              ∘g ⊗-assoc⁻4)
          ∙ (λ i → genBALANCED n
              ∘g id ,⊗ (⊸-β (⊸-app ∘g id ,⊗ genMkTree (suc n)) i ∘g (π (suc n) ∘g genAppend') ,⊗ id)
              ∘g id ,⊗ id ,⊗ CLOSE
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-app ∘g π n ,⊗ id)
              ∘g (lowerG ,⊗ (eq-π lhs rhs ∘g lowerG) ,⊗ lowerG ,⊗
                   (buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id)
              ∘g ⊗-assoc⁻4)
          ∙ (λ i → genBALANCED n
              ∘g id ,⊗ (⊸-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-β (genMkTree n ∘g ⊸-app) (~ i) ∘g
                                    (π n ∘g buildTrace ∘g eq-π lhs rhs) ,⊗ id)
              ∘g (lowerG ,⊗ (upgradeBuilder (suc n) ∘g
                             append' ∘g eq-π lhs rhs ∘g lowerG) ,⊗ lowerG ,⊗ lowerG ,⊗ id)
              ∘g ⊗-assoc⁻4)
          ∙ ((λ i → genBALANCED n
              ∘g id ,⊗ (⊸-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-app ∘g (π n ∘g eq-π-pf lhs rhs i) ,⊗ id)
              ∘g (lowerG ,⊗ (upgradeBuilder (suc n) ∘g append' ∘g
                             eq-π lhs rhs ∘g lowerG) ,⊗ lowerG ,⊗ lowerG ,⊗ id)
              ∘g ⊗-assoc⁻4))
          ∙ ((λ i → genBALANCED n
              ∘g id ,⊗ (⊸-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
              ∘g id ,⊗ id ,⊗ id ,⊗ (⊸-β (⊸-app ∘g id ,⊗ genMkTree n) i ∘g upgradeBuilder n ,⊗ id)
              ∘g (lowerG ,⊗ (upgradeBuilder (suc n) ∘g append'
                             ∘g eq-π lhs rhs ∘g lowerG) ,⊗ lowerG ,⊗
                               (append' ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id)
              ∘g ⊗-assoc⁻4))
          ∙ (λ i → genBALANCED n
              ∘g id ,⊗ (⊸-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
              ∘g id ,⊗ id ,⊗ id ,⊗ ⊸-app
              ∘g lowerG ,⊗ (upgradeBuilder (suc n) ∘g lowerG {ℓ-zero})
                        ,⊗ lowerG ,⊗ ((upgradeBuilder n) ∘g lowerG {ℓ-zero}) ,⊗ genMkTree n
              ∘g ⊗-assoc⁻4⊗-intro {f = id}
                                  {f' = liftG {ℓ-zero} ∘g append' ∘g eq-π lhs rhs ∘g lowerG}
                                  {f'' = id}
                                  {f''' = liftG {ℓ-zero} ∘g append' ∘g eq-π lhs rhs ∘g lowerG}
                                  {f'''' = id} (~ i)
            )
          ∙ (λ i →
            upgradeBalancedBuilder n (genMkTree n) (~ i)
            ∘g (id ,⊗ (liftG {ℓ-zero} ∘g append' ∘g eq-π lhs rhs ∘g lowerG)
                   ,⊗ id ,⊗ ((liftG {ℓ-zero} ∘g append' ∘g eq-π lhs rhs ∘g lowerG))) ,⊗ id)
        )
     ∙ sym ⊸-intro-natural

genRetr : lhs ≡ rhs
genRetr = equalizer-ind-unit (DyckTy tt) pf

Dyck≅Trace : Dyck ≅ (Trace true (just 0))
Dyck≅Trace =
  unambiguousRetract'→StrongEquivalence
    (⊸-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g π 0 ∘g genBuildTrace 0)
    mkTree
    (mkTree ∘g ⊸-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g π 0 ∘g buildTrace
     ≡⟨ (λ i → ⊸-mapCod-postcompε mkTree EOF (~ i) ∘g π 0 ∘g buildTrace) ⟩
     ⊸-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g ⊸-mapCod mkTree ∘g π 0 ∘g buildTrace
     ≡⟨ refl ⟩
     ⊸-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g π 0 ∘g
       (&ᴰ-intro λ n → ⊸-mapCod (genMkTree n) ∘g π n) ∘g buildTrace
     ≡⟨ cong (((⊸-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g π 0) ∘g_) genRetr ⟩
     (⊸-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g π 0 ∘g
       (&ᴰ-intro λ n → ⊸-intro (⊸-app ∘g id ,⊗ genMkTree n) ∘g π n) ∘g genAppend'
     ≡⟨ refl ⟩
     (⊸-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g ⊸-mapDom mkTree ∘g π 0 ∘g genAppend'
     ≡⟨ refl ⟩
     (⊸-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g ⊸-mapDom mkTree ∘g append'
     ≡⟨ ((λ i → ⊸-mapDom-postcompε mkTree EOF i ∘g append')) ⟩
     ⊸-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g append'
     ≡⟨ append-nil-r' ⟩
    id ∎)
    (unambiguous-Trace true (just 0))

-- The equivalence between Dyck and Trace true (just 0) allows us to extend the
-- Parser for Trace true (just 0) to a Parser for Dyck
DyckParser : Parser Dyck (Trace false (just 0))
DyckParser = ≈Parser (AccTraceParser (just 0)) (≅→≈ (sym≅ Dyck≅Trace))
