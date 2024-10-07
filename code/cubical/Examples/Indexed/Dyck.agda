{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.Indexed.Dyck where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool hiding (_⊕_ ;_or_)
import Cubical.Data.Equality as Eq
open import Cubical.Data.Nat as Nat
open import Cubical.Data.List hiding (init; rec; map)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (rec; map)
open import Cubical.Data.FinSet

private
  variable
    ℓg : Level

open import Examples.Dyck
open import Grammar Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Lift Alphabet
open import Term Alphabet

open StrongEquivalence

data DyckTag : Type ℓ-zero where
  nil' balanced' : DyckTag
DyckTy : Unit → Functor Unit
DyckTy _ = ⊕e DyckTag (λ
  { nil' → k ε
  ; balanced' → ⊗e (k (literal [)) (⊗e (Var _) (⊗e (k (literal ])) (Var _))) })
IndDyck : Grammar ℓ-zero
IndDyck = μ DyckTy _

NIL : ε ⊢ IndDyck
NIL = roll ∘g ⊕ᴰ-in nil' ∘g liftG

BALANCED : literal [ ⊗ IndDyck ⊗ literal ] ⊗ IndDyck ⊢ IndDyck
BALANCED = roll ∘g ⊕ᴰ-in balanced' ∘g liftG ,⊗ liftG ,⊗ liftG ,⊗ liftG

appendAlg : Algebra DyckTy λ _ → IndDyck ⟜ IndDyck
appendAlg tt = ⊕ᴰ-elim λ
  { nil' → ⟜-intro ⊗-unit-l ∘g lowerG
  ; balanced' → ⟜-intro (BALANCED
    ∘g lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻)
       ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id)
    ∘g ⊗-assoc⁻4)
  }

append' : IndDyck ⊢ IndDyck ⟜ IndDyck
append' = rec _ appendAlg _

append : IndDyck ⊗ IndDyck ⊢ IndDyck
append = ⟜-intro⁻ append'

append-nil-r' : ⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g append' ≡ id
append-nil-r' = ind-id' DyckTy (compHomo DyckTy (initialAlgebra DyckTy) appendAlg (initialAlgebra DyckTy)
    ((λ _ → ⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) , λ _ → pf)
    (recHomo DyckTy appendAlg))
    _
  where
    opaque
      unfolding ⊗-intro ⊗-unit-r⁻ ⊗-assoc⁻
      pf : (⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ∘g appendAlg _
         ≡ roll ∘g map (DyckTy _) (λ _ → ⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻)
      pf = ⊕ᴰ≡ _ _ (λ
        { nil' →
        (⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g ⟜-intro ⊗-unit-l ∘g lowerG)
          ≡⟨ (λ i → ⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻⊗-intro {f = (⟜-intro ⊗-unit-l)} i ∘g lowerG) ⟩
        (⟜-app ∘g id ,⊗ NIL ∘g ⟜-intro ⊗-unit-l ,⊗ id ∘g ⊗-unit-r⁻ ∘g lowerG)
          ≡⟨ refl ⟩
        (⟜-app ∘g (⟜-intro ⊗-unit-l ,⊗ id) ∘g (id ,⊗ NIL) ∘g ⊗-unit-r⁻ ∘g lowerG)
          ≡⟨ cong (_∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g lowerG) (⟜-β ⊗-unit-l) ⟩
        (⊗-unit-l ∘g (id ,⊗ NIL) ∘g ⊗-unit-r⁻ ∘g lowerG)
          ≡⟨ cong (_∘g ⊗-unit-r⁻ ∘g lowerG) (sym (⊗-unit-l⊗-intro NIL)) ⟩
        (NIL ∘g ⊗-unit-l ∘g ⊗-unit-r⁻ ∘g lowerG)
          ≡⟨ cong (NIL ∘g_) (cong (_∘g lowerG) ⊗-unit-lr⁻) ⟩
        NIL ∘g lowerG
        ∎ 
        ; balanced' →
        cong ((⟜-app ∘g id ,⊗ NIL) ∘g_) ⊗-unit-r⁻⊗-intro
        ∙ cong (_∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) (⟜-β _)
        ∙ cong ((BALANCED
                 ∘g id ,⊗ (⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ id ,⊗ (⟜-app ∘g id ,⊗ NIL)
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

data TraceTag (b : Bool) (n : ℕ) : Type where
  eof' : b Eq.≡ true → n Eq.≡ zero → TraceTag b n
  close' : ∀ n-1 → (suc n-1 Eq.≡ n) → TraceTag b n
  open' : TraceTag b n
  leftovers' : (b Eq.≡ false) → ∀ n-1 → (suc n-1 Eq.≡ n) → TraceTag b n
  unexpected' : b Eq.≡ false → n Eq.≡ zero → TraceTag b n

LP = [
RP = ]

-- Trace is *parameterized* by a Bool and *indexed* by a ℕ
TraceTys : Bool → ℕ → Functor ℕ
TraceTys b n = ⊕e (TraceTag b n) (λ
  { (eof' x x₁) → k ε
  ; (leftovers' x n-1 x₁) → k ε
  ; open' → ⊗e (k (literal LP)) (Var (suc n))
  ; (close' n-1 _) → ⊗e (k (literal RP)) (Var n-1)
  ; (unexpected' x x₁) → ⊗e (k (literal RP)) (k ⊤) })

Trace : Bool → ℕ → Grammar _
Trace b = μ (TraceTys b)

EOF : ε ⊢ Trace true 0
EOF = roll ∘g ⊕ᴰ-in (eof' Eq.refl Eq.refl) ∘g liftG

OPEN : ∀ {n b} → literal [ ⊗ Trace b (suc n) ⊢ Trace b n
OPEN = roll ∘g ⊕ᴰ-in open' ∘g liftG ,⊗ liftG

CLOSE : ∀ {n b} → literal ] ⊗ Trace b n ⊢ Trace b (suc n)
CLOSE = roll ∘g ⊕ᴰ-in (close' _ Eq.refl) ∘g liftG ,⊗ liftG

LEFTOVERS : ∀ {n} → ε ⊢ Trace false (suc n)
LEFTOVERS = roll ∘g ⊕ᴰ-in (leftovers' Eq.refl _ Eq.refl) ∘g liftG

UNEXPECTED : literal ] ⊗ ⊤ ⊢ Trace false 0
UNEXPECTED = roll ∘g ⊕ᴰ-in (unexpected' Eq.refl Eq.refl) ∘g liftG ,⊗ liftG

parseTy = &[ n ∈ ℕ ] ⊕[ b ∈ _ ] Trace b n
parse : string ⊢ parseTy
parse = foldKL*r _ (record { the-ℓ = _ ; G = _
  ; nil-case =
    &ᴰ-in (Nat.elim (⊕ᴰ-in true ∘g EOF) (λ _ _ → ⊕ᴰ-in false ∘g LEFTOVERS))
  ; cons-case = &ᴰ-in λ n →
    ⊕ᴰ-elim (λ
      { [ → ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g OPEN) ∘g ⊕ᴰ-distR .fun ∘g id ,⊗ &ᴰ-π (suc n)
      ; ] → Nat.elim {A = λ n → literal RP ⊗ parseTy ⊢ ⊕[ b ∈ _ ] Trace b n}
        (⊕ᴰ-in false ∘g UNEXPECTED ∘g id ,⊗ ⊤-intro)
        (λ n-1 _ → ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g CLOSE) ∘g ⊕ᴰ-distR .fun ∘g id ,⊗ &ᴰ-π n-1)
        n
      })
    ∘g ⊕ᴰ-distL .fun
  })

printAlg : ∀ b → Algebra (TraceTys b) (λ _ → string)
printAlg b n = ⊕ᴰ-elim λ
  { (eof' _ _)         → KL*.nil ∘g lowerG
  ; (leftovers' _ _ _) → KL*.nil ∘g lowerG
  ; open' → CONS ∘g (⊕ᴰ-in LP ∘g lowerG) ,⊗ lowerG
  ; (close' _ _)      → CONS ∘g (⊕ᴰ-in RP ∘g lowerG) ,⊗ lowerG
  ; (unexpected' _ _) → CONS ∘g (⊕ᴰ-in RP ∘g lowerG) ,⊗ (⊤→string ∘g lowerG)
  }

print : ∀ {n b} → Trace b n ⊢ string
print = rec (TraceTys _) (printAlg _) _
 
⊕ᴰAlg : ∀ b → Algebra (TraceTys b) (λ n → ⊕[ b' ∈ _ ] Trace b' n)
⊕ᴰAlg b n = ⊕ᴰ-elim (λ
  { (eof' Eq.refl Eq.refl) → ⊕ᴰ-in true ∘g EOF ∘g lowerG
  ; (leftovers' Eq.refl n-1 Eq.refl) → ⊕ᴰ-in false ∘g LEFTOVERS ∘g lowerG
  ; (close' n-1 Eq.refl) →
    (⊕ᴰ-elim λ b' → ⊕ᴰ-in b' ∘g CLOSE)
    ∘g ⊕ᴰ-distR .fun ∘g lowerG ,⊗ lowerG
  ; open' →
    ((⊕ᴰ-elim λ b' → ⊕ᴰ-in b' ∘g OPEN) ∘g ⊕ᴰ-distR .fun)
    ∘g lowerG ,⊗ lowerG
  ; (unexpected' Eq.refl Eq.refl) →
    ⊕ᴰ-in false ∘g UNEXPECTED ∘g lowerG ,⊗ lowerG
  })

⊕ᴰ-in-homo : ∀ b →
  Homomorphism (TraceTys b) (initialAlgebra (TraceTys b)) (⊕ᴰAlg b)
⊕ᴰ-in-homo b .fst n = ⊕ᴰ-in b
⊕ᴰ-in-homo b .snd n = pf where
  opaque
    unfolding ⊕ᴰ-distR ⊗-intro
    pf : ⊕ᴰ-in b ∘g initialAlgebra (TraceTys b) n
         ≡ ⊕ᴰAlg b n ∘g map (TraceTys b n) λ _ → ⊕ᴰ-in b
    pf = ⊕ᴰ≡ _ _ (λ
      { (eof' Eq.refl Eq.refl) → refl
      ; (leftovers' Eq.refl n-1 Eq.refl) → refl
      ; open' → refl
      ; (close' n-1 Eq.refl) → refl
      ; (unexpected' Eq.refl Eq.refl) → refl }) 

parseHomo : ∀ b → Homomorphism (TraceTys b) (printAlg b) (⊕ᴰAlg b)
parseHomo b .fst n = &ᴰ-π n ∘g parse
parseHomo b .snd n = pf where
  opaque
    unfolding KL*r-elim ⊕ᴰ-distR CONS ⊤
    pf : &ᴰ-π n ∘g parse ∘g printAlg b n
       ≡ ⊕ᴰAlg b n ∘g map (TraceTys b n) (λ n → &ᴰ-π n ∘g parse) 
    pf = ⊕ᴰ≡ _ _ λ
      { (eof' Eq.refl Eq.refl) → refl
      ; (close' n-1 Eq.refl) → refl
      ; open' → refl
      ; (leftovers' Eq.refl n-1 Eq.refl) → refl
      ; (unexpected' Eq.refl Eq.refl) → refl
      }

Trace≅String : ∀ {n} → StrongEquivalence (⊕[ b ∈ _ ] Trace b n) string
Trace≅String {n} = mkStrEq
  (⊕ᴰ-elim (λ _ → print))
  (&ᴰ-π _ ∘g parse)
  (unambiguous-string _ _)
  isRetr
  where
    isRetr : (&ᴰ-π n ∘g parse) ∘g ⊕ᴰ-elim (λ _ → print) ≡ id
    isRetr = ⊕ᴰ≡ _ _ (λ b →
      ind' (TraceTys b)
        (⊕ᴰAlg b)
        (compHomo (TraceTys b) (initialAlgebra (TraceTys b)) (printAlg b) (⊕ᴰAlg b)
          (parseHomo b)
          (recHomo (TraceTys b) (printAlg b)))
        (⊕ᴰ-in-homo b)
        n)

isUnambiguousTrace : ∀ {n b} → unambiguous (Trace b n)
isUnambiguousTrace {n}{b} =
  unambiguous⊕ᴰ isSetBool
    (unambiguous≅ (sym-strong-equivalence Trace≅String) unambiguous-string)
    b

{-
  Next, we establish that IndDyck and Trace true zero are strongly equivalent.

  To prove this inductively, we more generally prove that Trace true n
  is strongly equivalent to a "GenDyck n" that is an analogously
  "unbalanced" Dyck tree.
-}
GenDyck : ℕ → Grammar _
GenDyck 0         = IndDyck
GenDyck (suc n-1) = IndDyck ⊗ literal RP ⊗ GenDyck n-1

-- We extend the balanced constructor and append to our unbalanced
-- trees
opaque
  genBALANCED : ∀ n → literal LP ⊗ IndDyck ⊗ literal RP ⊗ GenDyck n ⊢ GenDyck n
  genBALANCED zero   = BALANCED
  genBALANCED (suc n) = ⟜4⊗ (⟜4-intro-ε BALANCED)

upgradeBuilder : ∀ n → (IndDyck ⟜ IndDyck) ⊢ GenDyck n ⟜ GenDyck n
upgradeBuilder zero = id
upgradeBuilder (suc n) = ⟜-intro (⟜-app ,⊗ id ∘g ⊗-assoc)

opaque
  unfolding ⊗-intro genBALANCED
  -- uB-lem' :
  --   ∀ n (f : Trace true n ⊢ GenDyck n)
  --       (f' : {!!} ⊢ {!!})
  --      → (⟜-app ∘g id ,⊗ f) ∘g
  --       (upgradeBuilder n ∘g ⟜-intro {!!}) ,⊗ id
  --       ≡ (f ∘g {!!})
  -- uB-lem' = {!!}

  upgradeNilBuilder :
    ∀ n (f : Trace true n ⊢ GenDyck n)
       → (⟜-app ∘g id ,⊗ f) ∘g
        (upgradeBuilder n ∘g ⟜-intro ⊗-unit-l) ,⊗ id
        ≡ f ∘g ⊗-unit-l
  upgradeNilBuilder zero f =
    cong (_∘g (id ,⊗ f)) (⟜-β _)
    ∙ sym (⊗-unit-l⊗-intro _)
  upgradeNilBuilder (suc n) f =
    cong (_∘g ((⟜-intro ⊗-unit-l)) ,⊗ f) (⟜-β _)
    ∙ cong ((⟜-app ,⊗ id) ∘g_) (cong (_∘g (id ,⊗ f)) (⊗-assoc⊗-intro {f' = id}{f'' = id}))
    ∙ ( (λ i → (⟜-β ⊗-unit-l i) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ f))
    ∙ cong (_∘g (id ,⊗ f)) (cong ((⊗-unit-l ,⊗ id) ∘g_) (sym (⊗-assoc⊗-intro {f' = id}{f'' = id})))
    ∙ cong (_∘g id ,⊗ f) ⊗-unit-l⊗-assoc
    ∙ sym (⊗-unit-l⊗-intro _)

  upgradeBalancedBuilder :
    ∀ n (f : Trace true n ⊢ GenDyck n)
    → (⟜-app ∘g id ,⊗ f)
      ∘g (upgradeBuilder n ∘g ⟜-intro (
          BALANCED
          ∘g lowerG {ℓ-zero} ,⊗ (⟜-app ∘g lowerG{ℓ-zero} ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG {ℓ-zero} ,⊗ (⟜-app ∘g lowerG {ℓ-zero} ,⊗ id)
          ∘g ⊗-assoc⁻4))
         ,⊗ id
      ≡ genBALANCED n
        ∘g id ,⊗ (⟜-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
        ∘g id ,⊗ id ,⊗ id ,⊗ ⟜-app
        ∘g lowerG ,⊗ (upgradeBuilder (suc n) ∘g lowerG) ,⊗ lowerG ,⊗ ((upgradeBuilder n) ∘g lowerG) ,⊗ f
        ∘g ⊗-assoc⁻4
  upgradeBalancedBuilder zero f =
    cong (_∘g (id ,⊗ f)) (⟜-β _)
    ∙ (λ i → BALANCED
       ∘g lowerG ,⊗ (⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻⊗-intro {f = lowerG} (~ i)) ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id)
       ∘g ⊗-assoc⁻4
       ∘g id ,⊗ f
      )
    ∙ (λ i → BALANCED ∘g
      lowerG ,⊗ (⟜-app ∘g id ,⊗ NIL) ,⊗ id ∘g
      id ,⊗ ⊗-assoc⊗-unit-l⁻ (~ i) ∘g
      id ,⊗ id ,⊗ id ,⊗ ⟜-app ∘g
      id ,⊗ lowerG ,⊗ lowerG ,⊗ (id ∘g lowerG) ,⊗ id
      ∘g ⊗-assoc⁻4
      ∘g id ,⊗ f)
    ∙ (λ i → BALANCED
      ∘g id ,⊗ ⟜-app ,⊗ id
      ∘g id ,⊗ ((id ,⊗ NIL) ,⊗ id)
      ∘g id ,⊗ (⊗-assoc ∘g id ,⊗ ⊗-unit-l⁻)  -- 
      ∘g id ,⊗ id ,⊗ id ,⊗ ⟜-app
      ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (id ∘g lowerG) ,⊗ id ∘g ⊗-assoc⁻4⊗-intro {f = id}{f' = id}{f'' = id}{f''' = id}{f'''' = f} i)
    ∙ (λ i → BALANCED
      ∘g id ,⊗ (⟜-app ,⊗ id)
      ∘g id ,⊗ ⊗-assoc⊗-intro {f = id}{f' = NIL}{f'' = id} (~ i)
      ∘g id ,⊗ (id ,⊗ ⊗-unit-l⁻)
      ∘g id ,⊗ id ,⊗ id ,⊗ ⟜-app
      ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (id ∘g lowerG) ,⊗ f ∘g ⊗-assoc⁻4
          )
    ∙ λ i → BALANCED
      ∘g id ,⊗ (⟜-β (⟜-app ,⊗ id ∘g ⊗-assoc) (~ i))
      ∘g id ,⊗ (id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
      ∘g id ,⊗ id ,⊗ id ,⊗ ⟜-app
      ∘g lowerG ,⊗ (lowerG) ,⊗ lowerG ,⊗ (id ∘g lowerG) ,⊗ f
      ∘g ⊗-assoc⁻4
  upgradeBalancedBuilder (suc n) f = {!!}

genAppend' : IndDyck ⊢ &[ n ∈ _ ] (GenDyck n ⟜ GenDyck n)
genAppend' = (&ᴰ-intro upgradeBuilder) ∘g append'

genAppend : ∀ n → IndDyck ⊗ GenDyck n ⊢ GenDyck n
genAppend zero    = append
genAppend (suc _) = ⟜2⊗ (⟜2-intro-ε append)

{- First, we construct a GenDyck n from a Trace n -}
genMkTreeAlg : Algebra (TraceTys true) GenDyck
genMkTreeAlg n = ⊕ᴰ-elim (λ
  { (eof' Eq.refl Eq.refl) → NIL ∘g lowerG
  ; open' → genBALANCED n ∘g lowerG ,⊗ lowerG
  ; (close' n-1 Eq.refl) → ⟜0⊗ NIL ∘g lowerG ,⊗ lowerG
  })

genMkTree : ∀ {n} → Trace true n ⊢ GenDyck n
genMkTree = rec (TraceTys _) genMkTreeAlg _

mkTree : Trace true zero ⊢ IndDyck
mkTree = genMkTree

{-

  Next, we extract the trace from an IndDyck and then iterate this to
  extract one from a GenDyck.

  The trick to defining this by structural recursion is to map each
  IndDyck recursively to a "TraceBuilder", a linear function that
  takes a trace to its right and "piles" the characters from the tree
  onto the trace. Since an IndDyck is balanced, it doesn't affect the
  state n.

-}
TraceBuilder : Unit → Grammar ℓ-zero
TraceBuilder _ = &[ n ∈ _ ] (Trace true n ⟜ Trace true n)

buildTraceAlg : Algebra DyckTy TraceBuilder
buildTraceAlg _ = ⊕ᴰ-elim (λ
  { nil' → &ᴰ-intro (λ n → ⟜-intro-ε id ∘g lowerG)
  ; balanced' → &ᴰ-intro λ n → ⟜-intro
    -- OPEN, making a Trace n
    (OPEN
    -- build a Trace (suc n) with the left subtree
    ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc n) ,⊗ id)
    -- CLOSE, making a Trace (suc n)
    ∘g id ,⊗ id ,⊗ CLOSE
     -- build a Trace n with the right subtree
    ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
     -- reassoc the builder arg to the right, and lower everything else
    ∘g ⊗-assoc⁻4
    ∘g (lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ lowerG) ,⊗ id
    )
  })

buildTrace : IndDyck ⊢ TraceBuilder _
buildTrace = rec DyckTy buildTraceAlg _

-- we then extend the builder to generalized trees, which *adds*
-- closed parens to the trace.
genBuildTrace : ∀ m → GenDyck m ⊢ &[ n ∈ _ ] (Trace true (m + n) ⟜ Trace true n)
genBuildTrace zero = buildTrace
genBuildTrace (suc m) = &ᴰ-intro λ n → ⟜-intro
  -- build using the left subtree
  ((⟜-app ∘g (&ᴰ-π (suc (m + n)) ∘g buildTrace) ,⊗ id)
  -- CLOSE the trace, to make is (suc (m + n))
  ∘g id ,⊗ CLOSE
  -- recursively build using the right subtree
  ∘g id ,⊗ id ,⊗ (⟜-app ∘g (&ᴰ-π n ∘g genBuildTrace m) ,⊗ id)
  -- reassoc everything
  ∘g ⊗-assoc⁻3
  )

PileAlg : Algebra DyckTy (λ _ → &[ n ∈ _ ] (GenDyck n ⟜ Trace true n))
PileAlg _ = ⊕ᴰ-elim (λ
  { nil' → &ᴰ-intro λ n → ⟜-intro-ε genMkTree ∘g lowerG
  ; balanced' → &ᴰ-intro λ n → ⟜-intro
    (genBALANCED n
     ∘g id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ EOF ∘g ⊗-unit-r⁻) ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
     ∘g ⊗-assoc⁻4
     ∘g (lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ lowerG) ,⊗ id
     )
  })

genRetr :
  Path (IndDyck ⊢ &[ n ∈ _ ] (GenDyck n ⟜ Trace true n))
    ((&ᴰ-intro λ n → ⟜-intro (genMkTree ∘g ⟜-app) ∘g &ᴰ-π n) ∘g buildTrace)
    ((&ᴰ-intro λ n → ⟜-intro (⟜-app ∘g id ,⊗ genMkTree) ∘g &ᴰ-π n) ∘g genAppend')
genRetr = ind' DyckTy PileAlg
  (compHomo DyckTy (initialAlgebra DyckTy) buildTraceAlg PileAlg
    ((λ _ → &ᴰ-intro λ n → ⟜-intro (genMkTree ∘g ⟜-app) ∘g &ᴰ-π n) , λ _ → ⊕ᴰ≡ _ _ λ
      { nil' → &ᴰ≡ _ _ (λ m →
          cong (_∘g lowerG) (⟜-mapCod-precomp genMkTree ⊗-unit-l)
        )
      ; balanced' → &ᴰ≡ _ _ λ m →
         (⟜-intro (genMkTree ∘g ⟜-app) ∘g &ᴰ-π m) ∘g
          buildTraceAlg _
         ∘g ⊕ᴰ-in balanced'
          ≡⟨ {!!} ⟩
      &ᴰ-π m ∘g
        (PileAlg _ ∘g
        map (DyckTy _)
        (λ _ → &ᴰ-intro (λ n → ⟜-intro (genMkTree ∘g ⟜-app) ∘g &ᴰ-π n)))
        ∘g ⊕ᴰ-in balanced'
        ∎
    })
    (recHomo DyckTy buildTraceAlg))
  (compHomo DyckTy (initialAlgebra DyckTy) appendAlg PileAlg
    ((λ _ → f1) , λ _ → f1-is-homo
      -- &ᴰ≡ _ _ λ { n →
      --   ⊕ᴰ≡ _ _ λ
      --     { nil' →
      --       ⟜-intro (⟜-app ∘g id ,⊗ genMkTree) ∘g {!!}
      --         ≡⟨ {!!} ⟩
      --       {!!} ∎
      --     ; balanced' → {!!}
      --     }
      -- }
      -- ⊕ᴰ≡ _ _ (λ
    -- { nil' → &ᴰ≡ _ _ λ {
    --     zero →
    --   {!⟜-intro (⟜-app ∘g id ,⊗ genMkTree) ∘g !}

    --   --  ⟜-intro (⟜-app ∘g id ,⊗ genMkTree) ∘g
    --   --  ⟜-intro ⊗-unit-l ∘g lowerG
    --   --   ≡⟨ (λ i → ⟜-mapDom-precomp genMkTree ⊗-unit-l i ∘g lowerG) ⟩
    --   --  ⟜-intro (⊗-unit-l ∘g id ,⊗ genMkTree) ∘g
    --   --  lowerG
    --   --   ≡⟨ ((λ i → ⟜-intro (⊗-unit-l⊗-intro genMkTree (~ i)) ∘g lowerG)) ⟩
    --   -- ⟜-intro (genMkTree ∘g ⊗-unit-l) ∘g
    --   -- lowerG
    --   -- ∎
    --   ; (suc m) →
    --    ⟜-intro (⟜-app ∘g id ,⊗ genMkTree) ∘g
    --    ⟜-intro (⟜2⊗ (⟜2-intro-ε ⟜-app)) ∘g
    --    ⟜-intro ⊗-unit-l ∘g lowerG
    --     ≡⟨ (λ i → ⟜-mapDom-precomp genMkTree (⟜2⊗ (⟜2-intro-ε ⟜-app)) i ∘g
    --               ⟜-intro ⊗-unit-l ∘g lowerG) ⟩
    --   ⟜-intro (⟜2⊗ (⟜2-intro-ε ⟜-app) ∘g id ,⊗ genMkTree) ∘g
    --   ⟜-intro ⊗-unit-l ∘g lowerG
    --     ≡⟨ ⟜≡ _ _ nil-lem ⟩
    --   ⟜-intro (genMkTree ∘g ⊗-unit-l) ∘g
    --   lowerG
    --   ∎
    --  }
    -- ; balanced' → {!refl!} })
    )
    (recHomo DyckTy appendAlg))
  _
  where
    f1 : IndDyck ⟜ IndDyck ⊢ &[ n ∈ _ ] (GenDyck n ⟜ Trace true n)
    f1 = (&ᴰ-intro λ n → ⟜-intro (⟜-app ∘g id ,⊗ genMkTree) ∘g &ᴰ-π n) ∘g (&ᴰ-intro upgradeBuilder)
    opaque
      unfolding ⊗-intro
        
  
      f1-is-homo : f1 ∘g appendAlg _ ≡ PileAlg _ ∘g map (DyckTy _) λ _ → f1
      f1-is-homo = ⊕ᴰ≡ _ _ λ
        { nil' → &ᴰ≡ _ _ λ n →
          ⟜≡ _ _
              (cong (_∘g ((upgradeBuilder n ∘g ⟜-intro ⊗-unit-l ∘g lowerG) ,⊗ id)) (⟜-β _)
              ∙ cong (_∘g (lowerG ,⊗ id)) (upgradeNilBuilder n genMkTree ∙ sym (⟜-β _)))
        ; balanced' → &ᴰ≡ _ _ λ n → ⟜≡ _ _
          ( cong (_∘g ((upgradeBuilder n ∘g ⟜-intro (BALANCED ∘g lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id) ∘g ⊗-assoc⁻4)) ,⊗ id)) (⟜-β _)
          ∙ upgradeBalancedBuilder n genMkTree
          ∙ {!!}
          ∙ cong ((genBALANCED n ∘g id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ EOF ∘g ⊗-unit-r⁻) ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)) ∘g_) (sym (⊗-assoc⁻4⊗-intro {f = lowerG}{f' = f1 ∘g lowerG}{f'' = lowerG}{f''' = f1 ∘g lowerG}{f'''' = id}))
{-
      (genBALANCED n ∘g
       id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ EOF ∘g ⊗-unit-r⁻) ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
       ∘g ⊗-assoc⁻4
       ∘g (lowerG ,⊗ f1 ∘g lowerG ,⊗ lowerG ,⊗ f1 ∘g lowerG) ,⊗ id)
 -}
          ∙ cong (_∘g ((id ,⊗ (liftG {ℓ-zero} ∘g f1 ∘g lowerG) ,⊗ id ,⊗ (liftG {ℓ-zero} ∘g f1 ∘g lowerG))) ,⊗ id) (sym (⟜-β _)))

          --  (⟜-app ∘g (⟜-intro (⟜-app ∘g id ,⊗ genMkTree) ∘g upgradeBuilder n ∘g ⟜-intro (BALANCED ∘g lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id) ∘g ⊗-assoc⁻4)) ,⊗ id
          --   ≡⟨ {!!} ⟩
          --   ⟜-app
          -- ∘g (⟜-intro (genBALANCED n
          --             ∘g  id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ EOF ∘g ⊗-unit-r⁻) ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
          --             ∘g ⊗-assoc⁻4
          --             ∘g (lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ lowerG) ,⊗ id)
          --    ∘g id ,⊗ (liftG {ℓ-zero} ∘g f1 ∘g lowerG) ,⊗ id ,⊗ (liftG {ℓ-zero} ∘g f1 ∘g lowerG))
          --    ,⊗ id
          --  ∎)
          }

      -- ⟜-app ∘g
      -- (&ᴰ-π n ∘g
      --  (PileAlg tt ∘g map (DyckTy tt) (λ _ → f1)) ∘g ⊕ᴰ-in balanced')
      -- ,⊗ id


Dyck≅Trace : StrongEquivalence IndDyck (Trace true 0)
Dyck≅Trace =
  unambiguousRetract→StrongEquivalence
    (⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g &ᴰ-π 0 ∘g genBuildTrace 0)
    genMkTree
    (genMkTree ∘g ⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g &ᴰ-π 0 ∘g buildTrace
     ≡⟨ (λ i → ⟜-mapCod-postcompε (genMkTree {n = 0}) EOF (~ i) ∘g &ᴰ-π 0 ∘g buildTrace) ⟩
     ⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g ⟜-mapCod genMkTree ∘g &ᴰ-π 0 ∘g buildTrace
     ≡⟨ refl ⟩
     ⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g &ᴰ-π 0 ∘g (&ᴰ-intro λ n → ⟜-mapCod genMkTree ∘g &ᴰ-π n) ∘g buildTrace
     ≡⟨ cong (((⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g &ᴰ-π 0) ∘g_) genRetr ⟩
     (⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g &ᴰ-π 0 ∘g (&ᴰ-intro λ n → ⟜-intro (⟜-app ∘g id ,⊗ genMkTree {n = n}) ∘g &ᴰ-π n) ∘g genAppend'
     ≡⟨ refl ⟩
     (⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g ⟜-mapDom mkTree ∘g &ᴰ-π 0 ∘g genAppend'
     ≡⟨ refl ⟩
     (⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g ⟜-mapDom mkTree ∘g append'
     ≡⟨ ((λ i → ⟜-mapDom-postcompε mkTree EOF i ∘g append')) ⟩
     ⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g append'
     ≡⟨ append-nil-r' ⟩
    id ∎)
    isUnambiguousTrace

-- I don't think we actually need to prove the following
-- GenDyck≅Trace : ∀ n → StrongEquivalence (GenDyck n) (Trace true n)
-- GenDyck≅Trace n =
--   unambiguousRetract→StrongEquivalence
--     (transportG (cong (Trace true) (+-zero n))
--       ∘g ⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g &ᴰ-π 0
--       ∘g genBuildTrace n)
--     genMkTree
--     {!!}
--     isUnambiguousTrace
