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
open import Grammar Alphabet hiding (NIL)
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
  { nil' → ⟜-intro-ε id ∘g lowerG
  ; balanced' → ⟜-intro (BALANCED
    ∘g lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻)
       ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id)
    ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻)
  }

append : IndDyck ⊗ IndDyck ⊢ IndDyck
append = ⟜-intro⁻ (rec _ appendAlg _)

-- Need this lemma for the retract property below
append-nil-r : append ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ≡ id
append-nil-r = {!!}

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
parse = ?
-- foldKL*r _ (record { the-ℓ = _ ; G = _
--   ; nil-case =
--     &ᴰ-in (Nat.elim (⊕ᴰ-in true ∘g EOF) (λ _ _ → ⊕ᴰ-in false ∘g LEFTOVERS))
--   ; cons-case = &ᴰ-in λ n →
--     ⊕ᴰ-elim (λ
--       { [ → ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g OPEN) ∘g ⊕ᴰ-distR .fun ∘g id ,⊗ &ᴰ-π (suc n)
--       ; ] → Nat.elim {A = λ n → literal RP ⊗ parseTy ⊢ ⊕[ b ∈ _ ] Trace b n}
--         (⊕ᴰ-in false ∘g UNEXPECTED ∘g id ,⊗ ⊤-intro)
--         (λ n-1 _ → ⊕ᴰ-elim (λ b → ⊕ᴰ-in b ∘g CLOSE) ∘g ⊕ᴰ-distR .fun ∘g id ,⊗ &ᴰ-π n-1)
--         n
--       })
--     ∘g ⊕ᴰ-distL .fun
--   })

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

{-
  Next, we establish that IndDyck and Trace true zero are strongly equivalent.

  To prove this inductively, we more generally prove that Trace true n
  is strongly equivalent to a "GenDyck n" that is an analogously
  "unbalanced" Dyck tree.
  
-}
GenDyck : ℕ → Grammar _
GenDyck 0         = IndDyck
GenDyck (suc n-1) = IndDyck ⊗ literal RP ⊗ GenDyck n-1

{- First, we construct a GenDyck from a Trace -}
genBALANCED : ∀ n → literal LP ⊗ IndDyck ⊗ literal RP ⊗ GenDyck n ⊢ GenDyck n
genBALANCED zero   = BALANCED
genBALANCED (suc n) = ⟜4⊗ (⟜4-intro-ε BALANCED)

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
  IndDyck recursively to a "TraceBuilder"

-}

genAppend : ∀ n → IndDyck ⊗ GenDyck n ⊢ GenDyck n
genAppend zero    = append
genAppend (suc _) = ⟜2⊗ (⟜2-intro-ε append)

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
    ∘g lowerG ,⊗ (lowerG ,⊗ (lowerG ,⊗ lowerG ,⊗ id ∘g  ⊗-assoc⁻) ∘g ⊗-assoc⁻)
       ∘g ⊗-assoc⁻
    )
  })

buildTrace : IndDyck ⊢ TraceBuilder _
buildTrace = rec DyckTy buildTraceAlg _

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
  ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻)

-- -- appEOF : TraceAction _ ⊢ Trace zero true
-- -- appEOF = (⟜-app ∘g ⊸0⊗ EOF ∘g &ᴰ-π 0)

-- -- -- prove this by induction and this should imply the retract property
-- -- genRetract :
-- --   ∀ {n} →
-- --   Path (IndDyck ⊗ Trace n true ⊢ GenIndDyck (n , true))
-- --     (genMkTree ∘g ⟜-app ∘g (&ᴰ-π n ∘g traceBuilder) ,⊗ id)
-- --     (genAppend {n = n} ∘g id ,⊗ genMkTree)
-- -- genRetract = {!!}

-- -- genSection :
-- --   ∀ {n} →
-- --   Path (Trace n true ⊢ Trace n true)
-- --     -- seems unavoidable unfortunately
-- --     (subst (λ m → Trace n true ⊢ Trace m true) (+-zero n)
-- --       (⟜-app ∘g ⊸0⊗ EOF ∘g &ᴰ-π 0 ∘g genTraceBuilder {m = n} ∘g genMkTree))
-- --     id
-- -- genSection = {!!}

-- -- -- mkTree ∘g ((⟜-app ∘g ⊸0⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl)) ∘g &ᴰ-π 0)

-- -- -- is a homomorphism from eTAlg to (initialAlgebra DyckTy)

-- -- Dyck≅Trace : StrongEquivalence IndDyck (Trace zero true)
-- -- Dyck≅Trace = mkStrEq exhibitTrace' mkTree
-- --   {!!} -- use mkTreeAlg
-- --   (ind-id' DyckTy (compHomo DyckTy (initialAlgebra DyckTy) eTAlg (initialAlgebra DyckTy)
-- --     ((λ _ → mkTree ∘g appEOF)
-- --     , λ _ → ⊕ᴰ≡ _ _ (λ
-- --       { nil' →
-- --         cong
-- --           (rec TraceTys mkTreeAlg (0 , true) ∘g_)
-- --           (p (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl))
-- --       ; balanced' →
-- --         mkTree ∘g appEOF ∘g eTAlg _ ∘g ⊕ᴰ-in balanced'
-- --           ≡⟨ refl ⟩
-- --         mkTree ∘g ⟜-app ∘g ⊸0⊗ EOF ∘g ⟜-intro {k = Trace 0 true}
-- --           (OPEN
-- --           ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id)
-- --           ∘g id ,⊗ id ,⊗ CLOSE
-- --           ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id)
-- --           ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻)
-- --           ≡⟨ {!!} ⟩
-- --         mkTree ∘g OPEN
-- --           ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id)
-- --           ∘g id ,⊗ id ,⊗ CLOSE
-- --           ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id)
-- --           ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
-- --           ∘g ⊸0⊗ EOF
-- --           ≡⟨ refl ⟩
-- --         BALANCED
-- --           ∘g id ,⊗ rec TraceTys mkTreeAlg (1 , true)
-- --           ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id)
-- --           ∘g id ,⊗ id ,⊗ CLOSE
-- --           ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id)
-- --           ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
-- --           ∘g ⊸0⊗ EOF
-- --           ≡⟨ {!!} ⟩ -- TODO: tedious but just βη
-- --         BALANCED
-- --           ∘g id ,⊗ (rec TraceTys mkTreeAlg (1 , true) ∘g (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id ∘g id ,⊗ (CLOSE ∘g id ,⊗ appEOF)))
-- --           ≡⟨ (λ i → BALANCED ∘g id ,⊗ the-lemma i) ⟩
-- --         BALANCED
-- --           ∘g id ,⊗ (mkTree ∘g appEOF) ,⊗ id ,⊗ (mkTree ∘g appEOF)
-- --           ∎
-- -- -- ⊸0⊗ : ε ⊢ k → l ⊢ l ⊗ k
-- -- -- ⊸0⊗ f = id ,⊗ f ∘g ⊗-unit-r⁻
  
-- --         -- rec TraceTys mkTreeAlg (0 , true) ∘g
-- --         -- ⟜-app ∘g
-- --         -- id ,⊗ (roll ∘g
-- --         --     ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
-- --         -- ⊗-unit-r⁻ ∘g
-- --         -- ⟜-intro {k = Trace 0 true}
-- --         --   (roll ∘g ⊕ᴰ-in open'
-- --         --   ∘g id ,⊗ ((⟜-app ∘g &ᴰ-π (suc 0) ,⊗ ((roll ∘g ⊕ᴰ-in close' ∘g ⊕ᴰ-in (_ , Eq.refl) ∘g id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id)) ∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
-- --         --   ∘g ⊗-assoc⁻)
-- --         --   ≡⟨ cong ((rec TraceTys mkTreeAlg (0 , true)) ∘g_) (q' _ _) ⟩
-- --         -- rec TraceTys mkTreeAlg (0 , true) ∘g
-- --         -- roll ∘g
-- --         -- ⊕ᴰ-in open' ∘g
-- --         -- -- Bool.elim {A = λ b → literal [ ⊗ GenIndDyck (suc 0 , b)  ⊢ GenIndDyck (0 , b)}
-- --         -- --   (roll ∘g ⊕ᴰ-in balanced')
-- --         -- --   ⊤-intro true ∘g
-- --         -- id ,⊗
-- --         --   (⟜-app ∘g
-- --         --     &ᴰ-π (suc 0) ,⊗
-- --         --     (roll ∘g
-- --         --       ⊕ᴰ-in close' ∘g
-- --         --       ⊕ᴰ-in (0 , Eq.refl) ∘g id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id) ∘g
-- --         --       ⊗-assoc⁻) ∘g
-- --         --    ⊗-assoc⁻) ∘g
-- --         -- ⊗-assoc⁻ ∘g
-- --         -- id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
-- --         -- ⊗-unit-r⁻
-- --         --   ≡⟨ (λ i → roll ∘g ⊕ᴰ-in balanced' ∘g id ,⊗ rec TraceTys mkTreeAlg (1 , true) ∘g ((id ,⊗ (⟜-app ∘g ⊗-intro (&ᴰ-π 1)
-- --         --     (roll ∘g
-- --         --      ⊕ᴰ-in close' ∘g
-- --         --      ⊕ᴰ-in (0 , Eq.refl) ∘g
-- --         --      id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id) ∘g ⊗-assoc⁻) ∘g ⊗-assoc⁻)
-- --         --     ∘g ⊗-assoc⁻ ∘g id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g (id ,⊗ rec TraceTys mkTreeAlg (1 , true)) ∘g {!!}) ∘g id ,⊗ id ,⊗ {!!}) ∘g (⊗-assoc⁻ ∘g
-- --         --      id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
-- --         --      ⊗-unit-r⁻)) ⟩


-- --         -- roll ∘g ⊕ᴰ-in balanced' ∘g id ,⊗ recHomo TraceTys mkTreeAlg .fst (1 , true) ∘g {!!} ∘g (⊗-assoc⁻ ∘g
-- --         --      id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
-- --         --      ⊗-unit-r⁻)
-- --         -- -- roll ∘g
-- --         -- -- ⊕ᴰ-in balanced' ∘g
-- --         -- -- id ,⊗ ({!id!} ∘g map (DyckTy _) {!!} ∘g {!id!}) ∘g
-- --         -- -- id ,⊗
-- --         -- --   (⟜-app ∘g
-- --         -- --     &ᴰ-π (suc 0) ,⊗
-- --         -- --     (roll ∘g
-- --         -- --       ⊕ᴰ-in close' ∘g
-- --         -- --       ⊕ᴰ-in (0 , Eq.refl) ∘g id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id) ∘g
-- --         -- --       ⊗-assoc⁻) ∘g
-- --         -- --    ⊗-assoc⁻) ∘g
-- --         -- -- ⊗-assoc⁻ ∘g
-- --         -- -- id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
-- --         -- -- ⊗-unit-r⁻
-- --         --   ≡⟨ (λ i → roll ∘g ⊕ᴰ-in balanced' ∘g {!!} ) ⟩
-- --         -- roll ∘g
-- --         -- map (DyckTy _)
-- --         --   (λ z →
-- --         --      mkTree ∘g
-- --         --      (⟜-app ∘g
-- --         --       ⊸0⊗
-- --         --       (roll ∘g
-- --         --        ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl))
-- --         --      ∘g &ᴰ-π 0)
-- --         --  ∘g ⊕ᴰ-in balanced'
-- --         -- ∎
-- --      }))
-- --     (recHomo DyckTy eTAlg))
-- --     tt)
-- --     where
-- --       -- maybe generalize from 0 to n and prove ∀ n by induction?
-- --       the-lemma :
-- --         Path (TraceAction _ ⊗ literal ] ⊗ TraceAction _ ⊢ IndDyck ⊗ literal ] ⊗ IndDyck)
-- --         (rec TraceTys mkTreeAlg ((suc 0) , true) ∘g (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id ∘g id ,⊗ (CLOSE ∘g id ,⊗ appEOF)))
-- --         ((rec TraceTys mkTreeAlg (0 , true) ∘g appEOF) ,⊗ id ,⊗ (rec TraceTys mkTreeAlg (0 , true) ∘g appEOF))
-- --       the-lemma = {!!}
   
-- --       the-lemma' :
-- --         Path (TraceAction _ ⊗ literal ] ⊗ Trace 0 true ⊢ IndDyck ⊗ literal ] ⊗ IndDyck)
-- --         (rec TraceTys mkTreeAlg ((suc 0) , true) ∘g (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id ∘g id ,⊗ (CLOSE ∘g id ,⊗ id)))
-- --         ((rec TraceTys mkTreeAlg (0 , true) ∘g appEOF) ,⊗ id ,⊗ (rec TraceTys mkTreeAlg (0 , true)))
-- --       the-lemma' = {!!}
-- --       -- TODO rename all of these lemmas and put them in the relevant external
-- --       -- files
-- --       opaque
-- --         unfolding ε
-- --         -- Epsilon.Properties
-- --         u : unambiguous ε
-- --         u = EXTERNAL.propParses→unambiguous isFinBracket λ w → isSetString _ _

-- --       -- Epsilon.Properties
-- --       s : ⊗-unit-l {g = ε} ≡ ⊗-unit-r {g = ε}
-- --       s = u _ _

-- --       -- Epsilon.Properties
-- --       t : ⊗-unit-l⁻ {g = ε} ≡ ⊗-unit-r⁻ {g = ε}
-- --       t =
-- --         ⊗-unit-l⁻
-- --           ≡⟨ cong (⊗-unit-l⁻ ∘g_) (sym ⊗-unit-r⁻r) ⟩
-- --         ⊗-unit-l⁻ ∘g ⊗-unit-r ∘g ⊗-unit-r⁻
-- --           ≡⟨ cong (λ z → ⊗-unit-l⁻ ∘g z ∘g ⊗-unit-r⁻) (sym s) ⟩
-- --         ⊗-unit-l⁻ ∘g ⊗-unit-l ∘g ⊗-unit-r⁻
-- --           ≡⟨ cong (_∘g ⊗-unit-r⁻) ⊗-unit-ll⁻ ⟩
-- --         ⊗-unit-r⁻
-- --         ∎

-- --       opaque
-- --         -- opaque so that ⊗-unit-r⁻ commutes for free
-- --         unfolding ⊗-unit-r⁻ ⊗-unit-l⁻
-- --         q' : ∀ {ℓg ℓh ℓk : Level}
-- --           {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk}
-- --           (e : ε ⊢ g)(e' : k ⊗ g ⊢ h) →
-- --           ⟜-app ∘g (id ,⊗ e) ∘g ⊗-unit-r⁻ ∘g ⟜-intro e' ≡
-- --             e' ∘g id ,⊗ e ∘g ⊗-unit-r⁻
-- --         q' e e' = cong (_∘g (id ,⊗ e ∘g ⊗-unit-r⁻)) (⟜-β e')

-- --         q : ∀ {ℓg ℓh : Level}
-- --           {g : Grammar ℓg}{h : Grammar ℓh}
-- --           (e : ε ⊢ g)(e' : g ⊢ h) →
-- --           ⟜-app ∘g (id ,⊗ e) ∘g ⊗-unit-r⁻ ∘g ⟜-intro-ε e' ≡ e' ∘g e
-- --         q e e' =
-- --           q' e (e' ∘g ⊗-unit-l) ∙
-- --           cong ((e' ∘g ⊗-unit-l ∘g id ,⊗ e) ∘g_) (sym t)  ∙
-- --           cong (λ z → e' ∘g z ∘g e) ⊗-unit-l⁻l

-- --       p : ∀ e →
-- --         ⟜-app ∘g
-- --         (id ,⊗ e) ∘g
-- --         ⊗-unit-r⁻ ∘g
-- --         ⟜-intro-ε id ≡ e
-- --       p e = q e id

-- -- weirdAlg : ∀ b → Algebra (TraceBTys b) (λ n → ⊕[ b' ∈ _ ] Trace' b' n)
-- -- weirdAlg b n = ⊕ᴰ-elim (λ
-- --   { eof' →
-- --     ⊕ᴰ-in b
-- --     ∘g ⊕ᴰ-elim (λ { n≡0 → ⊕ᴰ-elim (λ { b≡true →
-- --     roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in n≡0 ∘g ⊕ᴰ-in b≡true }) })
-- --   ; open' →
-- --     ⊸-intro⁻ (⊕ᴰ-elim λ b' → ⊸-intro (⊕ᴰ-in b' ∘g roll ∘g ⊕ᴰ-in open'))
-- --   ; close' → ⊕ᴰ-elim λ { n-1 → ⊸-intro⁻ (⊕ᴰ-elim λ b' → ⊸-intro (⊕ᴰ-in b' ∘g roll ∘g ⊕ᴰ-in close' ∘g ⊕ᴰ-in n-1)) }
-- --   ; leftovers' →
-- --     ⊕ᴰ-in b ∘g
-- --     ⊕ᴰ-elim (λ n-1 → ⊕ᴰ-elim (λ { b≡false → roll ∘g ⊕ᴰ-in leftovers' ∘g ⊕ᴰ-in n-1 ∘g ⊕ᴰ-in b≡false }))
-- --   ; unexpected' → ⊕ᴰ-in b ∘g ⊕ᴰ-elim λ n,b≡0,false → roll ∘g ⊕ᴰ-in unexpected' ∘g ⊕ᴰ-in n,b≡0,false
-- --   })

-- -- EOF' : ε ⊢ Trace' true 0
-- -- EOF' = roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl

-- -- OPEN' : ∀ {n b} → literal [ ⊗ Trace' b (suc n) ⊢ Trace' b n
-- -- OPEN' = roll ∘g ⊕ᴰ-in open'

-- -- CLOSE' : ∀ {n b} → literal ] ⊗ Trace' b n ⊢ Trace' b (suc n)
-- -- CLOSE' = roll ∘g ⊕ᴰ-in close' ∘g ⊕ᴰ-in (_ , Eq.refl)



