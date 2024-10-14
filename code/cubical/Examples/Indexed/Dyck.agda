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
open import Grammar.Equalizer Alphabet
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
  genBALANCED (suc n) = BALANCED ,⊗ id ∘g ⊗-assoc4

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
  upgradeBalancedBuilder (suc n) f =
    (λ i →
      (⟜-β (⟜-app ,⊗ id ∘g ⊗-assoc) i) ∘g
        (⟜-intro (BALANCED ∘g lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id)
        ∘g ⊗-assoc⁻4))
        ,⊗ f)
    ∙ (λ i →
      ⟜-app ,⊗ id
      ∘g ⊗-assoc⊗-intro {f = ⟜-intro (BALANCED ∘g lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id) ∘g ⊗-assoc⁻4)}{f' = id}{f'' = id} i
      ∘g id ,⊗ f)
    ∙ (λ i →
        (⟜-β (BALANCED ∘g lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id) ∘g ⊗-assoc⁻4) i) ,⊗ id
        ∘g ⊗-assoc
        ∘g id ,⊗ f
      )
    ∙ (λ i →
       BALANCED ,⊗ id
       ∘g (lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ id)) ,⊗ id
       ∘g ⊗-assoc⁻4⊗-assoc i
       ∘g id ,⊗ f)
    ∙ (λ i → BALANCED ,⊗ id
        ∘g ⊗-assoc4⊗-intro {f = lowerG}{f' = ⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻}{f'' = lowerG}{f''' = (⟜-app ∘g lowerG ,⊗ id)}{f'''' = id} (~ i)
        ∘g id ,⊗ id ,⊗ id ,⊗ ⊗-assoc
        ∘g ⊗-assoc⁻4
        ∘g id ,⊗ f)
    ∙ (λ i → BALANCED ,⊗ id
        ∘g ⊗-assoc4
        ∘g lowerG ,⊗ (⟜-app ∘g lowerG ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ lowerG ,⊗ ((⟜-app ∘g lowerG ,⊗ id) ,⊗ id)
        ∘g id ,⊗ id ,⊗ id ,⊗ ⊗-assoc
        ∘g ⊗-assoc⁻4⊗-intro {f = id}{f' = id}{f'' = id}{f''' = id}{f'''' = f} i)
    ∙ (λ i → BALANCED ,⊗ id
        ∘g ⊗-assoc4
        ∘g lowerG ,⊗ ((⟜-app ∘g (id ,⊗ NIL) ∘g ⊗-unit-r⁻⊗-intro {f = lowerG} (~ i)) ,⊗ lowerG ,⊗ ((⟜-app ∘g lowerG ,⊗ id) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ f))
        ∘g ⊗-assoc⁻4)
    ∙ (
      λ i → BALANCED ,⊗ id
        ∘g ⊗-assoc4
        ∘g id ,⊗ (⟜-app ,⊗ id)
        ∘g id ,⊗ ((id ,⊗ NIL) ,⊗ id)
        ∘g id ,⊗ ⊗-assoc⊗-unit-l⁻ (~ i)
        ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ ((⟜-app ∘g lowerG ,⊗ id) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ f)
        ∘g ⊗-assoc⁻4
      )
    ∙ (λ i →
        BALANCED ,⊗ id
        ∘g ⊗-assoc4
        ∘g id ,⊗ (⟜-app ,⊗ id)
        ∘g id ,⊗ (⊗-assoc⊗-intro {f = id}{f' = NIL}{f'' = id} (~ i))
        ∘g id ,⊗ (id ,⊗ ⊗-unit-l⁻)
        ∘g lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (⟜-app ,⊗ id ∘g (⊗-assoc⊗-intro {f = lowerG}{f' = id}{f'' = id} (~ i)) ∘g id ,⊗ f)
        ∘g ⊗-assoc⁻4
      )
    ∙ λ i → (BALANCED ,⊗ id ∘g ⊗-assoc4) ∘g
      id ,⊗ (⟜-β (⟜-app ,⊗ id ∘g ⊗-assoc) (~ i) ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻)) ∘g
      lowerG ,⊗ (lowerG) ,⊗ lowerG ,⊗ (⟜-β (⟜-app ,⊗ id ∘g ⊗-assoc) (~ i) ∘g lowerG ,⊗ f)
      ∘g ⊗-assoc⁻4

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
  ; (close' n-1 Eq.refl) → (NIL ,⊗ id ∘g ⊗-unit-l⁻) ∘g lowerG ,⊗ lowerG
  })

genMkTree : ∀ n → Trace true n ⊢ GenDyck n
genMkTree n = rec (TraceTys _) genMkTreeAlg _

mkTree : Trace true 0 ⊢ IndDyck
mkTree = genMkTree 0

opaque
  unfolding ⊗-intro
  genMkTree-β-OPEN : ∀ {n} → genMkTree n ∘g OPEN ≡ genBALANCED n ∘g id ,⊗ genMkTree (suc n)
  genMkTree-β-OPEN = refl

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

-- buildTraceβBalanced :
--   buildTrace ∘g roll ∘g ⊕ᴰ-in balanced'
--   ≡ &ᴰ-intro λ n → ⟜-intro
--     (({!\!}
--      ∘g ⊗-assoc⁻4
--     )
--     ∘g (lowerG ,⊗ (buildTrace ∘g lowerG) ,⊗ lowerG ,⊗ (buildTrace ∘g lowerG)) ,⊗ id)

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

{-

  genAppend' n (balanced(lp, d₁, rp, d₂)) (genMkTree n t)
  ≡ genBAL n lp (d₁ , rp , genAppend' )


-}

{-

  This doesn't seem to work, even though it seems provable by induction:

  we want to show that

  d : IndDyck ⊢ (λ& n → λ⟜ t → genMkTree n (buildTrace n d t))
                ≡ (λ& n → λ⟜ t → genAppend' n d (genMkTree n t))

  By induction on d

  n:ℕ ; e : ε , t : Trace n ⊢
    genMkTree n (buildTrace n (nil(e)) t)
    ≡ genMkTree n t
    ≡ genAppend' n nil(e) (genMkTree n t)  [ by defn of genAppend' ]

  n:ℕ ; lp : LP , d₁ : IndDyck , rp : RP , d₂ : IndDyck ⊢
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

  but I don't really see how to structure this inductive argument as
  an instance of the universal property of fold.

  The issue is that the universal property allows you to prove two
  functions are equivalent if you can prove they both satisfy the same
  recurrence relation, but there doesn't seem to be a way to describe
  the balanced case as a recurrence because we need to know the left
  subcall inductively



-}

lhs rhs : IndDyck ⊢ &[ n ∈ _ ] (GenDyck n ⟜ Trace true n)
lhs = (&ᴰ-intro λ n → ⟜-intro (genMkTree n ∘g ⟜-app) ∘g &ᴰ-π n) ∘g buildTrace

rhs = ((&ᴰ-intro λ n → ⟜-intro (⟜-app ∘g id ,⊗ genMkTree n) ∘g &ᴰ-π n) ∘g genAppend')

pfAlg : Algebra DyckTy (λ _ → equalizer lhs rhs)
pfAlg _ =
  eq-intro _ _ (roll ∘g map (DyckTy _) (λ _ → eq-π _ _))
    pf
  where
    opaque
      unfolding ⊗-intro
      pf : lhs ∘g roll ∘g map (DyckTy _) (λ _ → eq-π lhs rhs)
           ≡ rhs ∘g roll ∘g map (DyckTy _) (λ _ → eq-π _ _)
      pf = ⊕ᴰ≡ _ _ λ
        { nil' → &ᴰ≡ _ _ λ n →
          ⟜-intro-natural
          ∙ cong ⟜-intro
            ((λ i → genMkTree n ∘g ⟜-β ⊗-unit-l i ∘g lowerG ,⊗ id)
            ∙ λ i → upgradeNilBuilder n (genMkTree n) (~ i) ∘g lowerG ,⊗ id)
          ∙ sym ⟜-intro-natural
        ; balanced' → &ᴰ≡ _ _ λ n →
          ⟜-intro-natural ∙
          cong ⟜-intro
            ((λ i → genMkTree n
              ∘g ⟜-β (OPEN
                ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc n) ,⊗ id)
                ∘g id ,⊗ id ,⊗ CLOSE
                ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
                ∘g ⊗-assoc⁻4
                ∘g (lowerG ,⊗ lowerG {ℓ-zero} ,⊗ lowerG ,⊗ lowerG {ℓ-zero}) ,⊗ id) i
              ∘g (id ,⊗ (liftG {ℓ-zero} ∘g buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id ,⊗ ((liftG {ℓ-zero} ∘g buildTrace ∘g eq-π lhs rhs ∘g lowerG))) ,⊗ id)
            ∙ (λ i → genBALANCED n
                ∘g id ,⊗ genMkTree (suc n)
                ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc n) ,⊗ id)
                ∘g id ,⊗ id ,⊗ CLOSE
                ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
                ∘g ⊗-assoc⁻4⊗-intro {f = lowerG}{f' = buildTrace ∘g eq-π lhs rhs ∘g lowerG}{f'' = lowerG}{f''' = buildTrace ∘g eq-π lhs rhs ∘g lowerG}{f'''' = id} i)
            ∙ (λ i → genBALANCED n
                ∘g id ,⊗ (⟜-β (genMkTree (suc n) ∘g ⟜-app) (~ i) ∘g (&ᴰ-π (suc n) ∘g (buildTrace ∘g eq-π lhs rhs)) ,⊗ id)
                ∘g id ,⊗ id ,⊗ CLOSE
                ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
                ∘g (lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id)
                ∘g ⊗-assoc⁻4)
            -- by inductive hypothesis for the left subtree
            ∙ (λ i → genBALANCED n
                ∘g id ,⊗ (⟜-app ∘g (&ᴰ-π (suc n) ∘g eq-π-pf lhs rhs i) ,⊗ id)
                ∘g id ,⊗ id ,⊗ CLOSE
                ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
                ∘g (lowerG ,⊗ lowerG ,⊗ lowerG ,⊗ (buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id)
                ∘g ⊗-assoc⁻4)
            ∙ (λ i → genBALANCED n
                ∘g id ,⊗ (⟜-β (⟜-app ∘g id ,⊗ genMkTree (suc n)) i ∘g (&ᴰ-π (suc n) ∘g genAppend') ,⊗ id)
                ∘g id ,⊗ id ,⊗ CLOSE
                ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id)
                ∘g (lowerG ,⊗ (eq-π lhs rhs ∘g lowerG) ,⊗ lowerG ,⊗ (buildTrace ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id)
                ∘g ⊗-assoc⁻4)
            ∙ (λ i → genBALANCED n
                ∘g id ,⊗ (⟜-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
                ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-β (genMkTree n ∘g ⟜-app) (~ i) ∘g (&ᴰ-π n ∘g buildTrace ∘g eq-π lhs rhs) ,⊗ id)
                ∘g (lowerG ,⊗ (upgradeBuilder (suc n) ∘g append' ∘g eq-π lhs rhs ∘g lowerG) ,⊗ lowerG ,⊗ lowerG ,⊗ id)
                ∘g ⊗-assoc⁻4)
            -- inductive hypothesis 
            ∙ ((λ i → genBALANCED n
                ∘g id ,⊗ (⟜-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
                ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g (&ᴰ-π n ∘g eq-π-pf lhs rhs i) ,⊗ id)
                ∘g (lowerG ,⊗ (upgradeBuilder (suc n) ∘g append' ∘g eq-π lhs rhs ∘g lowerG) ,⊗ lowerG ,⊗ lowerG ,⊗ id)
                ∘g ⊗-assoc⁻4))
            ∙ ((λ i → genBALANCED n
                ∘g id ,⊗ (⟜-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
                ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-β (⟜-app ∘g id ,⊗ genMkTree n) i ∘g upgradeBuilder n ,⊗ id)
                ∘g (lowerG ,⊗ (upgradeBuilder (suc n) ∘g append' ∘g eq-π lhs rhs ∘g lowerG) ,⊗ lowerG ,⊗ (append' ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id)
                ∘g ⊗-assoc⁻4))
            ∙ (λ i → genBALANCED n
                ∘g id ,⊗ (⟜-app ∘g id ,⊗ (NIL ,⊗ id ∘g ⊗-unit-l⁻))
                ∘g id ,⊗ id ,⊗ id ,⊗ ⟜-app
                ∘g lowerG ,⊗ (upgradeBuilder (suc n) ∘g lowerG {ℓ-zero}) ,⊗ lowerG ,⊗ ((upgradeBuilder n) ∘g lowerG {ℓ-zero}) ,⊗ genMkTree n
                ∘g ⊗-assoc⁻4⊗-intro {f = id}{f' = liftG {ℓ-zero} ∘g append' ∘g eq-π lhs rhs ∘g lowerG}{f'' = id}{f''' = liftG {ℓ-zero} ∘g append' ∘g eq-π lhs rhs ∘g lowerG}{f'''' = id} (~ i)
              )
            ∙ (λ i →
              upgradeBalancedBuilder n (genMkTree n) (~ i)
              ∘g (id ,⊗ (liftG {ℓ-zero} ∘g append' ∘g eq-π lhs rhs ∘g lowerG) ,⊗ id ,⊗ ((liftG {ℓ-zero} ∘g append' ∘g eq-π lhs rhs ∘g lowerG))) ,⊗ id))
          ∙ sym ⟜-intro-natural
        }

genRetr :
  Path (IndDyck ⊢ &[ n ∈ _ ] (GenDyck n ⟜ Trace true n))
    lhs
    rhs
genRetr = equalizer-section _ _
  (rec DyckTy pfAlg _)
  (ind-id' DyckTy (compHomo DyckTy (initialAlgebra DyckTy) pfAlg (initialAlgebra DyckTy)
    ((λ _ → eq-π lhs rhs) , λ _ → eq-π-is-homo)
    (recHomo DyckTy pfAlg)) _)
  where
    opaque
      unfolding eq-π eq-intro
      eq-π-is-homo : eq-π lhs rhs ∘g pfAlg _ ≡ roll ∘g map (DyckTy _) (λ _ → eq-π lhs rhs)
      eq-π-is-homo = ⊕ᴰ≡ _ _ λ
        { nil' → refl
        ; balanced' → refl
        }

Dyck≅Trace : StrongEquivalence IndDyck (Trace true 0)
Dyck≅Trace =
  unambiguousRetract→StrongEquivalence
    (⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g &ᴰ-π 0 ∘g genBuildTrace 0)
    mkTree
    (mkTree ∘g ⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g &ᴰ-π 0 ∘g buildTrace
     ≡⟨ (λ i → ⟜-mapCod-postcompε mkTree EOF (~ i) ∘g &ᴰ-π 0 ∘g buildTrace) ⟩
     ⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g ⟜-mapCod mkTree ∘g &ᴰ-π 0 ∘g buildTrace
     ≡⟨ refl ⟩
     ⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻ ∘g &ᴰ-π 0 ∘g (&ᴰ-intro λ n → ⟜-mapCod (genMkTree n) ∘g &ᴰ-π n) ∘g buildTrace
     ≡⟨ cong (((⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g &ᴰ-π 0) ∘g_) genRetr ⟩
     (⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g &ᴰ-π 0 ∘g (&ᴰ-intro λ n → ⟜-intro (⟜-app ∘g id ,⊗ genMkTree n) ∘g &ᴰ-π n) ∘g genAppend'
     ≡⟨ refl ⟩
     (⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g ⟜-mapDom mkTree ∘g &ᴰ-π 0 ∘g genAppend'
     ≡⟨ refl ⟩
     (⟜-app ∘g id ,⊗ EOF ∘g ⊗-unit-r⁻) ∘g ⟜-mapDom mkTree ∘g append'
     ≡⟨ ((λ i → ⟜-mapDom-postcompε mkTree EOF i ∘g append')) ⟩
     ⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ∘g append'
     ≡⟨ append-nil-r' ⟩
    id ∎)
    isUnambiguousTrace
