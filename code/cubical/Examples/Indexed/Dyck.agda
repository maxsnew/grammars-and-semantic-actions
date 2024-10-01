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
open import Grammar.Maybe Alphabet hiding (μ)
open import Grammar.Equivalence Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term Alphabet

data DyckTag : Type ℓ-zero where
  nil' balanced' : DyckTag
DyckTy : Unit → Functor Unit
DyckTy _ = ⊕e DyckTag (λ
  { nil' → k ε
  ; balanced' → ⊗e (k (literal [)) (⊗e (Var _) (⊗e (k (literal ])) (Var _))) })
IndDyck : Grammar ℓ-zero
IndDyck = μ DyckTy _

NIL : ε ⊢ IndDyck
NIL = roll ∘g ⊕ᴰ-in nil'

BALANCED : literal [ ⊗ IndDyck ⊗ literal ] ⊗ IndDyck ⊢ IndDyck
BALANCED = roll ∘g ⊕ᴰ-in balanced'

append : IndDyck ⊗ IndDyck ⊢ IndDyck
append = ⟜-intro⁻ (rec DyckTy
  (λ { tt → ⊕ᴰ-elim (λ
    { nil'      → ⟜-intro-ε id
    ; balanced' → ⟜-intro
      (BALANCED
       -- using app NIL on the left here is a bit weird but I think it works
      ∘g id ,⊗ (⟜-app ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻) ,⊗ id ,⊗ ⟜-app
      ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻) }) })
  _)

-- Need this lemma for the retract property below
append-nil-r : append ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻ ≡ id
append-nil-r = {!!}

data TraceTag : Type where
  eof' open' close' leftovers' unexpected' : TraceTag
TraceTys : ℕ × Bool → Functor (ℕ × Bool)
TraceTys (n , b) = ⊕e TraceTag (λ
  { eof' → ⊕e (n Eq.≡ zero) (λ _ → ⊕e (b Eq.≡ true) λ _ → k ε)
  ; open' → ⊗e (k (literal [)) (Var (suc n , b))
  ; close' → ⊕e (Eq.fiber suc n) λ (n-1 , _) → ⊗e (k (literal ])) (Var (n-1 , b))
  ; leftovers' → ⊕e (Eq.fiber suc n) λ (n-1 , _) → ⊕e (b Eq.≡ false) λ _ → k ε
  ; unexpected' → ⊕e ((n , b) Eq.≡ (0 , false)) λ _ → ⊗e (k (literal ])) (k ⊤)
  })

Trace : ℕ → Bool → Grammar ℓ-zero
Trace n b = μ TraceTys (n , b)

OPEN : ∀ {n b} → literal [ ⊗ Trace (suc n) b ⊢ Trace n b
OPEN = roll ∘g ⊕ᴰ-in open'

CLOSE : ∀ {n b} → literal ] ⊗ Trace n b ⊢ Trace (suc n) b
CLOSE = roll ∘g ⊕ᴰ-in close' ∘g ⊕ᴰ-in (_ , Eq.refl)

parse : string ⊢ &[ n ∈ ℕ ] ⊕[ b ∈ _ ] Trace n b
parse = foldKL*r _ (record { the-ℓ = ℓ-zero ; G = _
    ; nil-case = &ᴰ-intro (Nat.elim
      (⊕ᴰ-in true ∘g roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl ∘g id)
      (λ n-1 _ → ⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in leftovers' ∘g ⊕ᴰ-in (_ , Eq.refl) ∘g ⊕ᴰ-in Eq.refl ∘g id))
    ; cons-case = &ᴰ-intro λ n → ⟜-intro⁻ (⊕ᴰ-elim (λ
      { [ → ⟜-intro {k = Goal n} (⊸-intro⁻ (
        (⊕ᴰ-elim λ b → ⊸-intro {k = Goal n}
          (⊕ᴰ-in b ∘g OPEN))
        ∘g &ᴰ-π (suc n)))
      ; ] → ⟜-intro {k = Goal n} (Nat.elim {A = λ n → _ ⊢ Goal n}
          (⊕ᴰ-in false ∘g roll ∘g ⊕ᴰ-in unexpected' ∘g ⊕ᴰ-in Eq.refl ∘g id ,⊗ ⊤-intro)
          (λ n-1 _ →
          ⊸-intro⁻ ((⊕ᴰ-elim λ b → ⊸-intro {k = Goal (suc n-1)} (⊕ᴰ-in b ∘g CLOSE))
            ∘g &ᴰ-π n-1))
          n) })) })
    where
      Goal : ℕ → Grammar ℓ-zero
      Goal n = ⊕[ b ∈ Bool ] Trace n b


GenIndDyck : ℕ × Bool → Grammar ℓ-zero
GenIndDyck (n , false) = ⊤
GenIndDyck (n , true) =
      Nat.elim IndDyck (λ _ GID⟨n⟩ → IndDyck ⊗ literal ] ⊗ GID⟨n⟩)
      n

-- | x : n ≡ 0 ∧ b ≡ true ∧ ε ⊢ let (refl, x) = x in let (refl , x) = empty in nil(empty) : GID n b
-- | x : [ ⊗ GID (suc n) true ⊢ GID n true
mkTreeAlg : Algebra TraceTys GenIndDyck
mkTreeAlg (n , b) = ⊕ᴰ-elim (λ
      { eof' → ⊕ᴰ-elim (λ { Eq.refl → ⊕ᴰ-elim λ { Eq.refl → roll ∘g ⊕ᴰ-in nil' } })
      ; open' → Bool.elim {A = λ b → literal [ ⊗ GenIndDyck (suc n , b)  ⊢ GenIndDyck (n , b)}
          (balance~ n)
          ⊤-intro b
      ; close' → ⊕ᴰ-elim (λ { (n-1 , Eq.refl) → Bool.elim
                                                   {A =
                                                    λ b →
                                                      Term (literal ] ⊗ GenIndDyck (n-1 , b)) (GenIndDyck (suc n-1 , b))}
        (⟜0⊗ (roll ∘g ⊕ᴰ-in nil'))
        ⊤-intro
        b } )
      ; leftovers' → ⊕ᴰ-elim λ { (n-1 , Eq.refl) → ⊕ᴰ-elim λ { Eq.refl → ⊤-intro } }
      ; unexpected' → ⊕ᴰ-elim λ { Eq.refl → ⊤-intro }
      })
  where
    balance~ : ∀ n → literal [ ⊗ IndDyck ⊗ literal ] ⊗ GenIndDyck (n , true) ⊢ GenIndDyck (n , true)
    balance~ zero = roll ∘g ⊕ᴰ-in balanced'
    balance~ (suc n) = ⟜4⊗ (⟜4-intro-ε (roll ∘g ⊕ᴰ-in balanced'))

genAppend : ∀ {n} → IndDyck ⊗ GenIndDyck (n , true) ⊢ GenIndDyck (n , true)
genAppend {zero} = append
genAppend {suc n} = ⟜2⊗ (⟜2-intro-ε append)

genMkTree : ∀ {n b} → Trace n b ⊢ GenIndDyck (n , b)
genMkTree = rec TraceTys mkTreeAlg _

mkTree : Trace zero true ⊢ IndDyck
mkTree = rec TraceTys mkTreeAlg (0 , true)

TraceAction : Unit → Grammar ℓ-zero
TraceAction _ = &[ n ∈ ℕ ] (Trace n true ⟜ Trace n true)

eTAlg : Algebra DyckTy TraceAction
eTAlg _ = ⊕ᴰ-elim (λ
      { nil' → &ᴰ-intro (λ n → ⟜-intro-ε id)
      ; balanced' → &ᴰ-intro λ n → ⟜-intro {k = Trace n true}
        (OPEN                                       -- combine with the open, making an n
        ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc n) ,⊗ id)      -- apply at (suc n)
        ∘g id ,⊗ id ,⊗ CLOSE                        -- combine it with the close, making a (suc n)
        ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π n ,⊗ id) -- apply the last one at n
        ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻) -- assoc a bunch
      })

EOF : ε ⊢ Trace zero true
EOF = roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl

appEOF : TraceAction _ ⊢ Trace zero true
appEOF = (⟜-app ∘g ⊸0⊗ EOF ∘g &ᴰ-π 0)

traceBuilder : IndDyck ⊢ TraceAction _
traceBuilder = rec DyckTy eTAlg _

genTraceBuilder : ∀ {m} →
  GenIndDyck (m , true) ⊢ &[ n ∈ _ ] (Trace (m + n) true ⟜ Trace n true)
genTraceBuilder {m = zero} = traceBuilder
genTraceBuilder {m = suc m} = &ᴰ-intro (λ n → ⟜-intro
  ((⟜-app ∘g (&ᴰ-π (suc (m + n)) ∘g traceBuilder) ,⊗ CLOSE)
   ∘g id ,⊗ id ,⊗ (⟜-app ∘g (&ᴰ-π n ∘g genTraceBuilder {m = m}) ,⊗ id)
   ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻))

exhibitTrace' : IndDyck ⊢ Trace zero true
exhibitTrace' = appEOF ∘g traceBuilder

-- prove this by induction and this should imply the retract property
genRetract :
  ∀ {n} →
  Path (IndDyck ⊗ Trace n true ⊢ GenIndDyck (n , true))
    (genMkTree ∘g ⟜-app ∘g (&ᴰ-π n ∘g traceBuilder) ,⊗ id)
    (genAppend {n = n} ∘g id ,⊗ genMkTree)
genRetract = {!!}

genSection :
  ∀ {n} →
  Path (Trace n true ⊢ Trace n true)
    -- seems unavoidable unfortunately
    (subst (λ m → Trace n true ⊢ Trace m true) (+-zero n)
      (⟜-app ∘g ⊸0⊗ EOF ∘g &ᴰ-π 0 ∘g genTraceBuilder {m = n} ∘g genMkTree))
    id
genSection = {!!}

-- mkTree ∘g ((⟜-app ∘g ⊸0⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl)) ∘g &ᴰ-π 0)

-- is a homomorphism from eTAlg to (initialAlgebra DyckTy)

Dyck≅Trace : StrongEquivalence IndDyck (Trace zero true)
Dyck≅Trace = mkStrEq exhibitTrace' mkTree
  {!!} -- use mkTreeAlg
  (ind-id' DyckTy (compHomo DyckTy (initialAlgebra DyckTy) eTAlg (initialAlgebra DyckTy)
    ((λ _ → mkTree ∘g appEOF)
    , λ _ → ⊕ᴰ≡ _ _ (λ
      { nil' →
        cong
          (rec TraceTys mkTreeAlg (0 , true) ∘g_)
          (p (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl))
      ; balanced' →
        mkTree ∘g appEOF ∘g eTAlg _ ∘g ⊕ᴰ-in balanced'
          ≡⟨ refl ⟩
        mkTree ∘g ⟜-app ∘g ⊸0⊗ EOF ∘g ⟜-intro {k = Trace 0 true}
          (OPEN
          ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id)
          ∘g id ,⊗ id ,⊗ CLOSE
          ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id)
          ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻)
          ≡⟨ {!!} ⟩
        mkTree ∘g OPEN
          ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id)
          ∘g id ,⊗ id ,⊗ CLOSE
          ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id)
          ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
          ∘g ⊸0⊗ EOF
          ≡⟨ refl ⟩
        BALANCED
          ∘g id ,⊗ rec TraceTys mkTreeAlg (1 , true)
          ∘g id ,⊗ (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id)
          ∘g id ,⊗ id ,⊗ CLOSE
          ∘g id ,⊗ id ,⊗ id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id)
          ∘g id ,⊗ id ,⊗ ⊗-assoc⁻ ∘g id ,⊗ ⊗-assoc⁻ ∘g ⊗-assoc⁻
          ∘g ⊸0⊗ EOF
          ≡⟨ {!!} ⟩ -- TODO: tedious but just βη
        BALANCED
          ∘g id ,⊗ (rec TraceTys mkTreeAlg (1 , true) ∘g (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id ∘g id ,⊗ (CLOSE ∘g id ,⊗ appEOF)))
          ≡⟨ (λ i → BALANCED ∘g id ,⊗ the-lemma i) ⟩
        BALANCED
          ∘g id ,⊗ (mkTree ∘g appEOF) ,⊗ id ,⊗ (mkTree ∘g appEOF)
          ∎
-- ⊸0⊗ : ε ⊢ k → l ⊢ l ⊗ k
-- ⊸0⊗ f = id ,⊗ f ∘g ⊗-unit-r⁻
  
        -- rec TraceTys mkTreeAlg (0 , true) ∘g
        -- ⟜-app ∘g
        -- id ,⊗ (roll ∘g
        --     ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
        -- ⊗-unit-r⁻ ∘g
        -- ⟜-intro {k = Trace 0 true}
        --   (roll ∘g ⊕ᴰ-in open'
        --   ∘g id ,⊗ ((⟜-app ∘g &ᴰ-π (suc 0) ,⊗ ((roll ∘g ⊕ᴰ-in close' ∘g ⊕ᴰ-in (_ , Eq.refl) ∘g id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id)) ∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
        --   ∘g ⊗-assoc⁻)
        --   ≡⟨ cong ((rec TraceTys mkTreeAlg (0 , true)) ∘g_) (q' _ _) ⟩
        -- rec TraceTys mkTreeAlg (0 , true) ∘g
        -- roll ∘g
        -- ⊕ᴰ-in open' ∘g
        -- -- Bool.elim {A = λ b → literal [ ⊗ GenIndDyck (suc 0 , b)  ⊢ GenIndDyck (0 , b)}
        -- --   (roll ∘g ⊕ᴰ-in balanced')
        -- --   ⊤-intro true ∘g
        -- id ,⊗
        --   (⟜-app ∘g
        --     &ᴰ-π (suc 0) ,⊗
        --     (roll ∘g
        --       ⊕ᴰ-in close' ∘g
        --       ⊕ᴰ-in (0 , Eq.refl) ∘g id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id) ∘g
        --       ⊗-assoc⁻) ∘g
        --    ⊗-assoc⁻) ∘g
        -- ⊗-assoc⁻ ∘g
        -- id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
        -- ⊗-unit-r⁻
        --   ≡⟨ (λ i → roll ∘g ⊕ᴰ-in balanced' ∘g id ,⊗ rec TraceTys mkTreeAlg (1 , true) ∘g ((id ,⊗ (⟜-app ∘g ⊗-intro (&ᴰ-π 1)
        --     (roll ∘g
        --      ⊕ᴰ-in close' ∘g
        --      ⊕ᴰ-in (0 , Eq.refl) ∘g
        --      id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id) ∘g ⊗-assoc⁻) ∘g ⊗-assoc⁻)
        --     ∘g ⊗-assoc⁻ ∘g id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g (id ,⊗ rec TraceTys mkTreeAlg (1 , true)) ∘g {!!}) ∘g id ,⊗ id ,⊗ {!!}) ∘g (⊗-assoc⁻ ∘g
        --      id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
        --      ⊗-unit-r⁻)) ⟩


        -- roll ∘g ⊕ᴰ-in balanced' ∘g id ,⊗ recHomo TraceTys mkTreeAlg .fst (1 , true) ∘g {!!} ∘g (⊗-assoc⁻ ∘g
        --      id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
        --      ⊗-unit-r⁻)
        -- -- roll ∘g
        -- -- ⊕ᴰ-in balanced' ∘g
        -- -- id ,⊗ ({!id!} ∘g map (DyckTy _) {!!} ∘g {!id!}) ∘g
        -- -- id ,⊗
        -- --   (⟜-app ∘g
        -- --     &ᴰ-π (suc 0) ,⊗
        -- --     (roll ∘g
        -- --       ⊕ᴰ-in close' ∘g
        -- --       ⊕ᴰ-in (0 , Eq.refl) ∘g id ,⊗ (⟜-app ∘g &ᴰ-π 0 ,⊗ id) ∘g
        -- --       ⊗-assoc⁻) ∘g
        -- --    ⊗-assoc⁻) ∘g
        -- -- ⊗-assoc⁻ ∘g
        -- -- id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
        -- -- ⊗-unit-r⁻
        --   ≡⟨ (λ i → roll ∘g ⊕ᴰ-in balanced' ∘g {!!} ) ⟩
        -- roll ∘g
        -- map (DyckTy _)
        --   (λ z →
        --      mkTree ∘g
        --      (⟜-app ∘g
        --       ⊸0⊗
        --       (roll ∘g
        --        ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl))
        --      ∘g &ᴰ-π 0)
        --  ∘g ⊕ᴰ-in balanced'
        -- ∎
     }))
    (recHomo DyckTy eTAlg))
    tt)
    where
      -- maybe generalize from 0 to n and prove ∀ n by induction?
      the-lemma :
        Path (TraceAction _ ⊗ literal ] ⊗ TraceAction _ ⊢ IndDyck ⊗ literal ] ⊗ IndDyck)
        (rec TraceTys mkTreeAlg ((suc 0) , true) ∘g (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id ∘g id ,⊗ (CLOSE ∘g id ,⊗ appEOF)))
        ((rec TraceTys mkTreeAlg (0 , true) ∘g appEOF) ,⊗ id ,⊗ (rec TraceTys mkTreeAlg (0 , true) ∘g appEOF))
      the-lemma = {!!}
   
      the-lemma' :
        Path (TraceAction _ ⊗ literal ] ⊗ Trace 0 true ⊢ IndDyck ⊗ literal ] ⊗ IndDyck)
        (rec TraceTys mkTreeAlg ((suc 0) , true) ∘g (⟜-app ∘g &ᴰ-π (suc 0) ,⊗ id ∘g id ,⊗ (CLOSE ∘g id ,⊗ id)))
        ((rec TraceTys mkTreeAlg (0 , true) ∘g appEOF) ,⊗ id ,⊗ (rec TraceTys mkTreeAlg (0 , true)))
      the-lemma' = {!!}
      -- TODO rename all of these lemmas and put them in the relevant external
      -- files
      opaque
        unfolding ε
        -- Epsilon.Properties
        u : unambiguous ε
        u = EXTERNAL.propParses→unambiguous isFinBracket λ w → isSetString _ _

      -- Epsilon.Properties
      s : ⊗-unit-l {g = ε} ≡ ⊗-unit-r {g = ε}
      s = u _ _

      -- Epsilon.Properties
      t : ⊗-unit-l⁻ {g = ε} ≡ ⊗-unit-r⁻ {g = ε}
      t =
        ⊗-unit-l⁻
          ≡⟨ cong (⊗-unit-l⁻ ∘g_) (sym ⊗-unit-r⁻r) ⟩
        ⊗-unit-l⁻ ∘g ⊗-unit-r ∘g ⊗-unit-r⁻
          ≡⟨ cong (λ z → ⊗-unit-l⁻ ∘g z ∘g ⊗-unit-r⁻) (sym s) ⟩
        ⊗-unit-l⁻ ∘g ⊗-unit-l ∘g ⊗-unit-r⁻
          ≡⟨ cong (_∘g ⊗-unit-r⁻) ⊗-unit-ll⁻ ⟩
        ⊗-unit-r⁻
        ∎

      opaque
        -- opaque so that ⊗-unit-r⁻ commutes for free
        unfolding ⊗-unit-r⁻ ⊗-unit-l⁻
        q' : ∀ {ℓg ℓh ℓk : Level}
          {g : Grammar ℓg}{h : Grammar ℓh}{k : Grammar ℓk}
          (e : ε ⊢ g)(e' : k ⊗ g ⊢ h) →
          ⟜-app ∘g (id ,⊗ e) ∘g ⊗-unit-r⁻ ∘g ⟜-intro e' ≡
            e' ∘g id ,⊗ e ∘g ⊗-unit-r⁻
        q' e e' = cong (_∘g (id ,⊗ e ∘g ⊗-unit-r⁻)) (⟜-β e')

        q : ∀ {ℓg ℓh : Level}
          {g : Grammar ℓg}{h : Grammar ℓh}
          (e : ε ⊢ g)(e' : g ⊢ h) →
          ⟜-app ∘g (id ,⊗ e) ∘g ⊗-unit-r⁻ ∘g ⟜-intro-ε e' ≡ e' ∘g e
        q e e' =
          q' e (e' ∘g ⊗-unit-l) ∙
          cong ((e' ∘g ⊗-unit-l ∘g id ,⊗ e) ∘g_) (sym t)  ∙
          cong (λ z → e' ∘g z ∘g e) ⊗-unit-l⁻l

      p : ∀ e →
        ⟜-app ∘g
        (id ,⊗ e) ∘g
        ⊗-unit-r⁻ ∘g
        ⟜-intro-ε id ≡ e
      p e = q e id

-- An alternate definition of traces that I think should work out better.
TraceBTys : Bool → ℕ → Functor ℕ
TraceBTys b n = ⊕e TraceTag (λ
  { eof' → ⊕e (n Eq.≡ zero) (λ _ → ⊕e (b Eq.≡ true) λ _ → k ε)
  ; open' → ⊗e (k (literal [)) (Var (suc n))
  ; close' → ⊕e (Eq.fiber suc n) λ (n-1 , _) → ⊗e (k (literal ])) (Var (n-1))
  ; leftovers' → ⊕e (Eq.fiber suc n) λ (n-1 , _) → ⊕e (b Eq.≡ false) λ _ → k ε
  ; unexpected' → ⊕e ((n , b) Eq.≡ (0 , false)) λ _ → ⊗e (k (literal ])) (k ⊤)
  })

Trace' : Bool → ℕ → Grammar _
Trace' b = μ (TraceBTys b)

parse' : string ⊢ &[ n ∈ ℕ ] ⊕[ b ∈ _ ] Trace' b n
parse' = foldKL*r _ (record { the-ℓ = _ ; G = _
  ; nil-case = {!!}
  ; cons-case = {!!} })

printAlg : ∀ b → Algebra (TraceBTys b) (λ _ → string)
printAlg b n = ⊕ᴰ-elim (λ
  { eof' → {!!}
  ; open' → {!!}
  ; close' → {!!}
  ; leftovers' → {!!}
  ; unexpected' → {!!}
  })

printTrace : ∀ {n b} → Trace' b n ⊢ string
printTrace = rec (TraceBTys _) (printAlg _) _

weirdAlg : ∀ b → Algebra (TraceBTys b) (λ n → ⊕[ b' ∈ _ ] Trace' b' n)
weirdAlg b n = ⊕ᴰ-elim (λ
  { eof' →
    ⊕ᴰ-in b
    ∘g ⊕ᴰ-elim (λ { n≡0 → ⊕ᴰ-elim (λ { b≡true →
    roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in n≡0 ∘g ⊕ᴰ-in b≡true }) })
  ; open' →
    ⊸-intro⁻ (⊕ᴰ-elim λ b' → ⊸-intro (⊕ᴰ-in b' ∘g roll ∘g ⊕ᴰ-in open'))
  ; close' → ⊕ᴰ-elim λ { n-1 → ⊸-intro⁻ (⊕ᴰ-elim λ b' → ⊸-intro (⊕ᴰ-in b' ∘g roll ∘g ⊕ᴰ-in close' ∘g ⊕ᴰ-in n-1)) }
  ; leftovers' →
    ⊕ᴰ-in b ∘g
    ⊕ᴰ-elim (λ n-1 → ⊕ᴰ-elim (λ { b≡false → roll ∘g ⊕ᴰ-in leftovers' ∘g ⊕ᴰ-in n-1 ∘g ⊕ᴰ-in b≡false }))
  ; unexpected' → ⊕ᴰ-in b ∘g ⊕ᴰ-elim λ n,b≡0,false → roll ∘g ⊕ᴰ-in unexpected' ∘g ⊕ᴰ-in n,b≡0,false
  })

Trace≅String : ∀ {n} → StrongEquivalence (⊕[ b ∈ _ ] Trace' b n) string
Trace≅String = mkStrEq
  (⊕ᴰ-elim (λ _ → printTrace))
  (&ᴰ-π _ ∘g parse')
  {!!}
  (⊕ᴰ≡ _ _ (λ b → ind' (TraceBTys b) {!!} {!!} {!!} {!!}))
