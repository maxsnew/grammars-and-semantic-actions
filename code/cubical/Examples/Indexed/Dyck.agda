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

parse : string ⊢ &[ n ∈ ℕ ] ⊕[ b ∈ _ ] Trace n b
parse = foldKL*r _ (record { the-ℓ = ℓ-zero ; G = _
    ; nil-case = LinΠ-intro (Nat.elim
      (LinΣ-intro true ∘g roll ∘g LinΣ-intro eof' ∘g LinΣ-intro Eq.refl ∘g LinΣ-intro Eq.refl ∘g id)
      (λ n-1 _ → LinΣ-intro false ∘g roll ∘g LinΣ-intro leftovers' ∘g LinΣ-intro (_ , Eq.refl) ∘g LinΣ-intro Eq.refl ∘g id))
    ; cons-case = LinΠ-intro λ n → ⟜-intro⁻ (LinΣ-elim (λ
      { [ → ⟜-intro {k = Goal n} (⊸-intro⁻ (
        (LinΣ-elim λ b → ⊸-intro {k = Goal n}
          (LinΣ-intro b ∘g roll ∘g LinΣ-intro open'))
        ∘g LinΠ-app (suc n)))
      ; ] → ⟜-intro {k = Goal n} (Nat.elim {A = λ n → _ ⊢ Goal n}
          (LinΣ-intro false ∘g roll ∘g LinΣ-intro unexpected' ∘g LinΣ-intro Eq.refl ∘g id ,⊗ ⊤-intro)
          (λ n-1 _ →
          ⊸-intro⁻ ((LinΣ-elim λ b → ⊸-intro {k = Goal (suc n-1)} (LinΣ-intro b ∘g roll ∘g LinΣ-intro close' ∘g LinΣ-intro (_ , Eq.refl)))
            ∘g LinΠ-app n-1))
          n) })) })
    where
      Goal : ℕ → Grammar ℓ-zero
      Goal n = ⊕[ b ∈ Bool ] Trace n b


GenIndDyck : ℕ × Bool → Grammar ℓ-zero
GenIndDyck (n , false) = ⊤
GenIndDyck (n , true) =
      Nat.elim IndDyck (λ _ GID⟨n⟩ → IndDyck ⊗ literal ] ⊗ GID⟨n⟩)
      n

mkTreeAlg : Algebra TraceTys GenIndDyck
mkTreeAlg (n , b) = LinΣ-elim (λ
      { eof' → LinΣ-elim (λ { Eq.refl → LinΣ-elim λ { Eq.refl → roll ∘g ⊕ᴰ-in nil' } })
      ; open' → Bool.elim {A = λ b → literal [ ⊗ GenIndDyck (suc n , b)  ⊢ GenIndDyck (n , b)}
          (balance~ n)
          ⊤-intro b
      ; close' → LinΣ-elim (λ { (n-1 , Eq.refl) → Bool.elim
                                                   {A =
                                                    λ b →
                                                      Term (literal ] ⊗ GenIndDyck (n-1 , b)) (GenIndDyck (suc n-1 , b))}
        (⟜0⊗ (roll ∘g LinΣ-intro nil'))
        ⊤-intro
        b } )
      ; leftovers' → LinΣ-elim λ { (n-1 , Eq.refl) → LinΣ-elim λ { Eq.refl → ⊤-intro } }
      ; unexpected' → LinΣ-elim λ { Eq.refl → ⊤-intro }
      })
  where
    balance~ : ∀ n → literal [ ⊗ IndDyck ⊗ literal ] ⊗ GenIndDyck (n , true) ⊢ GenIndDyck (n , true)
    balance~ zero = roll ∘g ⊕ᴰ-in balanced'
    balance~ (suc n) = ⟜4⊗ (⟜4-intro-ε (roll ∘g ⊕ᴰ-in balanced'))

mkTree : Trace zero true ⊢ IndDyck
mkTree = rec TraceTys mkTreeAlg (0 , true)

TraceAction : Unit → Grammar ℓ-zero
TraceAction _ = &[ n ∈ ℕ ] (Trace n true ⟜ Trace n true)

eTAlg : Algebra DyckTy TraceAction
eTAlg _ = LinΣ-elim (λ
      { nil' → LinΠ-intro (λ n → ⟜-intro-ε id)
      ; balanced' → LinΠ-intro λ n → ⟜-intro {k = Trace n true}
        (roll ∘g LinΣ-intro open'
        ∘g id ,⊗ ((⟜-app ∘g LinΠ-app (suc n) ,⊗ ((roll ∘g LinΣ-intro close' ∘g LinΣ-intro (_ , Eq.refl) ∘g id ,⊗ (⟜-app ∘g LinΠ-app n ,⊗ id)) ∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
        ∘g ⊗-assoc⁻)
      })

exhibitTrace' : IndDyck ⊢ Trace zero true
exhibitTrace' = ((⟜-app ∘g ⊸0⊗ (roll ∘g LinΣ-intro eof' ∘g LinΣ-intro Eq.refl ∘g LinΣ-intro Eq.refl)) ∘g LinΠ-app 0) ∘g rec DyckTy eTAlg _

Dyck≅Trace : StrongEquivalence IndDyck (Trace zero true)
Dyck≅Trace = mkStrEq exhibitTrace' mkTree
  {!!} -- use mkTreeAlg
  (ind-id' DyckTy (compHomo DyckTy (initialAlgebra DyckTy) eTAlg (initialAlgebra DyckTy)
    ((λ _ → mkTree ∘g ((⟜-app ∘g ⊸0⊗ (roll ∘g LinΣ-intro eof' ∘g LinΣ-intro Eq.refl ∘g LinΣ-intro Eq.refl)) ∘g LinΠ-app 0))
    , λ _ → ⊕ᴰ≡ _ _ (λ
      { nil' →
        cong
          (rec TraceTys mkTreeAlg (0 , true) ∘g_)
          (p (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl))
      ; balanced' →
        rec TraceTys mkTreeAlg (0 , true) ∘g
        ⟜-app ∘g
        id ,⊗ (roll ∘g
            ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
        ⊗-unit-r⁻ ∘g
        ⟜-intro {k = Trace 0 true}
          (roll ∘g LinΣ-intro open'
          ∘g id ,⊗ ((⟜-app ∘g LinΠ-app (suc 0) ,⊗ ((roll ∘g LinΣ-intro close' ∘g LinΣ-intro (_ , Eq.refl) ∘g id ,⊗ (⟜-app ∘g LinΠ-app 0 ,⊗ id)) ∘g ⊗-assoc⁻)) ∘g ⊗-assoc⁻)
          ∘g ⊗-assoc⁻)
          ≡⟨ cong ((rec TraceTys mkTreeAlg (0 , true)) ∘g_) (q' _ _) ⟩
        rec TraceTys mkTreeAlg (0 , true) ∘g
        roll ∘g
        LinΣ-intro open' ∘g
        -- Bool.elim {A = λ b → literal [ ⊗ GenIndDyck (suc 0 , b)  ⊢ GenIndDyck (0 , b)}
        --   (roll ∘g ⊕ᴰ-in balanced')
        --   ⊤-intro true ∘g
        id ,⊗
          (⟜-app ∘g
            LinΠ-app (suc 0) ,⊗
            (roll ∘g
              ⊕ᴰ-in close' ∘g
              ⊕ᴰ-in (0 , Eq.refl) ∘g id ,⊗ (⟜-app ∘g LinΠ-app 0 ,⊗ id) ∘g
              ⊗-assoc⁻) ∘g
           ⊗-assoc⁻) ∘g
        ⊗-assoc⁻ ∘g
        id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
        ⊗-unit-r⁻
        -- roll ∘g
        -- ⊕ᴰ-in balanced' ∘g
        -- id ,⊗ ({!id!} ∘g map (DyckTy _) {!!} ∘g {!id!}) ∘g
        -- id ,⊗
        --   (⟜-app ∘g
        --     LinΠ-app (suc 0) ,⊗
        --     (roll ∘g
        --       ⊕ᴰ-in close' ∘g
        --       ⊕ᴰ-in (0 , Eq.refl) ∘g id ,⊗ (⟜-app ∘g LinΠ-app 0 ,⊗ id) ∘g
        --       ⊗-assoc⁻) ∘g
        --    ⊗-assoc⁻) ∘g
        -- ⊗-assoc⁻ ∘g
        -- id ,⊗ (roll ∘g ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl) ∘g
        -- ⊗-unit-r⁻
          ≡⟨ {!!} ⟩
        roll ∘g
        map (DyckTy _)
          (λ z →
             mkTree ∘g
             (⟜-app ∘g
              ⊸0⊗
              (roll ∘g
               ⊕ᴰ-in eof' ∘g ⊕ᴰ-in Eq.refl ∘g ⊕ᴰ-in Eq.refl))
             ∘g LinΠ-app 0)
         ∘g ⊕ᴰ-in balanced'
        ∎
     }))
    (recHomo DyckTy eTAlg))
    tt)
    where
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
