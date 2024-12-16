open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.List hiding (init ; rec ; map)

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.LiftFunctor Alphabet
import Cubical.Data.Equality as Eq
open import Term Alphabet
open import Helper

private
  variable ℓN ℓN' ℓP ℓ : Level

record NFA ℓN : Type (ℓ-suc ℓN) where
  field
    Q : FinSet ℓN
    init : Q .fst
    isAcc : Q .fst → Bool
    transition : FinSet ℓN
    src : ⟨ transition ⟩ → ⟨ Q ⟩
    dst : ⟨ transition ⟩ → ⟨ Q ⟩
    label : ⟨ transition ⟩ → ⟨ Alphabet ⟩
    ε-transition : FinSet ℓN
    ε-src : ⟨ ε-transition ⟩ → ⟨ Q ⟩
    ε-dst : ⟨ ε-transition ⟩ → ⟨ Q ⟩

  decEqQ : Discrete ⟨ Q ⟩
  decEqQ = isFinSet→Discrete (str Q)

  matchesTransition :
    Discrete ⟨ Alphabet ⟩ →
    ⟨ transition ⟩ →
    ⟨ Q ⟩ →
    ⟨ Alphabet ⟩ →
    ⟨ Q ⟩ → DecProp ℓN
  matchesTransition discAlphabet t src' label' dst' =
     DecProp×
         (DecProp≡ (discreteLift {L' = ℓN} discAlphabet)
           (lift label') (lift (label t)))
         (DecProp×
           (DecProp≡ (discreteLift {L' = ℓN} decEqQ)
             (lift src') (lift (src t)))
           (DecProp≡ (discreteLift {L' = ℓN} decEqQ)
             (lift dst') (lift (dst t)))
          )

  hasTransition : Discrete ⟨ Alphabet ⟩ → ⟨ Q ⟩ →
    ⟨ Alphabet ⟩ → ⟨ Q ⟩ → DecProp ℓN
  hasTransition discAlphabet src' label' dst' =
    DecProp∃ transition (λ t →
      matchesTransition discAlphabet t src' label' dst')

  data Tag (q : ⟨ Q ⟩) : Type ℓN where
    stop : true Eq.≡ isAcc q → Tag q
    step : ∀ t → (src t Eq.≡ q) → Tag q
    stepε : ∀ t → (ε-src t Eq.≡ q) → Tag q

  TraceTy : (q : ⟨ Q ⟩) → Functor ⟨ Q ⟩
  TraceTy q = ⊕e (Tag q) λ
    { (stop x) → k ε*
    ; (step t x) → ⊗e (k (literal* (label t))) (Var (dst t))
    ; (stepε t x) → Var (ε-dst t) }
  Trace : (q : ⟨ Q ⟩) → Grammar ℓN
  Trace = μ TraceTy

  STOP : ∀ {q} → true Eq.≡ isAcc q → ε ⊢ Trace q
  STOP acc = roll ∘g ⊕ᴰ-in (stop acc) ∘g liftG ∘g liftG

  STEP : ∀ t → literal (label t) ⊗ Trace (dst t) ⊢ Trace (src t)
  STEP t = roll ∘g ⊕ᴰ-in (step _ Eq.refl) ∘g (liftG ∘g liftG) ,⊗ liftG

  STEPε : ∀ t → Trace (ε-dst t) ⊢ Trace (ε-src t)
  STEPε t = roll ∘g ⊕ᴰ-in (stepε t Eq.refl) ∘g liftG

  Parse : Grammar _
  Parse = Trace init

  TraceAlg = Algebra TraceTy

  -- module _ {ℓP}(P : Grammar ℓP) where
  --   L = ℓ-max ℓP ℓN
  --   Q' = Lift {j = L} ⟨ Q ⟩

  --   Tag' : Q' → Type L
  --   Tag' q = Lift {j = L} (Tag (lower q))

  --   TraceTy' : (q : Q')  → Functor Q'
  --   TraceTy' (lift q) = LiftFunctor ⟨ Q ⟩ (TraceTy q)

  --   STOP' : ∀ {q} → true Eq.≡ isAcc q → ε ⊢ μ TraceTy' (lift q)
  --   STOP' acc =
  --     roll
  --     ∘g ⊕ᴰ-in (lift (stop acc))
  --     ∘g liftG ∘g liftG ∘g liftG

  --   STEP' : ∀ t →
  --     literal (label t) ⊗ μ TraceTy' (lift (dst t)) ⊢
  --       μ TraceTy' (lift (src t))
  --   STEP' t =
  --     roll
  --     ∘g ⊕ᴰ-in (lift (step _ Eq.refl))
  --     ∘g (liftG ∘g liftG ∘g liftG) ,⊗ liftG

  --   STEPε' : ∀ t →
  --     μ TraceTy' (lift (ε-dst t)) ⊢ μ TraceTy' (lift (ε-src t))
  --   STEPε' t = roll ∘g ⊕ᴰ-in (lift (stepε t Eq.refl)) ∘g liftG

  --   PAlgTy : (q : Q') → Functor Q'
  --   PAlgTy q = ⊕e (Tag' q) λ
  --     { (lift (stop x)) → k (LiftG ℓN P)
  --     ; (lift (step t x)) →
  --       ⊗e (k (literal* (label t))) (Var (lift (dst t)))
  --     ; (lift (stepε t x)) → Var (lift (ε-dst t)) }

  --   PAlgebra : (g :  Q' → Grammar L) → Type L
  --   PAlgebra = Algebra PAlgTy

  --   initialPAlg : PAlgebra (μ PAlgTy)
  --   initialPAlg = initialAlgebra PAlgTy

  --   initialPAlg' : PAlgebra (λ (lift q) → μ TraceTy' (lift q) ⊗ P)
  --   initialPAlg' (lift q) = ⊕ᴰ-elim λ {
  --       (lift (stop acc)) →
  --         STOP' acc ,⊗ id
  --           ∘g ⊗-unit-l⁻
  --         ∘g lowerG ∘g lowerG
  --     ; (lift (step t Eq.refl)) →
  --        STEP' t ,⊗ id
  --        ∘g ⊗-assoc
  --        ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  --     ; (lift (stepε t Eq.refl)) →
  --       STEPε' t ,⊗ id
  --       ∘g lowerG
  --     }

  --   module _ (g :  Q' → Grammar L) (pAlg : PAlgebra g) where
  --     underlyingAlg : Algebra TraceTy' (λ q → g q ⟜ P)
  --     underlyingAlg q = ⊕ᴰ-elim (λ {
  --         (lift (stop acc)) →
  --           ⟜-intro
  --             ((pAlg q
  --             ∘g ⊕ᴰ-in (lift (stop acc)))
  --             ∘g liftG ∘g liftG
  --             ∘g ⊗-unit-l)
  --            ∘g lowerG ∘g lowerG ∘g lowerG
  --       ; (lift (step t Eq.refl)) →
  --         ⟜-intro
  --           (pAlg q
  --           ∘g ⊕ᴰ-in (lift (step t Eq.refl))
  --           ∘g id ,⊗ ⟜-app ∘g ⊗-assoc⁻
  --           ∘g ((liftG ∘g liftG) ,⊗ ⟜-mapCod liftG) ,⊗ id)
  --           ∘g (lowerG ∘g lowerG ∘g lowerG) ,⊗ lowerG
  --       ; (lift (stepε t Eq.refl)) →
  --         ⟜-intro (
  --           pAlg q
  --           ∘g ⊕ᴰ-in (lift (stepε t Eq.refl))
  --           ∘g liftG ∘g ⟜-app)
  --         ∘g lowerG
  --         })

  --     Prec : ∀ q → μ TraceTy q ⊗ P ⊢ g (lift q)
  --     Prec q =
  --       ⟜-intro⁻
  --         (rec _ underlyingAlg (lift q)
  --         ∘g liftF ⟨ Q ⟩)

  --     Prec' : ∀ q → μ TraceTy' (lift q) ⊗ P ⊢ g (lift q)
  --     Prec' q = ⟜-intro⁻ (rec _ underlyingAlg (lift q))

  --   -- open StrongEquivalence
  --   -- opaque
  --   --   unfolding ⊗-intro ⊗-unit-l⁻
  --   --   μP≅μ⊗P :
  --   --     ∀ q →
  --   --     StrongEquivalence
  --   --       (μ PAlgTy (lift q))
  --   --       (μ TraceTy' (lift q) ⊗ P)
  --   --   μP≅μ⊗P q .fun = rec _ initialPAlg' (lift q)
  --   --   μP≅μ⊗P q .inv =
  --   --     ⟜-intro⁻
  --   --       (rec _
  --   --         (underlyingAlg (μ PAlgTy) initialPAlg)
  --   --         (lift q))
  --   --   μP≅μ⊗P q .sec = λ i → {!!}
  --   --   μP≅μ⊗P q .ret =
  --   --     ind-id'
  --   --       PAlgTy
  --   --       (compHomo PAlgTy initialPAlg initialPAlg' initialPAlg
  --   --         ((λ (lift q) →
  --   --           ⟜-intro⁻
  --   --             (rec _
  --   --               (underlyingAlg (μ PAlgTy) initialPAlg) (lift q))) ,
  --   --          (λ (lift q) →
  --   --            ⊕ᴰ≡ _ _ λ {
  --   --              (lift (stop acc)) →
  --   --                {!!}
  --   --            ; (lift (step t Eq.refl)) → {!!}
  --   --            ; (lift (stepε t Eq.refl)) → {!!}}
  --   --          ))
  --   --         (recHomo PAlgTy initialPAlg'))
  --   --       (lift q)

  --   module _ (g :  Q' → Grammar L) (pAlg : PAlgebra g) where
  --     opaque
  --       unfolding ⊗-intro ⊗-unit-l⁻
  --       ∃PAlgHom :
  --         Homomorphism
  --           PAlgTy
  --           initialPAlg'
  --           pAlg
  --       ∃PAlgHom .fst (lift q) = Prec' g pAlg q -- Prec' g pAlg q
  --       ∃PAlgHom .snd (lift q) =
  --         ⊕ᴰ≡ _ _
  --           λ { (lift (stop acc)) →
  --               (λ i →
  --                 ⟜-app
  --                 ∘g (underlyingAlg g pAlg (lift q)
  --                     ∘g ⊕ᴰ-in (lift (stop acc))
  --                     )
  --                     ,⊗ id
  --                 ∘g (liftG ∘g liftG ∘g liftG) ,⊗ (lowerG ∘g lowerG)
  --                 ∘g ⊗-unit-l⁻) ∙
  --               (λ i →
  --                 (⟜-β (pAlg (lift q)
  --                   ∘g ⊕ᴰ-in (lift (stop acc))
  --                   ∘g ⊗-unit-l ∘g id ,⊗ (liftG ∘g liftG)) i ∘g ⊗-unit-l⁻)
  --                 ∘g lowerG ∘g lowerG) ∙
  --               (λ i →
  --                 pAlg (lift q)
  --                 ∘g ⊕ᴰ-in (lift (stop acc))
  --                 ∘g ⊗-unit-l⁻l i)
  --             ; (lift (step t Eq.refl)) →
  --                 (λ i →
  --                   ⟜-β
  --                     (pAlg (lift q)
  --                     ∘g ⊕ᴰ-in (lift (step t Eq.refl))
  --                     ∘g id ,⊗ ⟜-app
  --                     ∘g (liftG ∘g liftG) ,⊗ ⟜-mapCod liftG ,⊗ id
  --                     ∘g ⊗-assoc⁻) i
  --                   ∘g (id ,⊗ rec _ (underlyingAlg g pAlg) (lift (dst t))) ,⊗ id
  --                   ∘g ⊗-assoc
  --                   ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  --                 ) ∙
  --                 (λ i →
  --                   pAlg (lift q)
  --                   ∘g ⊕ᴰ-in (lift (step t Eq.refl))
  --                   ∘g (liftG ∘g liftG) ,⊗ liftG
  --                   ∘g id ,⊗ {!!}
  --                   ∘g ⊗-assoc⁻∘⊗-assoc≡id i
  --                   ∘g (lowerG ∘g lowerG) ,⊗ lowerG
  --                   -- pAlg (lift q)
  --                   -- ∘g ⊕ᴰ-in (lift (step t Eq.refl))
  --                   -- ∘g (liftG ∘g liftG) ,⊗ liftG
  --                   -- ∘g id ,⊗ Prec' g pAlg (dst t)
  --                   -- ∘g ⊗-assoc⁻∘⊗-assoc≡id i
  --                   -- ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  --                 )
  --             ; (lift (stepε t Eq.refl)) →
  --               (λ i →
  --                 ⟜-β
  --                   (pAlg (lift q)
  --                   ∘g ⊕ᴰ-in (lift (stepε t Eq.refl))
  --                   ∘g liftG
  --                   ∘g ⟜-app
  --                   ) i
  --                 ∘g rec _ (underlyingAlg g pAlg) (lift (ε-dst t)) ,⊗ id
  --                 ∘g lowerG
  --               )
  --             }
