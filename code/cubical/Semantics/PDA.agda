module Semantics.PDA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as DM
open import Cubical.Data.W.Indexed
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.SumFin

open import Semantics.Grammar
open import Semantics.Term

private
  variable ℓ ℓ' : Level

module PDADefs ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) ((Γ₀ , isFinSetΓ₀) : FinSet ℓ) where
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  open TermDefs ℓ (Σ₀ , isFinSetΣ₀)

  Stack = List Γ₀

  record PDA : Type (ℓ-suc ℓ) where
    constructor mkPDA
    field
      Q : FinSet ℓ
      init : Q .fst
      isAcc : Q .fst → DecProp ℓ
      init-stack-sym : Γ₀
      δ : Q .fst → Σ₀ → Γ₀ → DM.Maybe (Q .fst × Stack)
      εδ : Q .fst → Γ₀ → DM.Maybe (Q .fst × Stack)
      isDet : ∀ q z →
        ((∀ c → fiber just (δ q c z)) → εδ q z ≡ nothing) ×
        (fiber just (εδ q z) → ∀ c → δ q c z ≡ nothing)

--     isDeterministic : Type ℓ
--     isDeterministic = ∀ q c z →
--       -- At most one transition per label
--       isProp (δ q c z .fst) ×
--       -- if there is an empty label, then no transitions for any characters
--       (isContr (δ q (inr _) z .fst) → ∀ (c' : Σ₀) → δ q (inl c') z .fst → ⊥)

    data PDATrace
      (q q' : Q .fst) :
      (l : Stack) → (w : String) → Type ℓ where
      nil : (q ≡ q') → (l : Stack) → Term ε-grammar (PDATrace q q' l)
      cons : ∀ {c} {z} {l} →
        (((nextState , push), fibs) : fiber just (δ q c z)) →
        Term
          (literal c ⊗ PDATrace nextState q' (rev(push) ++ l) )
          (PDATrace q q' (z ∷ l))
      ε-cons : ∀ {z} {l} →
        (((nextState , push), fibs) : fiber just (εδ q z)) →
        Term
          (PDATrace nextState q' (rev(push) ++ l) )
          (PDATrace q q' (z ∷ l))
      -- cons : ∀ {c} {g} {l} → (dst : δ q (inl c) g .fst) →
      --   Term
      --     (PDATrace
      --       (δ q (inl c) g .snd .fst .fst dst .fst)
      --       q'
      --       (rev(δ q (inl c) g .snd .fst .fst dst .snd) ++ l)
      --     )
      --     (PDATrace q q' (g ∷ l))
      -- ε-cons : ∀ {g} {l} → (dst : δ q (inr _) g .fst) →
      --   Term
      --     (PDATrace
      --       (δ q (inr _) g .snd .fst .fst dst .fst)
      --       q'
      --       (rev(δ q (inr _) g .snd .fst .fst dst .snd) ++ l)
      --     )
      --     (PDATrace q q' (g ∷ l))

--     module _ (isDet : isDeterministic) where
--       FromInit = (LinΣ[ q ∈ Q .fst ] PDATrace init q [ init-stack-sym ])

--       extendTrace' : (c : Σ₀) →
--         Term (FromInit ⊗ (literal c)) (Maybe FromInit)
--       extendTrace' c = {!!}

--       run : Term (KL* ⊕Σ₀) (Maybe FromInit)
--       run =
--         foldKL*l {g = ⊕Σ₀} {h = Maybe FromInit}
--           (Maybe-yes-intro {g = ε-grammar} {h = FromInit}
--             (λ x → init , nil refl [ init-stack-sym ] x))
--           (trans {g = Maybe FromInit ⊗ ⊕Σ₀} {h = Maybe (FromInit ⊗ ⊕Σ₀)} {k = Maybe FromInit}
--             swapMaybe -- (FromInit + ⊤) ⊗ ⊕Σ₀ ⊢ ((FromInit ⊗ ⊕Σ₀) + ⊤)
--             (Maybe-bind {g = FromInit ⊗ ⊕Σ₀} {h = FromInit}
--               (λ (s , tr , c , lit) → extendTrace' c (s , tr , lit))
--             )
--           )
--           where
--           swapMaybe : Term (Maybe FromInit ⊗ ⊕Σ₀) (Maybe (FromInit ⊗ ⊕Σ₀))
--           -- Some
--           swapMaybe {w} (s , inl x , c , lit) = inl (s , x , c , lit)
--           -- None
--           swapMaybe {w} (s , inr x , c , lit) = inr _


--   open PDA

-- module _ where
--   open PDADefs ℓ-zero (Fin 2 , isFinSetFin) (Fin 2 , isFinSetFin)
--   open PDADefs.PDA

--   0' : Fin 2
--   0' = fzero
--   1' : Fin 2
--   1' = fsuc fzero

--   A : Fin 2
--   A = fzero
--   Z : Fin 2
--   Z = fsuc fzero

--   p : Fin 3
--   p = fzero
--   q : Fin 3
--   q = fsuc fzero
--   r : Fin 3
--   r = fsuc (fsuc fzero)

--   0ⁿ1ⁿ : PDA
--   Q 0ⁿ1ⁿ = Fin 3 , isFinSetFin
--   init 0ⁿ1ⁿ = p
--   isAcc 0ⁿ1ⁿ x = ((x ≡ r) , (isSetFin _ _)) , (discreteFin x r)
--   init-stack-sym 0ⁿ1ⁿ = Z
--   -- 0'
--   -- p
--   δ 0ⁿ1ⁿ fzero (inl fzero) g = {!!}
--   -- q
--   δ 0ⁿ1ⁿ (fsuc fzero) (inl fzero) g = {!!}
--   -- r
--   δ 0ⁿ1ⁿ (fsuc (fsuc (inl x))) (inl fzero) g = {!!}
--   -- 1'
--   -- p
--   δ 0ⁿ1ⁿ fzero (inl (fsuc fzero)) g = {!!}
--   -- q
--   δ 0ⁿ1ⁿ (fsuc (inl x)) (inl (fsuc fzero)) g = {!!}
--   -- r
--   δ 0ⁿ1ⁿ (fsuc (fsuc (inl x))) (inl (fsuc fzero)) g = {!!}
--   -- ε
--   -- p
--   δ 0ⁿ1ⁿ fzero (fsuc tt) g = {!!}
--   -- q
--   δ 0ⁿ1ⁿ (fsuc fzero) (fsuc tt) g = {!!}
--   -- q
--   δ 0ⁿ1ⁿ (fsuc (fsuc (inl x))) (fsuc tt) g = {!!}

-- --   0ⁿ1ⁿ : PDA
-- --   Q 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
-- --   init 0ⁿ1ⁿ = lift (inl _)
-- --   isAcc 0ⁿ1ⁿ x =
-- --     ((x ≡ lift (fsuc (fsuc fzero))) , isSetLift isSetFin _ _) ,
-- --     discreteLift discreteFin x (lift (fsuc (fsuc fzero)))
-- --   init-stack-sym 0ⁿ1ⁿ = fzero
-- --   transition 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
-- --   src 0ⁿ1ⁿ (lift fzero) = lift (fzero)
-- --   dst 0ⁿ1ⁿ (lift fzero) = lift (fzero)
-- --   pop 0ⁿ1ⁿ (lift fzero) = fzero
-- --   push 0ⁿ1ⁿ (lift fzero) = fzero ∷ [ fsuc fzero ]
-- --   label 0ⁿ1ⁿ (lift fzero) = fzero
-- --   src 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (fzero)
-- --   dst 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (fzero)
-- --   pop 0ⁿ1ⁿ (lift (fsuc fzero)) = fsuc fzero
-- --   push 0ⁿ1ⁿ (lift (fsuc fzero)) = fsuc fzero ∷ [ fsuc fzero ]
-- --   label 0ⁿ1ⁿ (lift (fsuc fzero)) = fzero
-- --   src 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = lift (fsuc fzero)
-- --   dst 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = lift (fsuc fzero)
-- --   pop 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = fsuc fzero
-- --   push 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = []
-- --   label 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = fsuc fzero
-- --   ε-transition 0ⁿ1ⁿ = Lift (Fin 3) , isFinSetLift isFinSetFin
-- --   ε-src 0ⁿ1ⁿ (lift fzero) = lift (fzero)
-- --   ε-dst 0ⁿ1ⁿ (lift fzero) = lift (fsuc fzero)
-- --   ε-pop 0ⁿ1ⁿ (lift fzero) = (fsuc fzero)
-- --   ε-push 0ⁿ1ⁿ (lift fzero) = [ (fsuc fzero) ]
-- --   ε-src 0ⁿ1ⁿ (lift (fsuc fzero)) = lift fzero
-- --   ε-dst 0ⁿ1ⁿ (lift (fsuc fzero)) = lift (fsuc fzero)
-- --   ε-pop 0ⁿ1ⁿ (lift (fsuc fzero)) = fzero
-- --   ε-push 0ⁿ1ⁿ (lift (fsuc fzero)) = [ fzero ]
-- --   ε-src 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = lift (fsuc fzero)
-- --   ε-dst 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = lift (fsuc (fsuc fzero))
-- --   ε-pop 0ⁿ1ⁿ (lift (fsuc  (fsuc fzero))) = fzero
-- --   ε-push 0ⁿ1ⁿ (lift (fsuc (fsuc fzero))) = [ fzero ]

-- --   0ⁿ1ⁿParse : (w : String) → Type ℓ-zero
-- --   0ⁿ1ⁿParse w =
-- --     PDATrace 0ⁿ1ⁿ (0ⁿ1ⁿ .init) w [ 0ⁿ1ⁿ .init-stack-sym ]

-- --   mt : 0ⁿ1ⁿParse []
-- --   mt =
-- --     ε-cons {t = lift (fsuc fzero)}
-- --       (ε-cons {t = lift (fsuc (fsuc fzero))} (nil refl))

-- --   zeroone : 0ⁿ1ⁿParse (fzero ∷ [ fsuc fzero ])
-- --   zeroone =
-- --     cons {t = lift fzero}(
-- --       ε-cons {t = lift fzero}(
-- --         cons {t = lift (fsuc (fsuc fzero))}(
-- --           ε-cons {t = lift (fsuc (fsuc fzero))} (nil refl))))

-- --   zero⁴one⁴ :
-- --     0ⁿ1ⁿParse (
-- --       fzero ∷ fzero ∷ fzero ∷ fzero ∷
-- --       (fsuc fzero) ∷ (fsuc fzero) ∷ (fsuc fzero) ∷ [ fsuc fzero ])
-- --   zero⁴one⁴ =
-- --     cons {t = lift fzero}
-- --       (cons {t = lift (fsuc fzero)}
-- --         (cons {t = lift (fsuc fzero)}
-- --           (cons {t = lift (fsuc fzero)}
-- --             (ε-cons {t = lift fzero}
-- --               (cons {t = lift (fsuc (fsuc fzero))}
-- --                 (cons {t = lift (fsuc (fsuc fzero))}
-- --                   (cons {t = lift (fsuc (fsuc fzero))}
-- --                     (cons {t = lift (fsuc (fsuc fzero))}
-- --                       (ε-cons {t = lift (fsuc (fsuc fzero))} (nil refl))))))))))
