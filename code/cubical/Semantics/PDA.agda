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
      -- TODO change these to have a type of transitions with projections + determinism constraints
      δ : Q .fst → Σ₀ → Γ₀ → DM.Maybe (Q .fst × Stack)
      εδ : Q .fst → Γ₀ → DM.Maybe (Q .fst × Stack)
      isDet : ∀ q z →
        ((∀ c → fiber just (δ q c z)) → εδ q z ≡ nothing) ×
        (fiber just (εδ q z) → ∀ c → δ q c z ≡ nothing)

    data PDATrace
      (q q' : Q .fst) :
      (l l' : Stack) → (w : String) → Type ℓ where
      nil : (q ≡ q') → (l : Stack) → Term ε-grammar (PDATrace q q' l l)
      cons : ∀ c z {l} {l'} →
        (((nextState , push), fibs) : fiber just (δ q c z)) →
        Term
          (literal c ⊗ PDATrace nextState q' (rev(push) ++ l) l')
          (PDATrace q q' (z ∷ l) l')
      ε-cons : ∀ z {l} {l'} →
        (((nextState , push), fibs) : fiber just (εδ q z)) →
        Term
          (PDATrace nextState q' (rev(push) ++ l) l')
          (PDATrace q q' (z ∷ l) l')

    elimPDATrace :
      (P : ∀ q q' l l' → Grammar) →
      (nil-case : ∀ q l → Term ε-grammar (P q q l l)) →
      (cons-case : ∀ q q' c z l l' →
        (((nextState , push), fibs) : fiber just (δ q c z)) →
        Term
          (literal c ⊗ P nextState q' (rev(push) ++ l) l')
          (P q q' (z ∷ l) l')
      ) →
      (ε-cons-case : ∀ q q' z l l' →
        (((nextState , push), fibs) : fiber just (εδ q z)) →
        Term (P nextState q' (rev(push) ++ l) l') (P q q' (z ∷ l) l')
      ) →
      ∀ {q q' l l'} → Term (PDATrace q q' l l') (P q q' l l')
    elimPDATrace P nil-case cons-case ε-cons-case {q}{q'}{w = w}
      (nil pq l pw) =
      transport (cong (λ a → P q a l l w) pq) (nil-case q l pw)
    elimPDATrace P nil-case cons-case ε-cons-case
      (cons c z {l} {l'} fib x) =
      cons-case _ _ c z l l' fib
        ((([ c ] , (x .fst .fst .snd)) ,
        (x .fst .snd ∙ cong (_++ x .fst .fst .snd) (x .snd .fst))) ,
        (refl ,
          elimPDATrace P nil-case
            cons-case ε-cons-case (x .snd .snd)))
    elimPDATrace P nil-case cons-case ε-cons-case
      (ε-cons z {l} {l'} fib x) =
      ε-cons-case _ _ z l l' fib
        (elimPDATrace P nil-case cons-case ε-cons-case x)

    TraceFrom : (Q .fst) → Stack → Grammar
    TraceFrom q l = (LinΣ[ (q' , l') ∈ (Q .fst × Stack) ] PDATrace q q' l' l)

    FromInit = TraceFrom init [ init-stack-sym ]

    extendTrace' : ∀ {q l} → (c : Σ₀) →
      Term (TraceFrom q l ⊗ (literal c)) (MaybeGrammar (TraceFrom q l))
    extendTrace' {q} {l} c (s , Σtr , lit) =
      let ((q' , l') , tr) = Σtr in
      {!!}
      where
      inspectStack : ∀ q' l' →
        Term
        (PDATrace q q' l' l ⊗ (literal c))
        (MaybeGrammar (TraceFrom q l))
      inspectStack q' [] =
        MaybeGrammar-no-intro
          {g = PDATrace q q' [] l ⊗ literal c}
          {h = TraceFrom q l}
      inspectStack q' (z ∷ l') =
        DM.rec
          -- Transition for (c , z) is not defined
          (DM.rec
            -- Transition for ε not defined
            (MaybeGrammar-no-intro
              {g = PDATrace q q' (z ∷ l') l ⊗ literal c}
              {h = TraceFrom q l})
            -- Transition for ε defined
            (λ (next , push) →
              -- TODO extend by ε then try to transition by c
              {!!}
            )
            (εδ q z))
          -- Transition for (c , z) is defined
          (λ (next , push) →
            MaybeGrammar-yes-intro
              {g = PDATrace q q' (z ∷ l') l ⊗ literal c}
              {h = TraceFrom q l}
              (λ (s' , Σtr' , lit') →
                (next , rev push ++ l') ,
                literalCase
                  c q q' l' l z
                  ((next , push) , {!!})
                  (s' , (Σtr' , lit'))
              )
          )
          (δ q' c z)
        where
        -- There is a z on the head of the stack,
        -- the character c is the beginning of the input word,
        -- and the (c,z) transition is defined
        literalCase :
          (c : Σ₀) → (q q' : Q .fst) →
          (l' l : Stack) → (z : Γ₀) →
          (((nextState , push), fibs) : fiber just (δ q c z)) →
          Term
            (PDATrace q q' (z ∷ l') l  ⊗ (literal c))
            (PDATrace q nextState (rev(push) ++ l') l)
          -- TODO l vs l' in above line
        literalCase c q q' l' l z ((next , push), fibs) =
          ⊗--elim
            {g = PDATrace q q' (z ∷ l') l}
            {h = literal c}
            {k = PDATrace q next (rev(push) ++ l') l}
            {l = literal c}

      -- Term (PDATrace q₂ q''' l₂ l''')
      -- (LinearΣ-syntax
       -- (λ x → PDATrace q₂ next (rev push ++ l''') l₂ ⊗- literal c))
            (
            trans
              {g = PDATrace q q' (z ∷ l') l}
              {h =
                LinΣ[ x ∈ (Σ[ ((next , push), f) ∈ fiber just (δ q c z)] (q' ≡ next)) ]
                (PDATrace q next (rev push ++ l') l ⊗- literal c)}
              {k = PDATrace q next (rev push ++ l') l ⊗- literal c}
              (elimPDATrace
                the-P
                the-nil-case
                {!!}
                {!!}
                {q}{q'}{z ∷ l'}{l}
              )
              {!!}
            )
            {!!}
            where
            the-P : (q q' : Q .fst) → (l' l : Stack) → Grammar
            -- This doesn't work
            the-P q q' [] l = ⊥-grammar
            the-P q q' (z ∷ l') l =
              LinΣ[ x ∈ (Σ[ ((next , push), f) ∈ fiber just (δ q c z)] (q' ≡ next))]
                (PDATrace q next (rev push ++ l') l ⊗- literal c)

            the-nil-case : (q : Q .fst) → (l : Stack) → Term ε-grammar (the-P q q l l)
            the-nil-case q [] = {!!}
            the-nil-case q (x ∷ l) = {!!}


    run : Term (KL* ⊕Σ₀) (MaybeGrammar FromInit)
    run =
      foldKL*l {g = ⊕Σ₀} {h = MaybeGrammar FromInit}
        (MaybeGrammar-yes-intro {g = ε-grammar} {h = FromInit}
          (λ x → (init , [ init-stack-sym ]) , nil refl [ init-stack-sym ] x))
        (trans
          {g = MaybeGrammar FromInit ⊗ ⊕Σ₀}
          {h = MaybeGrammar (FromInit ⊗ ⊕Σ₀)}
          {k = MaybeGrammar FromInit}
          swapMaybeGrammar -- (FromInit + ⊤) ⊗ ⊕Σ₀ ⊢ ((FromInit ⊗ ⊕Σ₀) + ⊤)
          (MaybeGrammar-bind {g = FromInit ⊗ ⊕Σ₀} {h = FromInit}
            (λ (s , tr , c , lit) → extendTrace' c (s , tr , lit))
          )
        )
        where
        swapMaybeGrammar : Term (MaybeGrammar FromInit ⊗ ⊕Σ₀) (MaybeGrammar (FromInit ⊗ ⊕Σ₀))
        -- Some
        swapMaybeGrammar {w} (s , inl x , c , lit) = inl (s , x , c , lit)
        -- None
        swapMaybeGrammar {w} (s , inr x , c , lit) = inr _


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
