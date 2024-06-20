{-# OPTIONS -WnoUnsupportedIndexedMatch --lossy-unification #-}
module Semantics.NFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Grammar public
open import Semantics.DFA
open import Semantics.Helper
open import Semantics.Term

private
  variable ℓ ℓ' : Level

module NFADefs ℓ ((Σ₀ , isFinSetΣ₀) : FinSet ℓ) where
  open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)
  open StringDefs ℓ (Σ₀ , isFinSetΣ₀)
  open TermDefs ℓ (Σ₀ , isFinSetΣ₀)

  record NFA : Type (ℓ-suc ℓ) where
    constructor mkNFA
    field
      Q : FinSet ℓ
      init : Q .fst
      isAcc : Q .fst → DecProp ℓ
      transition : FinSet ℓ
      src : transition .fst → Q .fst
      dst : transition .fst → Q .fst
      label : transition .fst → Σ₀
      ε-transition : FinSet ℓ
      ε-src : ε-transition .fst → Q .fst
      ε-dst : ε-transition .fst → Q .fst

    decEqQ : Discrete (Q .fst)
    decEqQ = isFinSet→Discrete (Q .snd)

    acc? : Q .fst → Grammar
    acc? q = DecProp-grammar' (isAcc q)

    rej? : Q .fst → Grammar
    rej? q = DecProp-grammar' (negateDecProp (isAcc q))

    init? : Q .fst → Grammar
    init? q = DecProp-grammar'
      (((init ≡ q) , (isFinSet→isSet (Q .snd) _ _)) , (decEqQ init q))

    data NFATrace
      (q : Q .fst)
      (q-end : Q .fst) : (w : String) → Type ℓ where
      nil : (q ≡ q-end) →
        Term ε-grammar (NFATrace q q-end)
      cons : ∀ {t} →
        (src t ≡ q) →
        Term
          (literal (label t) ⊗ NFATrace (dst t) q-end) (NFATrace q q-end)
      ε-cons : ∀ {t} →
        (ε-src t ≡ q) →
        Term (NFATrace (ε-dst t) q-end) (NFATrace q q-end)

    elimNFATrace :
      (P : ∀ q q' → Grammar) →
      (nil-case : ∀ {q} → Term ε-grammar (P q q)) →
      (cons-case : ∀ {q}{q'}{t} → (src t ≡ q) →
        Term (literal (label t) ⊗ P (dst t) q') (P q q')) →
      (ε-cons-case : ∀ {q}{q'}{t} → (ε-src t ≡ q) →
        Term (P (ε-dst t) q') (P q q')) →
      ∀ {q}{q'} →
      Term (NFATrace q q') (P q q')
    elimNFATrace P nil-case cons-case ε-cons-case {q}{q'} (nil x y) =
      transport (cong (λ a → P q a _) x) (nil-case y)
    elimNFATrace P nil-case cons-case ε-cons-case (cons x y) =
      cons-case x ((y .fst) , ((y .snd .fst) ,
        (elimNFATrace P nil-case cons-case ε-cons-case (y .snd .snd))))
    elimNFATrace P nil-case cons-case ε-cons-case (ε-cons x y) =
      ε-cons-case x (elimNFATrace P nil-case cons-case ε-cons-case y)

    concatTrace : ∀ {q}{q'}{q''} →
      Term ((NFATrace q q') ⊗ (NFATrace q' q'')) (NFATrace q q'')
    concatTrace {q}{q'}{q''} =
      ⊗--elim
        {g = NFATrace q q'} {h = NFATrace q' q''} {k = NFATrace q q''} {l = NFATrace q' q''}
        (elimNFATrace (λ a b → NFATrace a q'' ⊗- NFATrace b q'')
          (λ {q} →
            ⊗--intro {g = ε-grammar} {h = NFATrace q q''} {k = NFATrace q q''}
            (ε-extension-l {g = ε-grammar} {h = NFATrace q q''} {k = NFATrace q q''}
              (id {ε-grammar}) (id {NFATrace q q''})))
          (λ {q}{q'}{t} p →
             ⊗--intro
               {g = literal (label t) ⊗ ((NFATrace (dst t) q'') ⊗- NFATrace q' q'')}
               {h = NFATrace q' q''}
               {k = NFATrace q q''}
               (trans
                {g = ((literal (label t) ⊗ (NFATrace (dst t) q'' ⊗- NFATrace q' q'')) ⊗
                 NFATrace q' q'')}
                {h = literal (label t) ⊗ (NFATrace (dst t) q'')}
                {k = NFATrace q q''}
                (⊗-assoc
                  {g = literal (label t)} {h = NFATrace (dst t) q'' ⊗- NFATrace q' q''}
                  {k = NFATrace q' q''} {l = literal (label t) ⊗ NFATrace (dst t) q''}
                  (⊗-intro
                    {g = literal (label t)} {h = literal (label t)}
                    {k = (NFATrace (dst t) q'' ⊗- NFATrace q' q'') ⊗ NFATrace q' q''}
                    {l = NFATrace (dst t) q''}
                    (id {literal (label t)})
                    (⊗--elim
                      {g = NFATrace (dst t) q'' ⊗- NFATrace q' q''}
                      {h = NFATrace q' q''}
                      {k = NFATrace (dst t) q''}
                      {l = NFATrace q' q''}
                      (id {NFATrace (dst t) q'' ⊗- NFATrace q' q''})
                      (id {NFATrace q' q''}))) )
                (cons p))
          )
          (λ {q}{q'}{t} p →
            ⊗--intro {g = NFATrace (ε-dst t) q'' ⊗- NFATrace q' q''} {h = NFATrace q' q''}{k = NFATrace q q''}
              (trans
                {g = (NFATrace (ε-dst t) q'' ⊗- NFATrace q' q'') ⊗ NFATrace q' q''}
                {h = NFATrace (ε-dst t) q''}
                {k = NFATrace q q''}
                (⊗--elim
                  {g = (NFATrace (ε-dst t) q'' ⊗- NFATrace q' q'')}
                  {h = NFATrace q' q''}
                  {k = NFATrace (ε-dst t) q''}
                  {l = NFATrace q' q''}
                  (id {NFATrace (ε-dst t) q'' ⊗- NFATrace q' q''})
                  (id {NFATrace q' q''}))
                (ε-cons p))
          )
          {q} {q'})
        (id {NFATrace q' q''})

    Accepting : Type ℓ
    Accepting = Σ[ q ∈ Q .fst ] isAcc q .fst .fst

    Parses : Grammar
    Parses =
      LinΣ[ q ∈ Accepting ] NFATrace init (q .fst)

    open DFADefs ℓ (Σ₀ , isFinSetΣ₀)
    PowersetDFA : DFA
    PowersetDFA = ?




    -- Determinize :
    --   (D : DFA) →
    --   Term Parses (DFA.Parses D) →
    --   Term ∥ Parses ∥grammar (DFA.Parses D)
    -- Determinize = {!!}

--     negate : NFA
--     Q negate = Q
--     init negate = init
--     isAcc negate q = negateDecProp (isAcc q)
--     transition negate = transition
--     src negate = src
--     dst negate = dst
--     label negate = label
--     ε-transition negate = ε-transition
--     ε-src negate = ε-src
--     ε-dst negate = ε-dst

--   open NFA
--   module _ (c : Σ₀) where
--     literalNFA : NFA
--     fst (Q literalNFA) = Lift (Fin 2)
--     snd (Q literalNFA) = isFinSetLift isFinSetFin
--     init literalNFA = lift (inl tt)
--     fst (fst (isAcc literalNFA x)) = x ≡ lift (inr (inl tt))
--     snd (fst (isAcc literalNFA x)) = isSetLift isSetFin _ _
--     snd (isAcc literalNFA x) = discreteLift discreteFin _ _
--     transition literalNFA = Lift Unit , isFinSetLift isFinSetUnit
--     src literalNFA _ = lift (inl tt)
--     dst literalNFA _ = lift (inr (inl tt))
--     label literalNFA _ = c
--     ε-transition literalNFA = Lift ⊥ , isFinSetLift isFinSetFin
--     ε-src literalNFA x = ⊥.rec (lower x)
--     ε-dst literalNFA x = ⊥.rec (lower x)

--   emptyNFA : NFA
--   Q emptyNFA = Lift (Fin 2) , isFinSetLift isFinSetFin
--   init emptyNFA = lift fzero
--   isAcc emptyNFA x =
--     ((x ≡ lift (fsuc fzero)) , isSetLift isSetFin _ _) ,
--     discreteLift discreteFin x (lift (fsuc fzero))
--   transition emptyNFA = Lift ⊥ , isFinSetLift isFinSetFin
--   src emptyNFA (lift x) = ⊥.rec x
--   dst emptyNFA (lift x) = ⊥.rec x
--   label emptyNFA (lift x) = ⊥.rec x
--   ε-transition emptyNFA = Lift Unit , isFinSetLift isFinSetUnit
--   ε-src emptyNFA _ = emptyNFA .init
--   ε-dst emptyNFA _ = lift (fsuc fzero)

--   module _ (N : NFA) where
--     isDeterministic : Type ℓ
--     isDeterministic =
--       -- No ε-transitions
--       (N .ε-transition .fst ≃ Fin 0) ×
--       -- forall states
--       (∀ (q : N .Q .fst) →
--         -- there are only Σ₀-many transitions (may be redundant)
--         (fiber (N .dst) q ≃ Σ₀) ×
--         -- and there is exactly one for each label c
--         (∀ (c : Σ₀) →
--           isContr (Σ[ t ∈ fiber (N .dst) q ]
--            (N .label (t .fst) ≡ c))))

--     module _ (deter : isDeterministic) where
--       open DFADefs ℓ (Σ₀ , isFinSetΣ₀)
--       open DFADefs.DFA

--       deterministicNFA : DFA
--       Q deterministicNFA = N .Q
--       init deterministicNFA = N .init
--       isAcc deterministicNFA = N .isAcc
--       δ deterministicNFA q c =
--         N .dst (deter .snd q .snd c .fst .fst .fst)

--   module _ (N : NFA) where
--     h =
--       LinΣ[ q ∈ N .Q .fst ]
--         (NFATrace N (N .init) q
--           & (acc? N q ⊕ rej? N q))
--     h' = h ⊕ ⊤-grammar

--     run' : ParseTransformer (KL* ⊕Σ₀) h'
--     run' =
--       fold*l
--         ⊕Σ₀
--         h'
--         mt-case
--         cons-case
--       where
--       mt-case : ParseTransformer ε-grammar h'
--       mt-case {w} p =
--         inl ((N .init) , ((nil refl p) ,
--           (decRec
--             (λ acc → inl
--               (DecProp-grammar-yes (N .isAcc (N .init)) _ _ acc _ _))
--             (λ ¬acc → inr (DecProp-grammar-yes
--               (negateDecProp (N .isAcc (N .init))) _ _ ¬acc _ _))
--             (N .isAcc (N .init) .snd))))

--       cons-case : ParseTransformer (h' ⊗ ⊕Σ₀) h'
--       cons-case {w} (split , inl (q , nil x x₁ , z) , char) = {!!}
--       cons-case {w} (split , inl (q , cons {t} x y , z) , char) = {!!}
--       cons-case {w} (split , inl (q , ε-cons {t} x y , z) , char) = {!!}
--       cons-case {w} (split , fsuc x , char) = {!!}


--   -- NFA Combinators
-- --   module _ (N : NFA) where
-- --     module _ (N' : NFA) where

-- --       ⊕NFA : NFA
-- --       -- States stratified into init, N states, N' states
-- --       Q ⊕NFA .fst = ⊤ ⊎ (N .Q .fst ⊎ N' .Q .fst)
-- --       Q ⊕NFA .snd =
-- --         isFinSet⊎
-- --           (_ , isFinSetUnit)
-- --           (_ , (isFinSet⊎ (N .Q) (N' .Q)))
-- --       -- initial state
-- --       init ⊕NFA = inl _
-- --       -- Acceptance at subautomata accepting states
-- --       isAcc ⊕NFA x =
-- --         -- LOL this is way too complicated
-- --         -- could've just pattern matched on x
-- --         DecProp⊎
-- --           (DecPropΣ
-- --             (((fiber (inr ∘ inl) x) , inr∘inl-prop-fibs) ,
-- --               decRec
-- --                 (PT.elim
-- --                     (λ _ → isPropDec inr∘inl-prop-fibs)
-- --                     (λ y → yes y))
-- --                 (λ ∄preimage →
-- --                   no λ y → ∄preimage ∣ y ∣₁
-- --                 )
-- --                 (DecPropIso .Iso.inv
-- --                   (_ , isDecProp∃ (N .Q)
-- --                     (λ y → (inr (inl y) ≡ x) ,
-- --                       isDecProp≡ (⊕NFA .Q) (inr (inl y)) x) ) .snd))
-- --             (N .isAcc ∘ fst))
-- --           (DecPropΣ
-- --             ((fiber (inr ∘ inr) x , inr∘inr-prop-fibs) ,
-- --               decRec
-- --                 (PT.elim
-- --                   (λ _ → isPropDec inr∘inr-prop-fibs)
-- --                   λ y → yes y)
-- --                 (λ ∄preimage → no λ y → ∄preimage ∣ y ∣₁)
-- --                 (DecPropIso .Iso.inv
-- --                   ((_ , isDecProp∃ (N' .Q) λ y → (inr (inr  y) ≡ x) ,
-- --                     (isDecProp≡ (⊕NFA .Q) (inr (inr y)) x))) .snd))
-- --             (N' .isAcc ∘ fst))
-- --           mutex
-- --           where
-- --           inr∘inl-prop-fibs =
-- --             isEmbedding→hasPropFibers
-- --               (compEmbedding (_ , isEmbedding-inr)
-- --                              (_ , isEmbedding-inl) .snd) x

-- --           inr∘inr-prop-fibs =
-- --             isEmbedding→hasPropFibers
-- --               (compEmbedding
-- --                 (_ , isEmbedding-inr)
-- --                 (_ , isEmbedding-inr) .snd) x

-- --           mutex =
-- --             (λ (q , _) (q' , _) →
-- --               lower (⊎Path.encode _ _
-- --                 (isEmbedding→Inj isEmbedding-inr _ _
-- --                   (q .snd ∙ (sym (q' .snd))))))
-- --       transition ⊕NFA .fst =
-- --         N .transition .fst ⊎ N' .transition .fst
-- --       transition ⊕NFA .snd =
-- --         isFinSet⊎ (N .transition) (N' .transition)
-- --       -- the labeled transitions have same src, dst, and label as
-- --       -- in original automata
-- --       src ⊕NFA (inl x) = inr (inl (N .src x))
-- --       src ⊕NFA (inr x) = inr (inr (N' .src x))
-- --       dst ⊕NFA (inl x) = inr (inl (N .dst x))
-- --       dst ⊕NFA (inr x) = inr (inr (N' .dst x))
-- --       label ⊕NFA (inl x) = N .label x
-- --       label ⊕NFA (inr x) = N' .label x
-- --       fst (ε-transition ⊕NFA) =
-- --         Fin 2 ⊎
-- --         (N .ε-transition .fst ⊎ N' .ε-transition .fst)
-- --       snd (ε-transition ⊕NFA) =
-- --         isFinSet⊎
-- --           (_ , isFinSetFin)
-- --           (_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition))
-- --       -- ε-transitions to subautomata initial states
-- --       ε-src ⊕NFA (inl fzero) = ⊕NFA .init
-- --       ε-dst ⊕NFA (inl fzero) = inr (inl (N .init))
-- --       ε-src ⊕NFA (inl (inr fzero)) = ⊕NFA .init
-- --       ε-dst ⊕NFA (inl (inr fzero)) = inr (inr (N' .init))
-- --       -- internal ε-transitions from subautomata
-- --       ε-src ⊕NFA (inr (inl x)) = inr (inl (N .ε-src x))
-- --       ε-dst ⊕NFA (inr (inl x)) = inr (inl (N .ε-dst x))
-- --       ε-src ⊕NFA (inr (inr x)) = inr (inr (N' .ε-src x))
-- --       ε-dst ⊕NFA (inr (inr x)) = inr (inr (N' .ε-dst x))

-- --       ⊗NFA : NFA
-- --       Q ⊗NFA .fst = N .Q .fst ⊎ N' .Q .fst
-- --       Q ⊗NFA .snd = isFinSet⊎ (N .Q) (N' .Q)
-- --       init ⊗NFA = inl (N .init)
-- --       isAcc ⊗NFA (inl x) =
-- --         DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
-- --       isAcc ⊗NFA (inr x) = N' .isAcc x
-- --       transition ⊗NFA .fst = N .transition .fst ⊎ N' .transition .fst
-- --       transition ⊗NFA .snd = isFinSet⊎ (N .transition) (N' .transition)
-- --       src ⊗NFA (inl x) = inl (N .src x)
-- --       dst ⊗NFA (inl x) = inl (N .dst x)
-- --       src ⊗NFA (inr x) = inr (N' .src x)
-- --       dst ⊗NFA (inr x) = inr (N' .dst x)
-- --       label ⊗NFA (inl x) = N .label x
-- --       label ⊗NFA (inr x) = N' .label x
-- --       ε-transition ⊗NFA .fst =
-- --         (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
-- --         (N .ε-transition .fst ⊎ N' .ε-transition .fst)
-- --       ε-transition ⊗NFA .snd =
-- --         isFinSet⊎
-- --           (_ , isFinSetΣ (N .Q)
-- --             λ x → _ ,
-- --               isDecProp→isFinSet
-- --                 (N .isAcc x .fst .snd)
-- --                 (N .isAcc x .snd))
-- --           ((_ , isFinSet⊎ (N .ε-transition) (N' .ε-transition)))
-- --       ε-src ⊗NFA (inl x) = inl (x .fst)
-- --       ε-dst ⊗NFA (inl x) = inr (N' .init)
-- --       ε-src ⊗NFA (inr (inl x)) = inl (N .ε-src x)
-- --       ε-dst ⊗NFA (inr (inl x)) = inl (N .ε-dst x)
-- --       ε-src ⊗NFA (inr (inr x)) = inr (N' .ε-src x)
-- --       ε-dst ⊗NFA (inr (inr x)) = inr (N' .ε-dst x)

-- --     KL*NFA : NFA
-- --     Q KL*NFA .fst = N .Q .fst ⊎ ⊤
-- --     Q KL*NFA .snd = isFinSet⊎ (N .Q) (_ , isFinSetUnit)
-- --     init KL*NFA = inl (N .init)
-- --     isAcc KL*NFA (inl x) =
-- --       DecPropIso .Iso.inv (⊥* , (false , invEquiv LiftEquiv))
-- --     isAcc KL*NFA (inr x) =
-- --       DecPropIso .Iso.inv (Unit* , (true , (invEquiv LiftEquiv)))
-- --     transition KL*NFA = N .transition
-- --     src KL*NFA x = inl (N .src x)
-- --     dst KL*NFA x = inl (N .dst x)
-- --     label KL*NFA = N .label
-- --     ε-transition KL*NFA .fst =
-- --       ⊤ ⊎
-- --       ((Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst) ⊎
-- --         (Σ[ q ∈ N .Q .fst ] N .isAcc q .fst .fst))
-- --     ε-transition KL*NFA .snd =
-- --       isFinSet⊎
-- --         (_ , isFinSetUnit)
-- --         (_ , isFinSet⊎
-- --           (_ , isFinSetAccΣ)
-- --           (_ , isFinSetAccΣ))
-- --       where
-- --       isFinSetAccΣ :
-- --         isFinSet
-- --           (Σ-syntax (N .Q .fst) (λ q → N .isAcc q .fst .fst))
-- --       isFinSetAccΣ =
-- --         isFinSetΣ (N .Q)
-- --           (λ x → _ ,
-- --             isDecProp→isFinSet
-- --               (N .isAcc x .fst .snd)
-- --               (N .isAcc x .snd))
-- --     ε-src KL*NFA (inl x) = inl (N .init)
-- --     ε-dst KL*NFA (inl x) = inr _
-- --     ε-src KL*NFA (inr (inl x)) = inl (x .fst)
-- --     ε-dst KL*NFA (inr (inl x)) = inl (N .init)
-- --     ε-src KL*NFA (inr (inr x)) = inl (x .fst)
-- --     ε-dst KL*NFA (inr (inr x)) = inr _

-- --   NFAfromRegularGrammar : RegularGrammar → NFA
-- --   NFAfromRegularGrammar ε-Reg = emptyNFA
-- --   NFAfromRegularGrammar (g ⊗Reg h) =
-- --     ⊗NFA (NFAfromRegularGrammar g) (NFAfromRegularGrammar h)
-- --   NFAfromRegularGrammar (literalReg c) = literalNFA c
-- --   NFAfromRegularGrammar (g ⊕Reg h) =
-- --     ⊕NFA (NFAfromRegularGrammar g) (NFAfromRegularGrammar h)
-- --   NFAfromRegularGrammar (KL*Reg g) = KL*NFA (NFAfromRegularGrammar g)

-- --   open Iso
-- --   module regex-isos
-- --     -- TODO need to prove these in the grammar module
-- --     -- but there are some cubical issues, so we'll
-- --     -- -- take them as given here
-- --     -- (⊗-unit-l-isStronglyEquivalent : (g : Grammar) →
-- --     --   isStronglyEquivalent (ε-grammar ⊗ g) g)
-- --     -- (⊗-unit-r-isStronglyEquivalent : (g : Grammar) →
-- --     --   isStronglyEquivalent (g ⊗ ε-grammar) g)
-- --     where
-- --     elimEmptyNFA :
-- --       ∀ {q}{q'} →
-- --       ParseTransformer (NFATrace emptyNFA q q') ε-grammar
-- --     elimEmptyNFA p =
-- --       elimNFA
-- --         emptyNFA
-- --         (λ _ _ → the-P)
-- --         (id-PT ε-grammar)
-- --         (λ {_}{_}{t} x y → ⊥.rec (lower t))
-- --         (λ x → id-PT the-P)
-- --         p
-- --       where
-- --       the-P = ε-grammar
-- --       the-nil-case = id-PT ε-grammar

-- --     isProp-emptyNFAParse' : ∀ {w} →
-- --       isProp (NFATrace emptyNFA (lift fzero) (lift (fsuc fzero)) w)
-- --     isProp-emptyNFAParse' {w} (nil x x₁) (nil x₂ x₃) =
-- --       cong₂ (λ a b → NFATrace.nil {emptyNFA} a {w} b)
-- --         (isSetLift isSetFin _ _ x x₂) (isSetString _ _ x₁ x₃)
-- --     isProp-emptyNFAParse' {w} (nil x x₁) (ε-cons x₂ y) =
-- --       ⊥.rec (fzero≠fone (cong lower x))
-- --     isProp-emptyNFAParse' {w} (ε-cons x x₁) (nil x₂ x₃) =
-- --       ⊥.rec (fzero≠fone (cong lower x₂))
-- --     isProp-emptyNFAParse' {w} (ε-cons x x₁) (ε-cons x₂ y) =
-- --       cong₂ (λ a b →
-- --         NFATrace.ε-cons {emptyNFA} {lift fzero}{lift (fsuc fzero)} a {w} b)
-- --         (isSetLift isSetFin _ _ x x₂) (a _ _)
-- --       where
-- --       a : isProp (NFATrace emptyNFA (lift (fsuc fzero)) (lift (fsuc fzero)) w)
-- --       a (nil x x₁) (nil x₂ x₃) =
-- --         cong₂ (λ a b → NFATrace.nil {emptyNFA} a {w} b)
-- --           (isSetLift isSetFin _ _ x x₂) (isSetString _ _ x₁ x₃)
-- --       a (nil x x₁) (ε-cons x₂ y) = ⊥.rec (fzero≠fone (cong lower x₂))
-- --       a (ε-cons x x₁) (nil x₂ x₃) = ⊥.rec (fzero≠fone (cong lower x))
-- --       a (ε-cons x x₁) (ε-cons x₂ y) = ⊥.rec (fzero≠fone (cong lower x))

-- --     ε-regex-iso : isStronglyEquivalent ε-grammar (Parses emptyNFA)
-- --     fst (fst (fun (ε-regex-iso w) p)) = _
-- --     snd (fst (fun (ε-regex-iso w) p)) = refl
-- --     snd (fun (ε-regex-iso w) p) = ε-cons refl (nil refl p)
-- --     inv (ε-regex-iso w) p = elimEmptyNFA (p .snd)
-- --     rightInv (ε-regex-iso w) b =
-- --       Σ≡Prop
-- --         (λ x → transport
-- --           (cong (λ a → isProp (NFATrace _ _ a _ )) (sym (x .snd)))
-- --         isProp-emptyNFAParse') (ΣPathP ((sym (b .fst .snd)) ,
-- --           (isSet→SquareP ((λ _ _ → isSetLift isSetFin)) _ _ _ _)))
-- --     leftInv (ε-regex-iso w) a = isSetString w [] _ _

-- --     literal-P : ∀ {c} → (q q' : (literalNFA c) .Q .fst) → Grammar
-- --     literal-P (lift fzero) (lift fzero) = ε-grammar
-- --     literal-P {c} (lift fzero) (lift (fsuc fzero)) = literal c
-- --     literal-P (lift (fsuc fzero)) (lift fzero) = ⊥-grammar
-- --     literal-P (lift (fsuc fzero)) (lift (fsuc fzero)) = ε-grammar

-- --     elimLiteralNFA :
-- --       ∀ {q}{q'}{c} →
-- --       ParseTransformer
-- --         (NFATrace (literalNFA c) q q') (literal-P {c} q q')
-- --     elimLiteralNFA {q}{q'}{c} p =
-- --       elimNFA
-- --         (literalNFA c)
-- --         literal-P
-- --         the-nil-case
-- --         the-cons-case
-- --         the-ε-cons-case
-- --         p
-- --         where
-- --         the-nil-case : ∀ {q} → ParseTransformer ε-grammar (literal-P {c} q q)
-- --         the-nil-case {lift fzero} p = p
-- --         the-nil-case {lift (fsuc fzero)} p = p

-- --         the-cons-case : ∀ {q}{q'} → (lift fzero ≡ q) →
-- --           ParseTransformer
-- --             (literal c ⊗ literal-P (lift (fsuc fzero)) q') (literal-P q q')
-- --         the-cons-case {lift fzero} {lift (fsuc fzero)} p par =
-- --           (par .fst .snd ∙
-- --             cong (λ a → _ ++ a) (par .snd .snd) ∙
-- --             ++-unit-r (par .fst .fst .fst)) ∙
-- --             par .snd .fst
-- --         the-cons-case {lift (fsuc fzero)} {lift (fsuc fzero)} p par =
-- --           ⊥.rec (fzero≠fone (cong lower p))

-- --         the-ε-cons-case : ∀ {q}{q'}{t} → (literalNFA c) .ε-src t ≡ q →
-- --           ParseTransformer
-- --             (literal-P ((literalNFA c) .ε-dst t) q')
-- --             (literal-P q q')
-- --         the-ε-cons-case {t = t} = ⊥.rec (lower t)


-- --     isProp-literalNFAParse' : ∀ {w}{c} →
-- --       isProp (NFATrace (literalNFA c) (lift fzero) (lift (fsuc fzero)) w)
-- --     isProp-literalNFAParse' {w} {c} (nil x x₁) (nil x₂ x₃) =
-- --       ⊥.rec (fzero≠fone (cong lower x))
-- --     isProp-literalNFAParse' {w} {c} (nil x x₁) (cons x₂ x₃) =
-- --       ⊥.rec (fzero≠fone (cong lower x))
-- --     isProp-literalNFAParse' {w} {c} (cons x x₁) (nil x₂ x₃) =
-- --       ⊥.rec (fzero≠fone (cong lower x₂))
-- --     isProp-literalNFAParse' {w} {c} (cons x x₁) (cons x₂ x₃) =
-- --       cong₂ (λ a b → NFATrace.cons {literalNFA c}
-- --         {_}{lift (fsuc fzero)} a {w} b) (isSetLift isSetFin _ _ x x₂) a
-- --       where
-- --       b : ∀ {w'} → isProp (NFATrace (literalNFA c) (lift (fsuc fzero))
-- --         (lift (fsuc fzero)) w')
-- --       b {w'} (nil x x₁) (nil x₂ x₃) =
-- --         cong₂ (λ a b → NFATrace.nil {literalNFA c} a {w'} b)
-- --           (isSetLift isSetFin _ _ x x₂) (isSetString w' [] _ _)
-- --       b (nil x x₁) (cons x₂ x₃) =
-- --         ⊥.rec (fzero≠fone (cong lower x₂))
-- --       b (cons x x₁) (nil x₂ x₃) =
-- --         ⊥.rec (fzero≠fone (cong lower x))
-- --       b (cons x x₁) (cons x₂ x₃) =
-- --         ⊥.rec (fzero≠fone (cong lower x₂))

-- --       a : x₁ ≡ x₃
-- --       a = Σ≡Prop (λ s → isProp× (isSetString _ _) b)
-- --         (Σ≡Prop (λ _ → isSetString _ _)
-- --           (ΣPathP (fsts-agree , snds-agree)))
-- --         where
-- --         fsts-agree = (x₁ .snd .fst ∙ (sym (x₃ .snd .fst)))
-- --         snds-agree =
-- --           cons-inj₂ (
-- --           cong (λ a → a ++ x₁ .fst .fst .snd) (sym (x₁ .snd .fst)) ∙
-- --           sym (x₁ .fst .snd) ∙ (x₃ .fst .snd) ∙
-- --           cong (λ a → a ++ x₃ .fst .fst .snd) (x₃ .snd .fst))

-- --     literal-regex-iso : ∀ {c} →
-- --       isStronglyEquivalent (literal c) (Parses (literalNFA c))
-- --     fst (fst (fun (literal-regex-iso {c} w) p)) = lift (inr (inl tt))
-- --     snd (fst (fun (literal-regex-iso {c} w) p)) = refl
-- --     snd (fun (literal-regex-iso {c} w) p) =
-- --       cons refl ((([ c ] , []) , p) , (refl , (nil refl refl)))
-- --     inv (literal-regex-iso {c} w) p =
-- --        elimLiteralNFA {q = lift fzero} {q' = lift (fsuc fzero)} {c = c}
-- --          (transport (cong (λ a → NFATrace _ _ a _) (p .fst .snd)) (p .snd))
-- --     rightInv (literal-regex-iso {c} w) b =
-- --       Σ≡Prop (λ x → transport (cong (λ a → isProp (NFATrace _ _ a _))
-- --         (sym (x .snd))) isProp-literalNFAParse')
-- --           (Σ≡Prop (λ x → isSetLift isSetFin _ _) (sym (b .fst .snd)))
-- --     leftInv (literal-regex-iso {c} w) a = isSetString w [ c ] _ _

-- --     module _
-- --       (g h : RegularGrammar)
-- --       (isog : isStronglyEquivalent
-- --         (RegularGrammar→Grammar g)
-- --         (Parses (NFAfromRegularGrammar g)))
-- --       (isoh : isStronglyEquivalent
-- --         (RegularGrammar→Grammar h)
-- --         (Parses (NFAfromRegularGrammar h)))
-- --         where

-- --       g' = (RegularGrammar→Grammar g)
-- --       h' = (RegularGrammar→Grammar h)
-- --       NFAg = (NFAfromRegularGrammar g)
-- --       NFAh = (NFAfromRegularGrammar h)
-- --       Ng = NFATrace (NFAfromRegularGrammar g)
-- --       Parses-g = Parses (NFAfromRegularGrammar g)
-- --       Nh = NFATrace (NFAfromRegularGrammar h)
-- --       Parses-h = Parses (NFAfromRegularGrammar h)

-- --       g⊗h' = (RegularGrammar→Grammar (g GrammarDefs.⊗Reg h))
-- --       NFAg⊗h = (NFAfromRegularGrammar (g GrammarDefs.⊗Reg h))
-- --       N⊗ = NFATrace (NFAfromRegularGrammar (g GrammarDefs.⊗Reg h))
-- --       Parses-⊗ = Parses (NFAfromRegularGrammar (g GrammarDefs.⊗Reg h))

-- --       -- Remember that this is sensitive to the encoding of the ⊗NFA
-- --       Nh→N⊗ : ∀ {q}{q'} →
-- --         ParseTransformer (Nh q q') (N⊗ (inr q) (inr q'))
-- --       Nh→N⊗ (nil x x₁) = nil (cong inr x) x₁
-- --       Nh→N⊗ (cons {t} x x₁) =
-- --         cons {t = inr t} (cong inr x) ((x₁ .fst) , ((x₁ .snd .fst) ,
-- --           (Nh→N⊗ (x₁ .snd .snd))))
-- --       Nh→N⊗ (ε-cons {t} x x₁) =
-- --         ε-cons {t = inr (inr t)} (cong inr x) (Nh→N⊗ x₁)

-- --       -- parses from the h segment to the end
-- --       N⊗h = LinΣ[ q ∈ Accepting NFAh ] Nh (NFAh .init) (q .fst)

-- --       Ng→N⊗ : ∀ {q}{q'} →
-- --         ParseTransformer (Ng q q') (N⊗ (inl q) (inl q'))
-- --       Ng→N⊗ (nil x x₁) = nil (cong inl x) x₁
-- --       Ng→N⊗ (cons {t} x x₁) =
-- --         cons {t = inl t} (cong inl x) ((x₁ .fst) , ((x₁ .snd .fst) ,
-- --           (Ng→N⊗ (x₁ .snd .snd))))
-- --       Ng→N⊗ (ε-cons {t} x x₁) =
-- --         ε-cons {t = inr (inl t)} (cong inl x) (Ng→N⊗ x₁)

-- --       Parses-g⊗Parses-h→Parses⊗ :
-- --         ParseTransformer (Parses-g ⊗ Parses-h) Parses-⊗
-- --       fst (Parses-g⊗Parses-h→Parses⊗ (split , pg , ph)) =
-- --         (inr (ph .fst .fst)) , ph .fst .snd
-- --       snd (Parses-g⊗Parses-h→Parses⊗ (split , pg , ph)) =
-- --         transport
-- --         (cong (λ a → NFATrace _ _ _ a) (sym (split .snd)))
-- --         (
-- --         concatTrace
-- --           NFAg⊗h
-- --           (split .fst .fst)
-- --           (split .fst .snd)
-- --           (Ng→N⊗ (pg .snd))
-- --           (ε-cons {t = inl (pg .fst)} refl (Nh→N⊗ (ph .snd)))
-- --         )

-- --       g⊗h→Parses⊗ :
-- --         ParseTransformer (g' ⊗ h') Parses-⊗
-- --       g⊗h→Parses⊗ (split , pg , ph) =
-- --         Parses-g⊗Parses-h→Parses⊗ (split ,
-- --           ((isog (split .fst .fst) .fun pg) ,
-- --           (isoh (split .fst .snd) .fun ph)))


-- --       ⊗-P : (q q' : Q NFAg⊗h .fst) → Grammar
-- --       ⊗-P (inl x) (inl y) = Ng x y
-- --       ⊗-P (inl x) (inr y) =
-- --         ε-grammar &
-- --         (NFA.acc? NFAg x & NFA.init? NFAh y)
-- --       ⊗-P (inr x) (inl y) = ⊥-grammar
-- --       ⊗-P (inr x) (inr y) = Nh x y

-- --       N⊗→g⊗h : ∀ {q}{q'} →
-- --         ParseTransformer (N⊗ q q') (g' ⊗ h')
-- --       N⊗→g⊗h {q} {q'} =
-- --         elimNFA
-- --           NFAg⊗h
-- --           (λ v v₁ → _)
-- --           {!!}
-- --           {!!}
-- --           {!!}
-- --           {q}
-- --           {q'}
-- --         where
-- --         the-nil-case : ∀ {q} → ParseTransformer ε-grammar (⊗-P q q)
-- --         the-nil-case {inl q} x = nil refl x
-- --         the-nil-case {inr q} x = nil refl x

-- --         the-cons-case : ∀ {q}{q'}{t} → NFAg⊗h .src t ≡ q →
-- --           ParseTransformer
-- --             (literal (NFAg⊗h .label t) ⊗ ⊗-P (NFAg⊗h .dst t) q')
-- --             (⊗-P q q')
-- --         the-cons-case {inl x} {inl x₁} {inl x₂} srct p =
-- --           cons {t = x₂} (isEmbedding→Inj isEmbedding-inl _ _ srct) p
-- --         the-cons-case {inl x} {inr x₁} {inl x₂} srct (a , b , c , d , e) =
-- --           {!!} , ({!d!} , {!!})
-- --           -- elimDecProp-PT
-- --           --   (((init (NFAfromRegularGrammar h) ≡ x₁) ,
-- --           --     (isFinSet→isSet (NFAh .Q .snd) _ _)) ,
-- --           --     decEqQ (NFAh) (NFAh .init) x₁)
-- --           --   _
-- --           --   (λ _ isInit →
-- --           --     elimDecProp-PT
-- --           --     _
-- --           --     _
-- --           --     (λ _ isAcc → {!!} , ({!!} , {!!}))
-- --           --     {!!}
-- --           --     d)
-- --           --   (λ _ notInit → {!!})
-- --           --   e
-- --         the-cons-case {inl x} {inr x₁} {fsuc x₂} srct p =
-- --           ⊥.rec (lower (Cubical.Data.Sum.⊎Path.Cover≃Path
-- --             _ _ .snd .equiv-proof srct .fst .fst))
-- --         the-cons-case {inr x} {inl x₁} {inl x₂} srct p =
-- --           Cubical.Data.Sum.⊎Path.Cover≃Path
-- --             _ _ .snd .equiv-proof srct .fst .fst
-- --         the-cons-case {inr x} {inr x₁} {inl x₂} srct p =
-- --           ⊥.rec (
-- --           lower (Cubical.Data.Sum.⊎Path.Cover≃Path
-- --             _ _ .snd .equiv-proof srct .fst .fst)
-- --           )
-- --         the-cons-case {inr x} {inr x₁} {inr x₂} srct p =
-- --           cons {t = x₂} (isEmbedding→Inj isEmbedding-inr _ _ srct) p

-- --         the-ε-cons-case : ∀ {q}{q'}{t} → NFAg⊗h .ε-src t ≡ q →
-- --           ParseTransformer
-- --           (⊗-P (NFAg⊗h .ε-dst t) q')
-- --           (⊗-P q q')
-- --         the-ε-cons-case = {!!}
-- --         -- the-ε-cons-case {inl x} {inl x₁} {fsuc (inl x₂)} srct p =
-- --         --   ε-cons {t = x₂} (isEmbedding→Inj isEmbedding-inl _ _ srct) p
-- --         -- the-ε-cons-case {inl x} {fsuc x₁} {inl x₂} srct p = {!!}
-- --         -- the-ε-cons-case {inl x} {fsuc x₁} {fsuc (fsuc x₂)} srct p =
-- --         --   ⊥.rec (
-- --         --   lower (Cubical.Data.Sum.⊎Path.Cover≃Path
-- --         --     _ _ .snd .equiv-proof srct .fst .fst)
-- --         --   )
-- --         -- the-ε-cons-case {fsuc x} {inl x₁} {fsuc (inl x₂)} srct p =
-- --         --   Cubical.Data.Sum.⊎Path.Cover≃Path
-- --         --     _ _ .snd .equiv-proof srct .fst .fst
-- --         -- the-ε-cons-case {fsuc x} {fsuc x₁} {inl x₂} srct p = {!p!}
-- --         -- the-ε-cons-case {fsuc x} {fsuc x₁} {fsuc (inl x₂)} srct p = {!!}
-- --         -- the-ε-cons-case {fsuc x} {fsuc x₁} {fsuc (fsuc x₂)} srct p =
-- --         --   ε-cons {t = x₂} (isEmbedding→Inj isEmbedding-inr _ _ srct) p

-- --       ⊗NFA-regex-iso :
-- --         isStronglyEquivalent
-- --           (RegularGrammar→Grammar (g GrammarDefs.⊗Reg h))
-- --           (Parses (NFAfromRegularGrammar (g GrammarDefs.⊗Reg h)))
-- --       fun (⊗NFA-regex-iso w) = {!!}
-- --       inv (⊗NFA-regex-iso w) = {!!}
-- --       rightInv (⊗NFA-regex-iso w) = {!!}
-- --       leftInv (⊗NFA-regex-iso w) = {!!}

-- --     ⊕NFA-regex-iso :
-- --       (g h : RegularGrammar) →
-- --       (isStronglyEquivalent
-- --         (RegularGrammar→Grammar g)
-- --         (Parses (NFAfromRegularGrammar g))) →
-- --       (isStronglyEquivalent
-- --         (RegularGrammar→Grammar h)
-- --         (Parses (NFAfromRegularGrammar h))) →
-- --       isStronglyEquivalent
-- --         (RegularGrammar→Grammar (g GrammarDefs.⊕Reg h))
-- --         (Parses (NFAfromRegularGrammar (g GrammarDefs.⊕Reg h)))
-- --     fun (⊕NFA-regex-iso g h isog isoh w) = {!!}
-- --     inv (⊕NFA-regex-iso g h isog isoh w) = {!!}
-- --     rightInv (⊕NFA-regex-iso g h isog isoh w) = {!!}
-- --     leftInv (⊕NFA-regex-iso g h isog isoh w) = {!!}

-- --     isStronglyEquivalent-NFA-Regex : (g : RegularGrammar) →
-- --       isStronglyEquivalent
-- --         (RegularGrammar→Grammar g)
-- --         (Parses (NFAfromRegularGrammar g))
-- --     isStronglyEquivalent-NFA-Regex GrammarDefs.ε-Reg = ε-regex-iso
-- --     isStronglyEquivalent-NFA-Regex (GrammarDefs.literalReg x) =
-- --       literal-regex-iso
-- --     isStronglyEquivalent-NFA-Regex (g GrammarDefs.⊗Reg h) =
-- --       ⊗NFA-regex-iso g h
-- --         (isStronglyEquivalent-NFA-Regex g)
-- --         (isStronglyEquivalent-NFA-Regex h)
-- --     isStronglyEquivalent-NFA-Regex (g GrammarDefs.⊕Reg h) =
-- --       ⊕NFA-regex-iso g h
-- --         (isStronglyEquivalent-NFA-Regex g)
-- --         (isStronglyEquivalent-NFA-Regex h)
-- --     isStronglyEquivalent-NFA-Regex (GrammarDefs.KL*Reg g) w = {!!}


-- -- -- open NFADefs
-- -- -- open NFA
-- -- -- open DFADefs
-- -- -- open DFA
-- -- -- module _ {ℓ} ((Σ₀ , isFinSetΣ₀) : FinSet ℓ)
-- -- --   (N : NFA ℓ (Σ₀ , isFinSetΣ₀))
-- -- --   where

-- -- --   open GrammarDefs ℓ (Σ₀ , isFinSetΣ₀)
-- -- --   open StringDefs ℓ (Σ₀ , isFinSetΣ₀)

-- -- --   powersetNFA : NFA ℓ (Σ₀ , isFinSetΣ₀)
-- -- --   fst (Q powersetNFA) = (N .Q .fst) → Bool
-- -- --   snd (Q powersetNFA) = isFinSet→ (N .Q) (Bool , isFinSetBool)
-- -- --   init powersetNFA q =
-- -- --     if Dec→Bool (NFA.decEqQ N q (N .init)) then
-- -- --       true else
-- -- --       false
-- -- --   fst (fst (isAcc powersetNFA f)) = ∃[ q ∈ N .Q .fst ] f q ≡ true
-- -- --   snd (fst (isAcc powersetNFA f)) = isPropPropTrunc
-- -- --   snd (isAcc powersetNFA f) =
-- -- --     isFinSet→Dec∥∥ (isFinSetΣ (N .Q) λ z → (f z ≡ true) ,
-- -- --       isDecProp→isFinSet (isSetBool (f z) true)
-- -- --         (isFinSet→Discrete isFinSetBool (f z) true))
-- -- --   fst (transition powersetNFA) =
-- -- --     Σ[ f ∈ (N .Q .fst → Bool) ] Σ[ g ∈ (N .Q .fst → Bool) ]
-- -- --       Σ[ c ∈ Σ₀ ]
-- -- --       ∃[ t ∈ N .transition .fst ]
-- -- --         ( f (N .src t) ≡ true ) × ( g (N .dst t) ≡ true ) × (N .label t ≡ c)
-- -- --   snd (transition powersetNFA) =
-- -- --     isFinSetΣ (powersetNFA .Q)
-- -- --       λ x → _ , isFinSetΣ (powersetNFA .Q) λ x → _ ,
-- -- --         isFinSetΣ (Σ₀ , isFinSetΣ₀) λ c → _ , isFinSet∥∥ (_ ,
-- -- --           isFinSetΣ (N .transition) (λ t → _ , isFinSetΣ (_ ,
-- -- --             isDecProp→isFinSet (isSetBool _ _) (DiscreteBool _ _)) λ _ → _ ,
-- -- --               isFinSetΣ (_ , isDecProp→isFinSet (isSetBool _ _) (DiscreteBool _ _)) λ _ → _ ,
-- -- --                 isDecProp→isFinSet (isSetΣ₀ _ _) (DiscreteΣ₀ _ _)))
-- -- --       where
-- -- --       DiscreteBool : Discrete Bool
-- -- --       DiscreteBool = isFinSet→Discrete isFinSetBool
-- -- --   src powersetNFA t = t .fst
-- -- --   dst powersetNFA t = t .snd .fst
-- -- --   label powersetNFA t = t .snd .snd .fst
-- -- --   fst (ε-transition powersetNFA) = ⊥*
-- -- --   snd (ε-transition powersetNFA) = isFinSetLift isFinSetFin
-- -- --   ε-src powersetNFA x = ⊥.rec (lower x)
-- -- --   ε-dst powersetNFA x = ⊥.rec (lower x)

-- -- --   isDeterministic-powersetNFA : isDeterministic _ _ (powersetNFA)
-- -- --   fst isDeterministic-powersetNFA = uninhabEquiv (λ x → lower x) (λ x → x)
-- -- --   fst (fst (snd isDeterministic-powersetNFA c)) x = x .fst .snd .snd .fst
-- -- --   fst (fst (fst (equiv-proof (snd (fst (snd isDeterministic-powersetNFA f))) c))) =
-- -- --     f , ({!!} , (c , ∣ {!!} , ({!!} , ({!!} , {!!})) ∣₁))
-- -- --     where
-- -- --     the-g : N .Q .fst → Bool
-- -- --     the-g q = {!!}
-- -- --   snd (fst (fst (equiv-proof (snd (fst (snd isDeterministic-powersetNFA f))) c))) = {!!}
-- -- --   snd (fst (equiv-proof (snd (fst (snd isDeterministic-powersetNFA f))) c)) = {!!}
-- -- --   snd (equiv-proof (snd (fst (snd isDeterministic-powersetNFA f))) c) = {!!}
-- -- --   fst (snd (snd isDeterministic-powersetNFA f) c) = {!!}
-- -- --   snd (snd (snd isDeterministic-powersetNFA f) c) = {!!}


-- -- --   powersetDFA : DFA ℓ (Σ₀ , isFinSetΣ₀)
-- -- --   Q powersetDFA = {!!}
-- -- --   init powersetDFA = {!!}
-- -- --   isAcc powersetDFA = {!!}
-- -- --   δ powersetDFA = {!!}
