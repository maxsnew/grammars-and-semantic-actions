open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

module NFA.Determinization (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Equiv
import Cubical.Foundations.Isomorphism as Isom

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.Empty as Empty hiding (rec)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum hiding (rec ; map)
import Cubical.Data.Equality as Eq


open import Cubical.HITs.PropositionalTruncation as PT hiding (rec)
import Cubical.HITs.PropositionalTruncation.Monad as PTMonad

open import Grammar Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.Inductive.Indexed Alphabet as Idx
open import Term Alphabet
open import NFA.Base Alphabet
open import DFA Alphabet
open import Helper
open import Graph.Reachability

private
  variable
    ℓN ℓ : Level

open NFA
open StrongEquivalence

module _ (N : NFA) (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩ ) where
  private
    module N = NFA N

  open directedGraph
  -- The NFA without labelled transitions,
  -- viewed as a directed graph
  ε-graph : directedGraph
  ε-graph .states = N.Q
  ε-graph .directed-edges = N.ε-transition
  ε-graph .src = N.ε-src
  ε-graph .dst = N.ε-dst
  private module ε-graph = directedGraph ε-graph

  is-ε-closed : ⟨ FinSetDecℙ N.Q ⟩ → Type ℓ-zero
  is-ε-closed X =
    (t : ⟨ N.ε-transition ⟩) (x : ⟨ N.Q ⟩)
    (src∈X : X (N.ε-src t) .fst .fst) →
    X (N.ε-dst t) .fst .fst

  isProp-is-ε-closed : ∀ X → isProp (is-ε-closed X)
  isProp-is-ε-closed X a b =
    funExt λ t → funExt λ x → funExt (λ src∈X →
      X (N.ε-dst t) .fst .snd (a t x src∈X) (b t x src∈X))

  Dec-is-ε-closed : ∀ X → Dec (is-ε-closed X)
  Dec-is-ε-closed X =
    decRec
      (λ ∣t,src∈X,¬dst∈X∣ →
        PT.rec
          (isPropDec (isProp-is-ε-closed X))
          (λ (t , src∈X , ¬dst∈X) →
            no (λ closed → ¬dst∈X (closed t (N.ε-src t) src∈X)))
          ∣t,src∈X,¬dst∈X∣)
      (λ ¬|t,src∈X,¬dst∈X| →
            yes (λ t x src∈X →
              decRec
                (λ dst∈X → dst∈X)
                (λ ¬dst∈X →
                  Empty.rec
                    (¬|t,src∈X,¬dst∈X| ∣ t , src∈X , ¬dst∈X ∣₁))
                (X (N.ε-dst t) .snd)))
      (DecProp∃
        N.ε-transition
        (λ t →
          DecProp×
            (X (N.ε-src t))
            (negateDecProp (X (N.ε-dst t))))
        .snd)

  isFinSet-is-ε-closed : ∀ X → isFinSet (is-ε-closed X)
  isFinSet-is-ε-closed X =
    isDecProp→isFinSet
      (isProp-is-ε-closed X)
      (Dec-is-ε-closed X)

  ε-closed : Type (ℓ-suc ℓ-zero)
  ε-closed = Σ ⟨ FinSetDecℙ N.Q ⟩ is-ε-closed

  isFinSet-ε-closed : isFinSet ε-closed
  isFinSet-ε-closed =
    isFinSetΣ (FinSetDecℙ N.Q) λ X → _ , (isFinSet-is-ε-closed X)

  _∈-ε-closed_ : ⟨ N.Q ⟩ → ε-closed → Type ℓ-zero
  q ∈-ε-closed qs = qs .fst q .fst .fst

  opaque
    -- The decidable finite set of states reachable from q-start
    ε-reach : ⟨ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    ε-reach q-start q-end .fst = _ , isPropPropTrunc
    ε-reach q-start q-end .snd = {!!}
    -- DecReachable ε-graph q-start q-end

    ε-reach-is-ε-closed : ∀ q-start → is-ε-closed (ε-reach q-start)
    ε-reach-is-ε-closed q-start t x x-is-reachable = {!!}
    -- do
    --   (n , gw , q-start≡start-gw , x≡end-gw) ← x-is-reachable
    --   return
    --     (suc n ,
    --     ε-graph.snoc t gw x≡end-gw ,
    --     q-start≡start-gw ∙ ε-graph.snoc-pres-start t gw x≡end-gw ,
    --     ε-graph.snoc-end t gw x≡end-gw)
    --   where open PTMonad

    ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → ε-closed
    ε-closure X .fst = FinSetDecℙ∃ N.Q N.Q X ε-reach
    ε-closure X .snd t x x∈X = do
      (a , a∈X , reach) ← x∈X
      return (a , a∈X , ε-reach-is-ε-closed a t x reach)
      where open PTMonad

    ε-closure-lift-∈ :
      {A : Decℙ ⟨ N.Q ⟩} {a : ⟨ N.Q ⟩} →
      _∈-FinSetDecℙ_ {A = N.Q} a A → a ∈-ε-closed (ε-closure A)
    ε-closure-lift-∈ a∈A = {!!}
    -- ∣ _ , a∈A , (Reachable-is-reflexive ε-graph _) ∣₁

    ε-closure-transition :
      (t : ⟨ N.ε-transition ⟩) →
      (X : ε-closed) →
      N.ε-src t ∈-ε-closed X →
      N.ε-dst t ∈-ε-closed X
    ε-closure-transition t X src∈X = X .snd t (N.ε-src t) src∈X

    -- open GraphWalk
    -- -- TODO need to induct on a walk
    -- ε-closure-walk :
    --   ∀ n →
    --   (q-[ε*]→q' : GraphWalk ε-graph n) →
    --   (X : ε-closed) →
    --   (start∈X : GraphWalk.start q-[ε*]→q' ∈-ε-closed X) →
    --   GraphWalk.end q-[ε*]→q' ∈-ε-closed X
    -- ε-closure-walk zero walk X start∈X = start∈X
    -- ε-closure-walk (suc n) walk X start∈X = {!!}

    -- TODO define in terms of the above
    -- ε-closure-GraphPath :
    --   (q-[ε*]→q' : GraphPath ε-graph) →
    --   (X : ε-closed) →
    --   (GraphWalk.start
    --     (GraphPath→GraphWalk ε-graph q-[ε*]→q' .snd .fst) ∈-ε-closed X) →
    --   (GraphWalk.end
    --     (GraphPath→GraphWalk ε-graph q-[ε*]→q' .snd .fst) ∈-ε-closed X)
    -- ε-closure-GraphPath walk X start∈X =
    --   ε-closure-walk (walk .fst) (walk .snd .snd .fst) X start∈X

  witness-ε :
    (q : ⟨ N.Q ⟩) → (X : ⟨ FinSetDecℙ N.Q ⟩ ) →
    q ∈-ε-closed (ε-closure X) →
    (X q .fst .fst) ⊎
    (Σ[ q' ∈ ⟨ N.Q ⟩ ]
     Σ[ q'∈X ∈ X q' .fst .fst ]
     GraphWalk' ε-graph q q')
     -- Σ[ q-[ε*]→q' ∈ GraphWalk' ε-graph ]
     --   ((GraphWalk.start
     --       (GraphPath→GraphWalk ε-graph q-[ε*]→q' .snd .fst) Eq.≡ q) ×
     --    (GraphWalk.end
     --       (GraphPath→GraphWalk ε-graph q-[ε*]→q' .snd .fst) Eq.≡ q')))
  witness-ε = λ q X x → {!!}

  opaque
    unfolding ε-closure
    lit-reach : ⟨ Alphabet ⟩ → ⟨ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    lit-reach c q-start =
      N.hasTransition (isFinSet→Discrete isFinSetAlphabet) q-start c

    lit-closure : ⟨ Alphabet ⟩ → ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    lit-closure c X = FinSetDecℙ∃ N.Q N.Q X (lit-reach c)

    lit-closure-transition :
      (t : ⟨ N.transition ⟩) →
      (X : ε-closed) →
      N.src t ∈-ε-closed X →
      N.dst t ∈-ε-closed ε-closure (lit-closure (N.label t) (X .fst))
    lit-closure-transition t X src∈X = {!!}
      -- ∣ (N.dst t) ,
      --   (∣ (N.src t) , (src∈X , ∣ t , (refl , refl , refl) ∣₁) ∣₁ ,
      --     ∣ 0 , ((trivialWalk ε-graph (N.dst t)) , (refl , refl)) ∣₁) ∣₁

    witness-lit :
      (c : ⟨ Alphabet ⟩) → (q : ⟨ N.Q ⟩) → (X : ⟨ FinSetDecℙ N.Q ⟩ ) →
      (lit-closure c X) q .fst .fst →
      (Σ[ t ∈ ⟨ N.transition ⟩ ]
       Σ[ q' ∈ ⟨ N.Q ⟩  ]
       Σ[ q'∈X ∈ X q' .fst .fst  ]
         (N.label t Eq.≡ c) ×
         (N.src t Eq.≡ q') ×
         (N.dst t Eq.≡ q))
    witness-lit c q X = {!!}

  -- TODO this should go elsewhere
  witness-true :
    (A : DecProp' ℓ) → A .fst →
    true Eq.≡ Bool-iso-DecProp' .Isom.Iso.inv A
  witness-true {ℓ} (ty , true , _) a = Eq.refl
  witness-true {ℓ} (ty , false , snd₁) a = Empty.rec (snd₁ .fst a)

  truth→witness :
    (b : Bool) → true Eq.≡ b →
    Isom.Iso.fun Bool-iso-DecProp' b .fst
  truth→witness true true≡b = lift tt

  ℙNAcc-DecProp' : (X : ε-closed) → DecProp' ℓ-zero
  ℙNAcc-DecProp' X =
    DecProp'∃ N.Q
      (λ q → DecProp'×
              (DecℙIso ⟨ N.Q ⟩ .Isom.Iso.fun (X .fst) q)
              (Bool-iso-DecProp' .Isom.Iso.fun (N .isAcc q)))
    -- DecProp∃
    --     N.Q
    --     (λ q → DecProp× (X .fst q) (Bool≃DecProp .fst (N.isAcc q)))

  open DFA
  ℙN : DFA {ℓD = ℓ-suc ℓ-zero}
  ℙN .Q = ε-closed , isFinSet-ε-closed
  ℙN .init = ε-closure (SingletonDecℙ {A = N.Q} N.init)
  ℙN .isAcc X = Bool-iso-DecProp' .Isom.Iso.inv (ℙNAcc-DecProp' X)
  -- Bool≃DecProp .snd .equiv-proof (ℙNAcc-DecProp' X) .fst fst
  ℙN .δ X c = ε-closure (lit-closure c (X .fst))

  private
    module ℙN = DFA ℙN

  chooseAcc : (X : ε-closed) →
    (Σ[ q ∈ ⟨ N.Q ⟩ ] Σ[ q∈X ∈ q ∈-ε-closed X ] ℙN.isAcc X Eq.≡ N.isAcc q)
  chooseAcc = {!!}

  embedAcc : (q : ⟨ N.Q ⟩) → (X : ε-closed) → (q ∈-ε-closed X) → true Eq.≡ N.isAcc q →
    true Eq.≡ ℙN.isAcc X
  embedAcc q X q∈X acc =
    witness-true
      (ℙNAcc-DecProp' X)
      ∣ q , (q∈X , truth→witness (N.isAcc q) acc) ∣₁

  NFA→DFA-alg :
    Algebra (N.TraceTy true)
      (λ q →
        &[ X ∈ ε-closed ]
        &[ q∈X ∈ q ∈-ε-closed X ] ℙN.Trace true X
      )
  NFA→DFA-alg q =
    ⊕ᴰ-elim (λ {
        stop → ⊕ᴰ-elim (λ {
          (lift acc) → &ᴰ-in λ X →
            &ᴰ-in (λ q∈X →
              roll ∘g
              ⊕ᴰ-in ℙN.stop ∘g
              ⊕ᴰ-in (lift (embedAcc q X q∈X acc)) ∘g
              -- Lifts are needed here but won't fill
              {!!}
            ) })
      ; step → ⊕ᴰ-elim (λ { (t , Eq.refl) →
        &ᴰ-in (λ X → &ᴰ-in λ src∈X →
          roll ∘g
          ⊕ᴰ-in ℙN.step ∘g
          ⊕ᴰ-in (lift (N.label t)) ∘g
          liftG ,⊗ id ∘g
          liftG ,⊗ liftG ∘g
          id ,⊗ &ᴰ-π (lit-closure-transition t X src∈X) ∘g
          id ,⊗ &ᴰ-π (ε-closure (lit-closure (N.label t) (X .fst))) ∘g
          lowerG ,⊗ id ∘g
          lowerG ,⊗ lowerG
          )
          })
      ; stepε →
        ⊕ᴰ-elim λ { (t , Eq.refl) →
          &ᴰ-in (λ X → &ᴰ-in (λ src∈X →
            &ᴰ-π (ε-closure-transition t X src∈X) ∘g
            &ᴰ-π X)) ∘g
          lowerG } })

  NFA→DFA : ∀ q →
    N.Trace true q ⊢
      &[ X ∈ ε-closed ]
      &[ q∈X ∈ q ∈-ε-closed X ] ℙN.Trace true X
  NFA→DFA q = rec (N.TraceTy true) NFA→DFA-alg q

  DFA→NFA-alg :
    Algebra (ℙN.TraceTy true)
      (λ X → ⊕[ q ∈ ⟨ N.Q ⟩ ] ⊕[ q∈X ∈ q ∈-ε-closed X ] N.Trace true q)
  DFA→NFA-alg X =
    ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim (λ { (lift accX) →
        let
          (q , q∈X , acc) = chooseAcc X
        in
        ⊕ᴰ-in q ∘g
        ⊕ᴰ-in q∈X ∘g
        roll ∘g
        ⊕ᴰ-in N.stop ∘g
        ⊕ᴰ-in (lift (accX Eq.∙ acc)) ∘g
        {!!}
      })
    ; step → ⊕ᴰ-elim (λ { (lift c) →
      ⊕ᴰ-elim (λ q →
        ⊕ᴰ-elim (λ q∈εcloselitcloseX →
          Sum.rec
            (λ q∈litcloseX →
              let
                -- need to pattern match on these equalities, so
                -- we will use a helper function below that does that
                (t , q' , q'∈X , label≡c , src≡q' , dst≡q) =
                  witness-lit c q (X .fst) q∈litcloseX
                in
              ⊕ᴰ-in q' ∘g
              ⊕ᴰ-in q'∈X ∘g
              (witness-lit-help c q
                (X .fst) q∈litcloseX t q' q'∈X label≡c src≡q' dst≡q)
            )
            (λ { (q' , q'∈litcloseX , walk) →
              let
               (t , q'' , q''∈X , label≡c , src≡q'' , dst≡q') =
                  witness-lit c q' (X .fst) q'∈litcloseX
                in
              ⊕ᴰ-in q'' ∘g
              ⊕ᴰ-in q''∈X ∘g
              witness-lit-help c q' (X .fst) q'∈litcloseX t q'' q''∈X
                label≡c src≡q'' dst≡q' ∘g
              id ,⊗ fold-walk c q X q' q∈εcloselitcloseX walk
              })
            (witness-ε q (lit-closure c (X .fst)) q∈εcloselitcloseX)
          ) ∘g
        ⊕ᴰ-distR .fun
      ) ∘g
      ⊕ᴰ-distR .fun ∘g
      lowerG ,⊗ id ∘g
      lowerG ,⊗ lowerG
    }) })
    where
    witness-lit-help : ∀
      (c : ⟨ Alphabet ⟩) → (q : ⟨ N.Q ⟩) → (X : ⟨ FinSetDecℙ N.Q ⟩ ) →
      (lit-closure c X) q .fst .fst →
      (t : ⟨ N.transition ⟩ ) →
      (q' : ⟨ N.Q ⟩) →
      (q'∈X : X q' .fst .fst) →
      (N.label t Eq.≡ c) →
      (N.src t Eq.≡ q') →
      (N.dst t Eq.≡ q) →
      (literal c) ⊗ N.Trace true q ⊢ N.Trace true q'
    witness-lit-help c q X q∈litcloseX t q' q'∈X Eq.refl Eq.refl Eq.refl =
      roll ∘g
      ⊕ᴰ-in N.step ∘g
      ⊕ᴰ-in (t , Eq.refl) ∘g
      liftG ,⊗ liftG ∘g
      liftG ,⊗ id

    -- TODO need to induct on a walk
    fold-walk : ∀ (c : ⟨ Alphabet ⟩) →
      (q : ⟨ N.Q ⟩) → (X : ε-closed) →
      (q' : ⟨ N.Q ⟩) →
      (q∈εlitX : q ∈-ε-closed ε-closure (lit-closure c (X .fst))) →
      (q'-[ε*]→q : GraphWalk' ε-graph q q') →
      N.Trace true q ⊢ N.Trace true q'
    fold-walk c q X q' q∈εlitX nil = id
    fold-walk c q X q' q∈εlitX (cons e walk) =
      roll ∘g
      ⊕ᴰ-in N.stepε ∘g
      ⊕ᴰ-in (e , Eq.refl) ∘g
      liftG ∘g
      fold-walk c q X (N.ε-dst e) q∈εlitX walk
