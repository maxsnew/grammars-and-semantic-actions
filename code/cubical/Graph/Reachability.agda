{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Graph.Reachability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Function.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Functions.Embedding

open import Cubical.Data.Empty as ⊥ hiding (elim ; rec)
open import Cubical.Data.FinData
open import Cubical.Data.FinData.More using (DecΣ ; Fin≡SumFin ; Fin≃Finℕ)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

private
  variable
    ℓ ℓ' : Level
    n : ℕ

isFinSetFin' : isFinSet (Fin n)
isFinSetFin' = isFinSetFin & subst isFinSet (sym Fin≡SumFin)

record directedGraph : Type (ℓ-suc ℓ) where
  field
    states : FinSet ℓ
    directed-edges : FinSet ℓ
    src : ⟨ directed-edges ⟩ → ⟨ states ⟩
    dst : ⟨ directed-edges ⟩ → ⟨ states ⟩

  record GraphWalk (length : ℕ) : Type ℓ where
    field
      vertices : Fin (suc length) → ⟨ states ⟩
      edges : Fin length → ⟨ directed-edges ⟩
      compat-src : (i : Fin length) → src (edges i) ≡ vertices (weakenFin i)
      compat-dst : (i : Fin length) → dst (edges i) ≡ vertices (suc i)

    start : ⟨ states ⟩
    start = vertices zero

    end : ⟨ states ⟩
    end = vertices (fromℕ length)

  unquoteDecl GraphWalkIsoΣ = declareRecordIsoΣ GraphWalkIsoΣ (quote GraphWalk)

  open GraphWalk

  trivialWalk : ⟨ states ⟩ → GraphWalk 0
  vertices (trivialWalk x) _ = x
  edges (trivialWalk x) ()
  compat-src (trivialWalk x) ()
  compat-dst (trivialWalk x) ()

  hasUniqueVertices : GraphWalk n → Type _
  hasUniqueVertices gw = isEmbedding (gw .vertices)

  GraphPath : Type _
  GraphPath =
    Σ[ n ∈ ℕ ] (n < card states) × (Σ[ gw ∈ GraphWalk n ] hasUniqueVertices gw)

  Reachable PathReachable : ⟨ states ⟩ → ⟨ states ⟩ → Type _
  Reachable u v =
    PT.∥ Σ[ n ∈ ℕ ] Σ[ gw ∈ GraphWalk n ] (u ≡ start gw) × (v ≡ end gw) ∥₁
  PathReachable u v =
    PT.∥ Σ[ gp ∈ GraphPath ]
      (u ≡ start (gp .snd .snd .fst)) × (v ≡ end (gp .snd .snd .fst)) ∥₁

  cons :
    (e : ⟨ directed-edges ⟩)
    (gw : GraphWalk n) →
    dst e ≡ start gw →
    GraphWalk (suc n)
  cons e gw p .vertices zero = src e
  cons e gw p .vertices (suc k) = gw .vertices k
  cons e gw p .edges zero = e
  cons e gw p .edges (suc k) = gw .edges k
  cons e gw p .compat-src zero = refl
  cons e gw p .compat-src (suc k) = gw .compat-src k
  cons e gw p .compat-dst zero = p
  cons e gw p .compat-dst (suc k) = gw .compat-dst k

  ext-fin-last : ∀ {ℓ} {A : Type ℓ} {n} →
    A → (Fin n → A) → Fin (suc n) → A
  ext-fin-last {n = zero} last f zero = last
  ext-fin-last {n = suc n} last f zero = f zero
  ext-fin-last {n = suc n} last f (suc k) = ext-fin-last {n = n} last (f ∘ suc) k

  tail : GraphWalk (suc n) → GraphWalk n
  tail gw .vertices = gw .vertices ∘ suc
  tail gw .edges = gw .edges ∘ suc
  tail gw .compat-src = gw .compat-src ∘ suc
  tail gw .compat-dst = gw .compat-dst ∘ suc

  snoc :
    (e : ⟨ directed-edges ⟩)
    (gw : GraphWalk n) →
    src e ≡ end gw →
    GraphWalk (suc n)
  snoc-pres-start :
    (e : ⟨ directed-edges ⟩)
    (gw : GraphWalk n) →
    (p : src e ≡ end gw) →
    start gw ≡ start (snoc e gw p)

  snoc {zero} e gw p .vertices zero = src e
  snoc {zero} e gw p .vertices one = dst e
  snoc {zero} e gw p .edges zero = e
  snoc {zero} e gw p .compat-src zero = refl
  snoc {zero} e gw p .compat-dst zero = refl
  snoc {suc n} e gw p = cons (gw .edges zero) (snoc e (tail gw) p)
    (gw .compat-dst zero ∙ snoc-pres-start e (tail gw) p)

  snoc-pres-start {zero} e gw p = sym p
  snoc-pres-start {suc n} e gw p = sym $ gw .compat-src zero

  snoc-end :
    (e : ⟨ directed-edges ⟩)
    (gw : GraphWalk n) →
    (p : src e ≡ end gw) →
    dst e ≡ end (snoc e gw p)
  snoc-end {zero} e gw p = refl
  snoc-end {suc n} e gw p = snoc-end e (tail gw) p

  drop :
    (gw : GraphWalk n) →
    (k : Fin (suc n)) →
      Σ[ m ∈ ℕ ] Σ[ gw' ∈ GraphWalk m ]
        (gw .vertices k ≡ start gw') × (end gw ≡ end gw')
  drop gw zero = _ , gw , refl , refl
  drop {suc n} gw (suc k) = drop (tail gw) k

  hasUniqueVertices→boundedLength :
    (gw : GraphWalk n) → hasUniqueVertices gw → n < card states
  hasUniqueVertices→boundedLength gw unique =
    card↪Inequality' (_ , isFinSetFin') states (gw .vertices) unique

  tailPresHasUniqueVertices :
    (gw : GraphWalk (suc n)) →
    hasUniqueVertices gw → hasUniqueVertices (tail gw)
  tailPresHasUniqueVertices gw unique =
    isEmbedding-∘ unique (injEmbedding isSetFin injSucFin)

  dropPresHasUniqueVertices :
    (gw : GraphWalk n) →
    hasUniqueVertices gw →
    (k : Fin (suc n)) → hasUniqueVertices (drop gw k .snd .fst)
  dropPresHasUniqueVertices gw unique zero = unique
  dropPresHasUniqueVertices {suc n} gw unique (suc k) =
    dropPresHasUniqueVertices
      (tail gw) (tailPresHasUniqueVertices gw unique) k

  makeUnique :
    (gw : GraphWalk n) →
    Σ[ m ∈ ℕ ] Σ[ gw' ∈ GraphWalk m ]
      hasUniqueVertices gw' × (start gw ≡ start gw') × (end gw ≡ end gw')
  makeUnique {zero} gw =
    zero ,
    gw ,
    injEmbedding (isFinSet→isSet (str states))
      (λ _ → isContr→isProp isContrFin1 _ _) ,
    refl ,
    refl
  makeUnique {suc n} gw =
    let newVert = gw .vertices zero in
    let newEdge = gw .edges zero in
    let n' , gw' , unique , startAgree , endAgree = makeUnique (tail gw) in
    DecΣ _ (λ k → gw' .vertices k ≡ newVert)
      (λ k → isFinSet→Discrete (str states) _ newVert) & decRec
      (λ (k , p) →
        let n'' , gw'' , startAgree' , endAgree' = drop gw' k in
        let unique' = dropPresHasUniqueVertices gw' unique k in
        n'' , gw'' , unique' , sym p ∙ startAgree' , endAgree ∙ endAgree')
      (λ ¬ΣnewVert →
        let gw'' = cons newEdge gw' (gw .compat-dst zero ∙ startAgree) in
        let uniqueGW'' = injEmbedding (isFinSet→isSet (str states))
              λ { {zero} {zero} p → refl
                ; {zero} {suc j} p →
                  ¬ΣnewVert (j , sym p ∙ gw .compat-src zero) & ⊥.rec
                ; {suc i} {zero} p →
                  ¬ΣnewVert (i , p ∙ gw .compat-src zero) & ⊥.rec
                ; {suc i} {suc j} p → congS suc $ isEmbedding→Inj unique i j p
                }
            in
        _ , gw'' , uniqueGW'' , (sym $ gw .compat-src zero) , endAgree)

  GraphWalk→GraphPath :
    (gw : GraphWalk n) →
    Σ[ gp ∈ GraphPath ]
      (start gw ≡ start (gp .snd .snd .fst)) ×
        (end gw ≡ end (gp .snd .snd .fst))
  GraphWalk→GraphPath gw =
    let m , gw' , unique , agree = makeUnique gw in
    let m<bound = hasUniqueVertices→boundedLength gw' unique in
    (m , m<bound , gw' , unique) , agree

  GraphPath→GraphWalk :
    (gp : GraphPath) →
      Σ[ n ∈ ℕ ] Σ[ gw ∈ GraphWalk n ]
        (start (gp .snd .snd .fst) ≡ start gw) ×
          (end (gp .snd .snd .fst) ≡ end gw)
  GraphPath→GraphWalk (n , _ , gw , _) = n , gw , refl , refl

  PathReachable≃Reachable :
    (u v : ⟨ states ⟩) → PathReachable u v ≃ Reachable u v
  PathReachable≃Reachable u v =
    propBiimpl→Equiv isPropPropTrunc isPropPropTrunc
    (PT.map λ (gp , uStart , vEnd) →
      GraphPath→GraphWalk gp & map-snd
        (map-snd λ (s , e) → uStart ∙ s , vEnd ∙ e))
    (PT.map λ (n , gw , uStart , vEnd) →
      GraphWalk→GraphPath gw & map-snd λ (s , e) → uStart ∙ s , vEnd ∙ e)

  isFinSetGraphWalk : (n : ℕ) → isFinSet (GraphWalk n)
  isFinSetGraphWalk n =
    EquivPresIsFinSet (isoToEquiv ∘ invIso $ GraphWalkIsoΣ {n}) $
    isFinSetΣ
      (_ , isFinSet→ (_ , isFinSetFin') states)
      (λ vertices → _ , isFinSetΣ
        (_ , isFinSet→ (_ , isFinSetFin') directed-edges)
        (λ edges → _ , isFinSetΣ
          (_ , isFinSetΠ (_ , isFinSetFin') (λ i → _ , isFinSet≡ states _ _))
          (λ _ → _ , isFinSetΠ (_ , isFinSetFin')
            (λ i → _ , isFinSet≡ states _ _))))

  isFinSetHasUniqueVertices :
    (gw : GraphWalk n) → isFinSet (hasUniqueVertices gw)
  isFinSetHasUniqueVertices gw =
    isFinSetIsEmbedding (_ , isFinSetFin') states (gw .vertices)

  isFinSetGraphPath : isFinSet GraphPath
  isFinSetGraphPath =
    EquivPresIsFinSet (Σ-cong-equiv-fst Fin≃Finℕ ∙ₑ Σ-assoc-≃) $
    isFinSetΣ
      (_ , isFinSetFin')
      (λ n → _ , isFinSetΣ
        (_ , isFinSetGraphWalk _)
        (λ gw → _ , isFinSetHasUniqueVertices gw))

  DecPathReachable : (u v : ⟨ states ⟩) → Dec (PathReachable u v)
  DecPathReachable u v = isFinSet→Dec∥∥ $ isFinSetΣ
    (_ , isFinSetGraphPath)
    (λ gp → _ , isFinSet×
      (_ , isFinSet≡ states _ _)
      (_ , isFinSet≡ states _ _))

  DecReachable : (u v : ⟨ states ⟩) → Dec (Reachable u v)
  DecReachable u v =
    EquivPresDec (PathReachable≃Reachable u v) (DecPathReachable u v)

  Reachable-is-reflexive : (u : ⟨ states ⟩) → Reachable u u
  Reachable-is-reflexive u = ∣ 0 , trivialWalk u , refl , refl ∣₁

