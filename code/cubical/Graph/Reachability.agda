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
open import Cubical.Data.FinData.Order
open import Cubical.Data.FinData.More using (DecΣ ; Fin≡SumFin ; Fin≃Finℕ)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List as List using (List; []; _∷_)
import Cubical.Data.List.FinData as ListFin
import Cubical.Data.Equality as Eq

open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

open import Helper

private
  variable
    ℓ ℓ' : Level
    n : ℕ

isFinSetFin' : isFinSet (Fin n)
isFinSetFin' = isFinSetFin & subst isFinSet (sym Fin≡SumFin)

-- Because it occurs in a subst below, GraphWalk is not strictly positive
-- I don't know if turning off this check is entirely safe, but
-- this induvtive construction of GraphWalk seems needed for the
-- determinization proof
{-# NO_POSITIVITY_CHECK #-}
record directedGraph : Type (ℓ-suc ℓ) where
  field
    states : FinSet ℓ
    directed-edges : FinSet ℓ
    src : ⟨ directed-edges ⟩ → ⟨ states ⟩
    dst : ⟨ directed-edges ⟩ → ⟨ states ⟩

  data GraphWalk (end : ⟨ states ⟩) : ⟨ states ⟩ → ℕ → Type ℓ where
    nil : GraphWalk end end 0
    cons' : ∀ n (e : ⟨ directed-edges ⟩) →
      GraphWalk end (dst e) n → GraphWalk end (src e) (suc n)

  -- TODO should be provable using IW trees
  postulate
    isSetGraphWalk :
      (end start : ⟨ states ⟩) →
      (n : ℕ) →
      isSet (GraphWalk end start n)
    isFinSetGraphWalk :
      (end start : ⟨ states ⟩) →
      (n : ℕ) →
      isFinSet (GraphWalk end start n)

  trivialWalk→sameEndpoints :
    (end start : ⟨ states ⟩) →
    GraphWalk end start 0 →
    end ≡ start
  trivialWalk→sameEndpoints end start nil = refl

  first-edge :
    {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start (suc n)) →
    ⟨ directed-edges ⟩
  first-edge (cons' _ e walk) = e

  tail :
    {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start (suc n)) →
    GraphWalk end (dst (first-edge walk)) n
  tail (cons' _ e walk) = walk

  vertices : {end start : ⟨ states ⟩} →
    GraphWalk end start n → Fin (suc n) → ⟨ states ⟩
  vertices {start = start} walk zero = start
  vertices (cons' n e walk) (suc m) = vertices walk m

  hasUniqueVertices : ∀ {end start : ⟨ states ⟩} → GraphWalk end start n → Type ℓ
  hasUniqueVertices walk = isEmbedding (vertices walk)

  hasUniqueVertices→boundedLength :
    {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start n) →
    hasUniqueVertices walk →
    n < card states
  hasUniqueVertices→boundedLength walk unique =
    card↪Inequality' (_ , isFinSetFin') states (vertices walk) unique

  uniqueVerticesWalk : ∀ (end start : ⟨ states ⟩) → Type ℓ
  uniqueVerticesWalk end start =
    Σ[ n ∈ ℕ ]
    Σ[ walk ∈ GraphWalk end start n ] hasUniqueVertices walk

  tailUniqueVertices :
    {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start (suc n)) →
    hasUniqueVertices walk →
    hasUniqueVertices (tail walk)
  tailUniqueVertices (cons' _ e walk) uniq =
    isEmbedding-∘ uniq (injEmbedding isSetFin injSucFin)

  drop : {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start n) →
    (k : Fin (suc n)) →
    Σ[ m ∈ ℕ ] GraphWalk end (vertices walk k) m
  drop walk zero = _ , walk
  drop (cons' n e walk) (suc k) = drop walk k

  dropPreservesUnique :
    {end start : ⟨ states ⟩} →
    (uniqWalk : uniqueVerticesWalk end start) →
    (k : Fin (suc (uniqWalk .fst))) →
    hasUniqueVertices (drop (uniqWalk .snd .fst) k .snd)
  dropPreservesUnique uniqWalk zero = uniqWalk .snd .snd
  dropPreservesUnique (n , cons' n-1 e walk , uniq) (suc k) =
    dropPreservesUnique
      (n-1 ,
      (walk , tailUniqueVertices (cons' n-1 e walk) uniq)) k

  GraphPath : ∀ (end start : ⟨ states ⟩) → Type _
  GraphPath end start =
    Σ[ n ∈ ℕ ]
      ((n < card states) ×
      (Σ[ walk ∈ GraphWalk end start n ] hasUniqueVertices walk))

  makeUnique :
    {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start n) →
    uniqueVerticesWalk end start
  makeUnique nil =
    0 ,
    nil ,
    injEmbedding
      (isFinSet→isSet (str states))
      (λ _ → isContr→isProp isContrFin1 _ _)
  makeUnique {end = end}(cons' n e walk) =
    let new-vert = src e in
    let new-edge = e in
    let n' , walk' , uniq = makeUnique walk in
    (DecΣ
      (suc n')
      (λ k → vertices walk' k ≡ new-vert)
      (λ k → isFinSet→Discrete (str states) (vertices walk' k) new-vert)) &
    decRec
      -- There is a repeated vertex
      (λ (m , p) →
        let n'' , walk'' = drop walk' m in
        let uniq' = dropPreservesUnique (n' , (walk' , uniq)) m in
        n'' ,
        subst (λ z → Σ[ w ∈ GraphWalk end z n'' ] hasUniqueVertices w) p (walk'' , uniq'))
      -- There is no repeated vertex
      (λ ¬ΣnewVert →
        suc n' ,
        (cons' n' new-edge walk' ,
        injEmbedding
          (isFinSet→isSet (str states))
              λ { {zero} {zero} p → refl
                ; {zero} {suc j} p → ¬ΣnewVert (j , (sym p)) & ⊥.rec
                ; {suc i} {zero} p → ¬ΣnewVert (i , p) & ⊥.rec
                ; {suc i} {suc j} p → congS suc $ isEmbedding→Inj uniq i j p
                }
          )
      )

  GraphWalk→GraphPath :
    {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start n) →
    GraphPath end start
  GraphWalk→GraphPath walk =
    let m , walk' , uniq = makeUnique walk in
    m , (hasUniqueVertices→boundedLength walk' uniq , walk' , uniq)

  Reachable PathReachable : ⟨ states ⟩ → ⟨ states ⟩ → Type _
  Reachable end start =
    PT.∥ Σ[ n ∈ ℕ ] GraphWalk end start n  ∥₁
  PathReachable end start =
    PT.∥ GraphPath end start ∥₁

  PathReachable≃Reachable :
    (end start : ⟨ states ⟩) → PathReachable end start ≃ Reachable end start
  PathReachable≃Reachable end start =
    propBiimpl→Equiv isPropPropTrunc isPropPropTrunc
      (PT.map (λ gp → (gp .fst) , (gp .snd .snd .fst)))
      (PT.map (λ (n , gw) → GraphWalk→GraphPath gw))

  isFinSetHasUniqueVertices :
    {end start : ⟨ states ⟩} →
    (gw : GraphWalk end start n) → isFinSet (hasUniqueVertices gw)
  isFinSetHasUniqueVertices gw =
    isFinSetIsEmbedding (_ , isFinSetFin') states (vertices gw)

  isFinSetGraphPath :
    (end start : ⟨ states ⟩) →
    isFinSet (GraphPath end start)
  isFinSetGraphPath end start =
    EquivPresIsFinSet (Σ-cong-equiv-fst Fin≃Finℕ ∙ₑ Σ-assoc-≃) $
      isFinSetΣ (_ , isFinSetFin')
        (λ n → _ , isFinSetΣ (_ , isFinSetGraphWalk _ _ _)
          (λ walk → _ , isFinSetHasUniqueVertices walk))

  DecPathReachable : (end start : ⟨ states ⟩) → Dec (PathReachable end start)
  DecPathReachable end start = isFinSet→Dec∥∥ (isFinSetGraphPath end start)

  DecReachable : (end start : ⟨ states ⟩) → Dec (Reachable end start)
  DecReachable end start =
    EquivPresDec
      (PathReachable≃Reachable end start)
      (DecPathReachable end start)

  Reachable-is-reflexive : (u : ⟨ states ⟩) → Reachable u u
  Reachable-is-reflexive u = ∣ 0 , nil ∣₁

  -- opaque
  --   unfolding GraphWalkOfLenBetween

  --   isFinSetGraphWalkOfLenBetween : (n : ℕ) (u v : ⟨ states ⟩) → isFinSet (GraphWalkOfLenBetween n u v)
  --   isFinSetGraphWalkOfLenBetween n u v = isFinSetΣ
  --     (_ , isFinSetGraphWalk n)
  --     (λ gw → _ , isFinSet×
  --       (_ , isFinSet≡ states u (start gw))
  --       (_ , isFinSet≡ states v (end gw)))

  -- DecGraphWalkBetween : (u v : ⟨ states ⟩) → Dec (GraphWalkBetween u v)
  -- DecGraphWalkBetween u v =
  --   let queue : List {!!}
  --       queue = [] in
  --   {!!}
