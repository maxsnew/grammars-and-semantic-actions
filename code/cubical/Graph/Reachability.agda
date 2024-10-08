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
open import Cubical.Data.FinData as FD
open import Cubical.Data.FinData.Order
open import Cubical.Data.FinData.More using (DecΣ ; Fin≡SumFin ; Fin≃Finℕ ; Fin≃SumFin)
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

record directedGraph ℓ : Type (ℓ-suc ℓ) where
  field
    states : FinSet ℓ
    directed-edges : FinSet ℓ
    src : ⟨ directed-edges ⟩ → ⟨ states ⟩
    dst : ⟨ directed-edges ⟩ → ⟨ states ⟩

module _ (G : directedGraph ℓ) where
  open directedGraph G
  data GraphWalk (end : ⟨ states ⟩) : ⟨ states ⟩ → ℕ → Type ℓ where
    nil : GraphWalk end end 0
    cons : ∀ n (e : ⟨ directed-edges ⟩) →
      GraphWalk end (dst e) n → GraphWalk end (src e) (suc n)

  GraphWalk' : (end start : ⟨ states ⟩) → Type ℓ
  GraphWalk' end start = Σ[ n ∈ ℕ ] GraphWalk end start n

  trivialWalk→sameEndpoints :
    (end start : ⟨ states ⟩) →
    GraphWalk end start 0 →
    end ≡ start
  trivialWalk→sameEndpoints end start nil = refl

  module _
    (isFinOrd-directed-edges : isFinOrd ⟨ directed-edges ⟩) where
    isFinOrdGraphWalk :
      ∀ (n : ℕ) →
      (end start : ⟨ states ⟩) →
      isFinOrd (GraphWalk end start n)
    isFinOrdGraphWalk zero end start =
      decRec
        (λ end≡start →
           1 ,
           isoToEquiv (
             iso
               (λ _ → inl _)
               (λ { (inl tt) → subst (λ z → GraphWalk end z zero) end≡start nil })
               (λ { (inl tt) → refl})
               λ { nil →
                 cong (λ u → subst (λ z → GraphWalk end z zero) u nil)
                   (isFinSet→isSet (str states) end end end≡start refl) ∙
                 substRefl {B = λ z → GraphWalk end z zero}
                   GraphWalk.nil }))
        (λ ¬q≡q' →
          0 ,
          uninhabEquiv
            (λ walk → ¬q≡q' (trivialWalk→sameEndpoints _ _ walk)) (λ x → x)
            )
        (isFinSet→Discrete (str states) end start)
    isFinOrdGraphWalk (suc n) end start =
      EquivPresIsFinOrd
        {A = Σ[ e ∈ ⟨ directed-edges ⟩ ] Σ[ src≡start ∈ src e Eq.≡ start ] GraphWalk end (dst e) n}
        (isoToEquiv
          (iso
            (λ { (e , Eq.refl , walk) → cons n e walk })
            (λ { (cons .n e walk) → e , Eq.refl , walk })
            (λ { (cons .n e walk) → refl } )
            λ { (e , Eq.refl , walk) → refl
            }
          ))
        (isFinOrdΣ ⟨ directed-edges ⟩ isFinOrd-directed-edges
          (λ e → _)
          (λ e → isFinOrdΣ (src e Eq.≡ start)
            (decRec
              (λ src≡start →
                isContr→isFinOrd ((Eq.pathToEq src≡start) ,
                (λ { Eq.refl →
                 cong (Eq.pathToEq)
                   (isFinSet→isSet (str states) (src e) (src e) src≡start refl) ∙
                Eq.eqToPath Eq.pathToEq-reflPath })))
              (λ ¬src≡start → 0 , uninhabEquiv (λ eq → ¬src≡start (Eq.eqToPath eq)) λ x → x)
              (isFinSet→Discrete (str states) (src e) start))
            _
            λ { Eq.refl → isFinOrdGraphWalk n end (dst e)}))

    isFinSetGraphWalk :
      (end start : ⟨ states ⟩) →
      (n : ℕ) →
      isFinSet (GraphWalk end start n)
    isFinSetGraphWalk end start n = isFinOrd→isFinSet (isFinOrdGraphWalk _ _ _)
    isSetGraphWalk :
      (end start : ⟨ states ⟩) →
      (n : ℕ) →
      isSet (GraphWalk end start n)
    isSetGraphWalk end start n = isFinSet→isSet (isFinSetGraphWalk _ _ _)

  first-edge :
    {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start (suc n)) →
    ⟨ directed-edges ⟩
  first-edge (cons _ e walk) = e

  tail :
    {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start (suc n)) →
    GraphWalk end (dst (first-edge walk)) n
  tail (cons _ e walk) = walk

  snoc :
    {start : ⟨ states ⟩} →
    (e : ⟨ directed-edges ⟩) →
    GraphWalk (src e) start n →
    GraphWalk (dst e) start (suc n)
  snoc e nil = cons 0 e nil
  snoc e (cons n e' walk) = cons (suc n) e' (snoc e walk)

  vertices :
    {end start : ⟨ states ⟩} →
    GraphWalk end start n →
    Fin (suc n) → ⟨ states ⟩
  vertices {start = start} walk zero = start
  vertices (cons n e walk) (suc m) = vertices walk m

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
  tailUniqueVertices (cons _ e walk) uniq =
    isEmbedding-∘ uniq (injEmbedding isSetFin injSucFin)

  dec-hasUniqueVertices :
    ∀ {end start : ⟨ states ⟩} → (walk : GraphWalk end start n) →
      Dec (hasUniqueVertices walk)
  dec-hasUniqueVertices nil =
    yes (injEmbedding (isFinSet→isSet (str states))
      (λ { {zero} {zero} → λ _ → refl }))
  dec-hasUniqueVertices (cons n e walk) =
    decRec
      (λ (k , p) → no (λ x →
        FD.znots (x zero (suc k) .equiv-proof (sym p) .fst .fst)))
      (λ ¬repeatFirst →
        decRec
          (λ uniqWalk → yes
            (λ j k →
              injEmbedding
                (isFinSet→isSet (str states))
                (λ {
                  {zero} {zero} → λ _ → refl
                ; {zero} {suc b} →
                  λ src≡vert →
                    ⊥.rec (¬repeatFirst (b , (sym src≡vert)))
                ; {suc a} {zero} →
                  λ src≡vert → ⊥.rec (¬repeatFirst (a , src≡vert))
                ; {suc a} {suc b} → λ verts≡ →
                  decRec
                    (λ a≡b → cong suc a≡b)
                    (λ ¬a≡b →
                      ⊥.rec
                        (¬a≡b (uniqWalk a b .equiv-proof verts≡ .fst .fst)))
                    (discreteFin a b)
                })
                j
                k)
          )
          (λ ¬uniqWalk → no (λ x → ¬uniqWalk (tailUniqueVertices _ x)))
          (dec-hasUniqueVertices walk)
      )
      (DecΣ (suc n) (λ k → vertices walk k ≡ src e)
      (λ k → isFinSet→Discrete (str states) (vertices walk k) (src e)))


  drop : {end start : ⟨ states ⟩} →
    (walk : GraphWalk end start n) →
    (k : Fin (suc n)) →
    Σ[ m ∈ ℕ ] GraphWalk end (vertices walk k) m
  drop walk zero = _ , walk
  drop (cons n e walk) (suc k) = drop walk k

  dropPreservesUnique :
    {end start : ⟨ states ⟩} →
    (uniqWalk : uniqueVerticesWalk end start) →
    (k : Fin (suc (uniqWalk .fst))) →
    hasUniqueVertices (drop (uniqWalk .snd .fst) k .snd)
  dropPreservesUnique uniqWalk zero = uniqWalk .snd .snd
  dropPreservesUnique (n , cons n-1 e walk , uniq) (suc k) =
    dropPreservesUnique
      (n-1 ,
      (walk , tailUniqueVertices (cons n-1 e walk) uniq)) k

  GraphPath : ∀ (end start : ⟨ states ⟩) → Type _
  GraphPath end start =
    Σ[ n ∈ Fin (card states) ]
    Σ[ walk ∈ GraphWalk end start (toℕ n) ] hasUniqueVertices walk


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
  makeUnique {end = end}(cons n e walk) =
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
        (cons n' new-edge walk' ,
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
  GraphWalk→GraphPath {end = end}{start = start} walk =
    let m , walk' , uniq = makeUnique walk in
    let bound = hasUniqueVertices→boundedLength walk' uniq in
    let to-and-fro = sym (toFromId' (card states) m bound) in
    fromℕ' (card states) m bound ,
      subst
        (λ n' → Σ[ walk ∈ GraphWalk end start n' ] hasUniqueVertices walk)
          to-and-fro (walk' , uniq)
    -- m , (hasUniqueVertices→boundedLength walk' uniq , walk' , uniq)

  Reachable PathReachable : ⟨ states ⟩ → ⟨ states ⟩ → Type _
  Reachable end start =
    PT.∥ Σ[ n ∈ ℕ ] GraphWalk end start n  ∥₁
  PathReachable end start =
    PT.∥ GraphPath end start ∥₁

  PathReachable≃Reachable :
    (end start : ⟨ states ⟩) → PathReachable end start ≃ Reachable end start
  PathReachable≃Reachable end start =
    propBiimpl→Equiv isPropPropTrunc isPropPropTrunc
      (PT.map (λ gp → (toℕ (gp .fst)) , (gp .snd .fst)))
      (PT.map (λ (n , gw) → GraphWalk→GraphPath gw))

  isFinSetHasUniqueVertices :
    {end start : ⟨ states ⟩} →
    (gw : GraphWalk end start n) → isFinSet (hasUniqueVertices gw)
  isFinSetHasUniqueVertices gw =
    isFinSetIsEmbedding (_ , isFinSetFin') states (vertices gw)

  module _
    (isFinOrd-directed-edges : isFinOrd ⟨ directed-edges ⟩)
    (end start : ⟨ states ⟩)
    where

    isFinOrdGraphPath : isFinOrd (GraphPath end start)
    isFinOrdGraphPath =
      isFinOrdΣ
        (Fin (states .snd .fst))
        ((card states) , Fin≃SumFin)
        (λ n → Σ-syntax (GraphWalk end start (toℕ n)) hasUniqueVertices)
        (λ m → isFinOrdΣ
          (GraphWalk end start (toℕ m))
          (isFinOrdGraphWalk isFinOrd-directed-edges (toℕ m) end start)
          hasUniqueVertices
          (λ walk → DecProp→isFinOrd ((_ , isPropIsEmbedding) , dec-hasUniqueVertices walk)))
    isFinSetGraphPath : isFinSet (GraphPath end start)
    isFinSetGraphPath =
      isFinOrd→isFinSet isFinOrdGraphPath

    DecPathReachable : Dec (PathReachable end start)
    DecPathReachable = isFinSet→Dec∥∥ isFinSetGraphPath

    DecReachable : Dec (Reachable end start)
    DecReachable =
      EquivPresDec
        (PathReachable≃Reachable end start)
        DecPathReachable

  Reachable-is-reflexive : (u : ⟨ states ⟩) → Reachable u u
  Reachable-is-reflexive u = ∣ 0 , nil ∣₁
