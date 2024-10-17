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
import Cubical.Data.FinData as FD
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum hiding (rec ; map)
import Cubical.Data.Equality as Eq

open import Cubical.HITs.PropositionalTruncation as PT hiding (rec)
import Cubical.HITs.PropositionalTruncation.Monad as PTMonad

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.Inductive.Indexed Alphabet as Idx
open import Term Alphabet
open import NFA.Base Alphabet
open import DFA Alphabet
open import Helper

open import Cubical.Data.Quiver.Base -- from cubical-categorical-logic
open import Quiver.Reachability

private
  variable
    ℓN ℓ : Level

open NFA
open StrongEquivalence

module _
  (N : NFA ℓN)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩ )
  (isFinOrd-Q : isFinOrd ⟨ N .Q ⟩)
  (isFinOrd-transition : isFinOrd ⟨ N .transition ⟩)
  (isFinOrd-ε-transition : isFinOrd ⟨ N .ε-transition ⟩)
  where
  private
    module N = NFA N

  ε-quiver : QuiverOver ⟨ N.Q ⟩ ℓN
  ε-quiver .QuiverOver.mor = ⟨ N.ε-transition ⟩
  ε-quiver .QuiverOver.dom = N.ε-src
  ε-quiver .QuiverOver.cod = N.ε-dst

  open QuiverOver ε-quiver

  is-ε-closed : ⟨ FinSetDecℙ N.Q ⟩ → Type ℓN
  is-ε-closed X =
    (t : ⟨ N.ε-transition ⟩) (x : ⟨ N.Q ⟩)
    (src∈X : X (N.ε-src t) .fst .fst) →
    X (N.ε-dst t) .fst .fst

  isProp-is-ε-closed : ∀ X → isProp (is-ε-closed X)
  isProp-is-ε-closed X = isPropΠ λ t → isPropΠ λ _ → isPropΠ λ _ →
    X (N.ε-dst t) .fst .snd

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

  εClosedℙQ : Type (ℓ-suc ℓN)
  εClosedℙQ = Σ ⟨ FinSetDecℙ N.Q ⟩ is-ε-closed

  isFinSet-εClosedℙQ : isFinSet εClosedℙQ
  isFinSet-εClosedℙQ =
    isFinSetΣ (FinSetDecℙ N.Q) λ X → _ , (isFinSet-is-ε-closed X)

  _∈ε_ : ⟨ N.Q ⟩ → εClosedℙQ → Type ℓN
  q ∈ε qs = qs .fst q .fst .fst

  open Reachability N.Q ε-quiver (str N.ε-transition)
  opaque
    -- The decidable finite set of states reachable from q-start
    ε-reach : ⟨ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    ε-reach q-start q-end .fst = _ , isPropPropTrunc
    ε-reach q-start q-end .snd =
      DecReachable isFinOrd-ε-transition q-end q-start

    ε-reach-is-ε-closed : ∀ q-start → is-ε-closed (ε-reach q-start)
    ε-reach-is-ε-closed q-start t x x-is-reachable =
      PT.rec isPropPropTrunc
        (λ (n , walk) → ∣ (suc n) , snocWalk t walk ∣₁)
        x-is-reachable

    ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → εClosedℙQ
    ε-closure X .fst = FinSetDecℙ∃ N.Q N.Q X ε-reach
    ε-closure X .snd t x x∈X = do
      (a , a∈X , reach) ← x∈X
      return (a , a∈X , ε-reach-is-ε-closed a t x reach)
      where open PTMonad

    ε-closure-lift-∈ :
      {A : Decℙ ⟨ N.Q ⟩} {a : ⟨ N.Q ⟩} →
      _∈-FinSetDecℙ_ {A = N.Q} a A → a ∈ε (ε-closure A)
    ε-closure-lift-∈ a∈A = ∣ _ , (a∈A , (Reachable-is-reflexive _)) ∣₁

    ε-closure-transition :
      (t : ⟨ N.ε-transition ⟩) →
      (X : εClosedℙQ) →
      N.ε-src t ∈ε X →
      N.ε-dst t ∈ε X
    ε-closure-transition t X src∈X = X .snd t (N.ε-src t) src∈X

    isFinOrd-εclosure-witnesses :
      (q : ⟨ N.Q ⟩) →
      (X : ⟨ FinSetDecℙ N.Q ⟩ ) →
      (q ∈ε (ε-closure X)) →
      isFinOrd (
        Σ[ q' ∈ ⟨ N.Q ⟩ ]
        Σ[ q'∈X ∈ X q' .fst .fst ]
        ∥ Walk' q q' ∥₁)
    isFinOrd-εclosure-witnesses q X q∈X =
      isFinOrdΣ ⟨ N.Q ⟩ isFinOrd-Q _
        λ q' → isFinOrdΣ (X q' .fst .fst) (DecProp→isFinOrd (X q')) _
          λ q'∈X →
            DecProp→isFinOrd
              ((∥ Walk' q q' ∥₁ , isPropPropTrunc) ,
              DecReachable isFinOrd-ε-transition q q')

    witness-ε :
      (q : ⟨ N.Q ⟩) → (X : ⟨ FinSetDecℙ N.Q ⟩ ) →
      q ∈ε (ε-closure X) →
      (Σ[ q' ∈ ⟨ N.Q ⟩ ]
       Σ[ q'∈X ∈ X q' .fst .fst ]
       Σ[ n ∈ ℕ ]
       Walk q q' n)
    witness-ε q X q∈εX =
      let
        q' , q'∈X , ∣walk'∣ =
          SplitSupport-FinOrd (isFinOrd-εclosure-witnesses q X q∈εX) q∈εX in
      let
        n , walk , uniq =
          SplitSupport-FinOrd
            (isFinOrdUniqueWalk isFinOrd-ε-transition q q')
            (PT.map (λ (n , walk) → Walk→UniqueWalk walk) ∣walk'∣) in
      q' , q'∈X , FD.toℕ n , walk

  opaque
    unfolding ε-closure
    lit-reach : ⟨ Alphabet ⟩ → ⟨ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    lit-reach c q-start =
      N.hasTransition (isFinSet→Discrete isFinSetAlphabet) q-start c

    lit-closure : ⟨ Alphabet ⟩ → ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
    lit-closure c X = FinSetDecℙ∃ N.Q N.Q X (lit-reach c)

    lit-closure-transition :
      (t : ⟨ N.transition ⟩) →
      (X : εClosedℙQ) →
      N.src t ∈ε X →
      N.dst t ∈ε ε-closure (lit-closure (N.label t) (X .fst))
    lit-closure-transition t X src∈X =
      ∣ (N.dst t) ,
        (∣ (N.src t) , (src∈X , ∣ t , refl , refl , refl ∣₁) ∣₁ ,
          ∣ 0 , nil ∣₁) ∣₁

    isFinOrd-matching-transition :
      (c : ⟨ Alphabet ⟩) →
      (q q' : ⟨ N.Q ⟩) →
      isFinOrd(Σ[ t ∈ ⟨ N.transition ⟩ ]
         (N.label t Eq.≡ c) ×
         (N.src t Eq.≡ q') ×
         (N.dst t Eq.≡ q))
    isFinOrd-matching-transition c q q' =
         isFinOrdΣ ⟨ N.transition ⟩ isFinOrd-transition
              _ λ t →
              isFinOrdΣ (N.label t Eq.≡ c)
                (DecProp→isFinOrd (isFinSet→DecProp-Eq≡ isFinSetAlphabet (N.label t) c)) _
               (λ _ → isFinOrdΣ _ (DecProp→isFinOrd (isFinSet→DecProp-Eq≡ (str N.Q) (N.src t) q')) _
                 λ _ → DecProp→isFinOrd (isFinSet→DecProp-Eq≡ (str N.Q) (N.dst t) q))

    isFinOrd-litclosure-witnesses :
      (c : ⟨ Alphabet ⟩) →
      (q : ⟨ N.Q ⟩) →
      (X : ⟨ FinSetDecℙ N.Q ⟩ ) →
      (lit-closure c X q .fst .fst) →
      isFinOrd (
        Σ[ q' ∈ ⟨ N.Q ⟩ ]
        Σ[ q'∈X ∈ X q' .fst .fst ]
        ∥ Σ[ t ∈ ⟨ N.transition ⟩ ]
         (N.label t Eq.≡ c) ×
         (N.src t Eq.≡ q') ×
         (N.dst t Eq.≡ q) ∥₁)
    isFinOrd-litclosure-witnesses c q X q∈litX =
      isFinOrdΣ ⟨ N.Q ⟩ isFinOrd-Q _ (λ q' →
        isFinOrdΣ (X q' .fst .fst) (DecProp→isFinOrd (X q')) _
          λ q'∈X →
            isFinOrd∥∥ _ (isFinOrd-matching-transition c q q') )

    witness-lit :
      (c : ⟨ Alphabet ⟩) → (q : ⟨ N.Q ⟩) → (X : ⟨ FinSetDecℙ N.Q ⟩ ) →
      (lit-closure c X) q .fst .fst →
      (Σ[ q' ∈ ⟨ N.Q ⟩  ]
       Σ[ q'∈X ∈ X q' .fst .fst  ]
       Σ[ t ∈ ⟨ N.transition ⟩ ]
         (N.label t Eq.≡ c) ×
         (N.src t Eq.≡ q') ×
         (N.dst t Eq.≡ q))
    witness-lit c q X q∈litX =
      let
        q' , q'∈X , ∣t∣ =
          SplitSupport-FinOrd (isFinOrd-litclosure-witnesses c q X q∈litX)
            (PT.map
            (λ (q' , q'∈X , ∣t∣) →
              q' ,
              q'∈X ,
              PT.map (λ { (t , c≡ , src≡ , dst≡) →
                (t ,
                Eq.pathToEq (cong lower (sym c≡)) ,
                Eq.pathToEq (cong lower (sym src≡)) ,
                Eq.pathToEq (cong lower (sym dst≡))
                ) }) ∣t∣)
            q∈litX) in
      let
        t , c≡ , src≡ , dst≡ =
          SplitSupport-FinOrd (isFinOrd-matching-transition c q q') ∣t∣
      in
      q' , q'∈X , t , c≡ , src≡ , dst≡


  -- TODO this should go elsewhere
  witness-true :
    (A : DecProp' ℓ) → A .fst →
    true Eq.≡ Bool-iso-DecProp' .Isom.Iso.inv A
  witness-true {ℓ} (ty , true , _) a = Eq.refl
  witness-true {ℓ} (ty , false , snd₁) a = Empty.rec (snd₁ .fst a)

  truth→witness :
    (b : Bool) → true Eq.≡ b →
    Isom.Iso.fun (Bool-iso-DecProp' {ℓ = ℓN}) b .fst
  truth→witness true true≡b = lift tt

  ℙNAcc-DecProp' : (X : εClosedℙQ) → DecProp' ℓN
  ℙNAcc-DecProp' X =
    DecProp'∃ N.Q
      (λ q → DecProp'×
              (DecℙIso ⟨ N.Q ⟩ .Isom.Iso.fun (X .fst) q)
              (Bool-iso-DecProp' .Isom.Iso.fun (N .isAcc q)))

  open DeterministicAutomaton
  ℙN : DFA (εClosedℙQ , isFinSet-εClosedℙQ)
  ℙN .init = ε-closure (SingletonDecℙ {A = N.Q} N.init)
  ℙN .isAcc X = Bool-iso-DecProp' .Isom.Iso.inv (ℙNAcc-DecProp' X)
  ℙN .δ X c = ε-closure (lit-closure c (X .fst))

  private
    module ℙN = DeterministicAutomaton ℙN

  isFinOrd-q∈X-acc :
    (X : εClosedℙQ) →
    isFinOrd (
      Σ[ q ∈ ⟨ N.Q ⟩ ]
      Σ[ q∈X ∈ q ∈ε X ] true Eq.≡ N.isAcc q)
  isFinOrd-q∈X-acc X =
    isFinOrdΣ ⟨ N.Q ⟩ isFinOrd-Q _
      (λ q →
        isFinOrdΣ (X .fst q .fst .fst) (DecProp→isFinOrd (X .fst q)) _
          (λ _ → DecProp→isFinOrd (isFinSet→DecProp-Eq≡ isFinSetBool true (N.isAcc q))))

  chooseAcc :
    (X : εClosedℙQ) →
    (accX : true Eq.≡ ℙN.isAcc X) →
    (Σ[ q ∈ ⟨ N.Q ⟩ ] Σ[ q∈X ∈ q ∈ε X ] true Eq.≡ N.isAcc q)
  chooseAcc X accX =
    let
      ∣q,q∈X,acc?∣ =
        subst
        (λ y → y .fst)
        (Bool-iso-DecProp' .Isom.Iso.rightInv (ℙNAcc-DecProp' X))
          (truth→witness (ℙN.isAcc X) accX)
      in
      SplitSupport-FinOrd (isFinOrd-q∈X-acc X)
        (PT.map (λ (q , q∈X , acc?) →
          q ,
          q∈X ,
          Bool-iso-DecProp'-witness→truth (N .isAcc q) acc?) ∣q,q∈X,acc?∣)

  embedAcc : (q : ⟨ N.Q ⟩) → (X : εClosedℙQ) → (q ∈ε X) → true Eq.≡ N.isAcc q →
    true Eq.≡ ℙN.isAcc X
  embedAcc q X q∈X acc =
    witness-true
      (ℙNAcc-DecProp' X)
      ∣ q , (q∈X , truth→witness (N.isAcc q) acc) ∣₁

  NFA→DFA-alg :
    Algebra (N.TraceTy true)
      (λ q →
        &[ X ∈ εClosedℙQ ]
        &[ q∈X ∈ q ∈ε X ] ℙN.Trace true X
      )
  NFA→DFA-alg q =
    ⊕ᴰ-elim (λ {
        stop → ⊕ᴰ-elim (λ {
          (lift acc) → &ᴰ-in λ X →
            &ᴰ-in (λ q∈X →
              roll ∘g
              ⊕ᴰ-in ℙN.stop ∘g
              ⊕ᴰ-in (lift (embedAcc q X q∈X acc)) ∘g
              liftG ∘g liftG ∘g lowerG ∘g lowerG
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

  fold-walk :
    (q : ⟨ N.Q ⟩) → (X : ⟨ FinSetDecℙ N.Q ⟩) →
    (q' : ⟨ N.Q ⟩) →
    (q∈εX : q ∈ε ε-closure X) →
    (q'-[ε*]→q : Walk' q q') →
    N.Trace true q ⊢ N.Trace true q'
  fold-walk q X q' q∈εX (0 , nil) = id
  fold-walk q X q' q∈εX (n , (cons n-1 e walk)) =
    roll ∘g
    ⊕ᴰ-in N.stepε ∘g
    ⊕ᴰ-in (e , Eq.refl) ∘g
    liftG ∘g
    fold-walk q X (N.ε-dst e) q∈εX (n-1 , walk)

  NFA→DFA : ∀ q →
    N.Trace true q ⊢
      &[ X ∈ εClosedℙQ ]
      &[ q∈X ∈ q ∈ε X ] ℙN.Trace true X
  NFA→DFA q = rec (N.TraceTy true) NFA→DFA-alg q

  DFA→NFA-alg :
    Algebra (ℙN.TraceTy true)
      (λ X → ⊕[ q ∈ ⟨ N.Q ⟩ ] ⊕[ q∈X ∈ q ∈ε X ] N.Trace true q)
  DFA→NFA-alg X =
    ⊕ᴰ-elim (λ {
      stop → ⊕ᴰ-elim (λ { (lift accX) →
        let
          q , q∈X , acc = chooseAcc X accX
        in
        ⊕ᴰ-in q ∘g
        ⊕ᴰ-in q∈X ∘g
        roll ∘g
        ⊕ᴰ-in N.stop ∘g
        ⊕ᴰ-in (lift acc) ∘g
        liftG ∘g liftG ∘g lowerG ∘g lowerG
      })
    ; step → ⊕ᴰ-elim (λ { (lift c) →
      ⊕ᴰ-elim (λ q →
        ⊕ᴰ-elim (λ q∈εlitX →
          let q' , q'∈litX , n , walk = witness-ε q (lit-closure c (X .fst)) q∈εlitX in
          let qt , qt∈X , t , label≡c , src≡qt , dst≡q' = witness-lit c q' (X .fst) q'∈litX in
          ⊕ᴰ-in qt ∘g
          ⊕ᴰ-in qt∈X ∘g
          step-help c q (X .fst) q∈εlitX q' q'∈litX n walk
                    t qt qt∈X label≡c src≡qt dst≡q'
          ) ∘g
        ⊕ᴰ-distR .fun
      ) ∘g
      ⊕ᴰ-distR .fun ∘g
      lowerG ,⊗ id ∘g
      lowerG ,⊗ lowerG
    }) })
    where
    step-help : ∀
      (c : ⟨ Alphabet ⟩) →
      (q : ⟨ N.Q ⟩) →
      (X : ⟨ FinSetDecℙ N.Q ⟩ ) →
      (q∈εlitX : q ∈ε ε-closure (lit-closure c X)) →
      (q' : ⟨ N.Q ⟩) →
      (q'∈litX : (lit-closure c X) q' .fst .fst) →
      (n : ℕ) →
      (walk : Walk q q' n) →
      (t : ⟨ N.transition ⟩ ) →
      (qt : ⟨ N.Q ⟩) →
      (qt∈X : X qt .fst .fst) →
      (N.label t Eq.≡ c) →
      (N.src t Eq.≡ qt) →
      (N.dst t Eq.≡ q') →
      (literal c) ⊗ N.Trace true q ⊢ N.Trace true qt
    step-help c q X q∈εlitX q' q'∈litX n walk t qt qt∈x
      Eq.refl Eq.refl Eq.refl =
      roll ∘g
      ⊕ᴰ-in N.step ∘g
      ⊕ᴰ-in (t , Eq.refl) ∘g
      liftG ,⊗ liftG ∘g
      id ,⊗ fold-walk q (lit-closure c X) q' q∈εlitX (n , walk) ∘g
      liftG ,⊗ id

  DFA→NFA : ∀ X →
    ℙN.Trace true X ⊢
      ⊕[ q ∈ ⟨ N.Q ⟩ ]
      ⊕[ q∈X ∈ q ∈ε X ] N.Trace true q
  DFA→NFA X = rec (ℙN.TraceTy true) DFA→NFA-alg X

  DFA→NFA-init :
    ℙN.Trace true (ε-closure (SingletonDecℙ {A = N.Q} N.init))
      ⊢ N.Trace true (N .init)
  DFA→NFA-init =
    ⊕ᴰ-elim (λ q → ⊕ᴰ-elim (λ q∈εinit →
      let q' , q'∈Singleton , walk = witness-ε q (SingletonDecℙ {A = N.Q} N.init) q∈εinit in
      fold-walk q (SingletonDecℙ {A = N.Q} N.init) N.init q∈εinit
      (subst (Walk' q) q'∈Singleton walk))) ∘g
    DFA→NFA (ε-closure (SingletonDecℙ {A = N.Q} N.init))

  NFA≈DFA : isLogicallyEquivalent
              (N.Trace true N.init)
              (ℙN.Trace true (ε-closure (SingletonDecℙ {A = N.Q} N.init)))
  NFA≈DFA .fst = &ᴰ-π (ε-closure-lift-∈ refl) ∘g &ᴰ-π _ ∘g NFA→DFA N.init
  NFA≈DFA .snd = DFA→NFA-init
