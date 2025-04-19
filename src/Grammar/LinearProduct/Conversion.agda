open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module @0 Grammar.LinearProduct.Conversion (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.More
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Epsilon.AsEquality Alphabet
open import Grammar.Epsilon.AsPath Alphabet
  hiding (ε-intro)
  renaming (ε to εPath
          ; ε* to ε*Path)
open import Grammar.Epsilon.Conversion Alphabet
open import Grammar.LinearProduct.AsEquality.Base Alphabet
import Grammar.LinearProduct.AsPath Alphabet as ⊗Path
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓE ℓF ℓG
      ℓH ℓK ℓL ℓM ℓN ℓO
      ℓ ℓ' : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD
    E : Grammar ℓE
    F : Grammar ℓF
    G : Grammar ℓG
    H : Grammar ℓH
    K : Grammar ℓK
    L : Grammar ℓL
    M : Grammar ℓM
    N : Grammar ℓN
    O : Grammar ℓO
    f f' f'' f''' f'''' f''''' : A ⊢ B
    g : C ⊢ D

opaque
  unfolding _⊗_ ⊗Path._⊗_
  ⊗→⊗Path : A ⊗ B ⊢ A ⊗Path.⊗ B
  ⊗→⊗Path _ (s , a , b) = Splitting→SplittingPath _ s , a , b

  ⊗Path→⊗ : A ⊗Path.⊗ B ⊢ A ⊗ B
  ⊗Path→⊗ _ (s , a , b) = SplittingPath→Splitting _ s , a , b

  ⊗Path→⊗→⊗Path : ⊗→⊗Path {A = A} {B = B} ∘g ⊗Path→⊗ ≡ id
  ⊗Path→⊗→⊗Path = funExt λ w → funExt λ where
    (s , a , b) → ΣPathP (SplittingIso w .Iso.rightInv s , refl)

  ⊗→⊗Path→⊗ : ⊗Path→⊗ {A = A} {B = B} ∘g ⊗→⊗Path ≡ id
  ⊗→⊗Path→⊗ = funExt λ w → funExt λ where
    (s , a , b) → ΣPathP (SplittingIso w .Iso.leftInv s , refl)

open StrongEquivalence

⊗≅⊗Path : A ⊗ B ≅ A ⊗Path.⊗ B
⊗≅⊗Path .fun = ⊗→⊗Path
⊗≅⊗Path .inv = ⊗Path→⊗
⊗≅⊗Path .sec = ⊗Path→⊗→⊗Path
⊗≅⊗Path .ret = ⊗→⊗Path→⊗

opaque
  unfolding _⊗_ ⊗-intro ⊗Path._⊗_ ⊗Path.⊗-intro ⊗→⊗Path
  ⊗→⊗Path-natural : (f : A ⊢ B) → (g : C ⊢ D) → ⊗→⊗Path ∘g f ,⊗ g ≡ f ⊗Path.,⊗ g ∘g ⊗→⊗Path
  ⊗→⊗Path-natural f g = refl

opaque
  unfolding _⊗_ ⊗-intro ⊗Path._⊗_ ⊗Path.⊗-intro
  opaque
    unfolding ε εPath ⊗Path.⊗-unit-r ⊗-unit-r ⊗→⊗Path ε→εPath
    ⊗-unit-r≡ : ⊗-unit-r {A = A} ≡ ⊗Path.⊗-unit-r ∘g ⊗→⊗Path ∘g id ,⊗ ε→εPath
    ⊗-unit-r≡ {A = A} =
      funExt λ w → funExt λ where
        (((w' , _) , Eq.refl) , a , Eq.refl) →
            (cong (λ z → Eq.transport A z a)
              (Eq.eqToPath (Eq.isPropPathToIsProp (isSetEqString _ _) _ (Eq.pathToEq (sym (++-unit-r w'))))))
            ∙ (Eq.eqToPath (Eq.transportPathToEq→transportPath A (sym (++-unit-r w')) a))
            ∙ (cong (λ z → subst A z a) (isSetString _ _ _ _))

    ⊗-unit-r⁻≡ : ⊗-unit-r⁻ {A = A} ≡ id ,⊗ εPath→ε ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-unit-r⁻
    ⊗-unit-r⁻≡ = funExt λ w → funExt λ where
       a → ΣPathP ((SplittingPathP refl) , Σ≡Prop (λ _ → isSetEqString _ _) refl)

  ⊗-unit-rr⁻ : ∀ {A : Grammar ℓA} → ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
  ⊗-unit-rr⁻ {A = A} =
    (λ i → ⊗-unit-r⁻≡ i ∘g ⊗-unit-r≡ i)
    ∙ (λ i → id ,⊗ εPath→ε ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-unit-rr⁻ i ∘g ⊗→⊗Path ∘g id ,⊗ ε→εPath)
    ∙ (λ i → id ,⊗ εPath→ε ∘g ⊗≅⊗Path .ret i ∘g id ,⊗ ε→εPath)
    ∙ λ i → id ,⊗ ε≅εPath .ret i

  ⊗-unit-r⁻r : ∀ {A : Grammar ℓA} → ⊗-unit-r {A = A} ∘g ⊗-unit-r⁻ ≡ id
  ⊗-unit-r⁻r {A = A} =
    (λ i → ⊗-unit-r≡ i ∘g ⊗-unit-r⁻≡ i)
    ∙ (λ i → ⊗Path.⊗-unit-r ∘g ⊗→⊗Path ∘g id ,⊗ ε≅εPath .sec i ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-unit-r⁻)
    ∙ (λ i → ⊗Path.⊗-unit-r ∘g ⊗≅⊗Path .sec i ∘g ⊗Path.⊗-unit-r⁻)
    ∙ (λ i → ⊗Path.⊗-unit-r⁻r i)

  opaque
    unfolding ε εPath ⊗Path.⊗-unit-l ⊗-unit-l ⊗→⊗Path ε→εPath
    ⊗-unit-l≡ : ⊗-unit-l {A = A} ≡ ⊗Path.⊗-unit-l ∘g ⊗→⊗Path ∘g ε→εPath ,⊗ id
    ⊗-unit-l≡ {A = A} =
      funExt λ w → funExt λ where
        (((_ , w') , Eq.refl) , Eq.refl , a) →
            subst-filler A refl a
            ∙ cong (λ z → subst A z a) (isSetString w w _ _)

  cong-∘g⊗-unit-r⁻ :
    (e e' : A ⊗ ε ⊢ B) →
    (e ∘g ⊗-unit-r⁻ ≡ e' ∘g ⊗-unit-r⁻) →
    e ≡ e'
  cong-∘g⊗-unit-r⁻ {A = A} f f' ∘g≡ =
    cong (f ∘g_) (sym ⊗-unit-rr⁻) ∙
    cong (_∘g ⊗-unit-r) ∘g≡ ∙
    cong (f' ∘g_) (⊗-unit-rr⁻)

  opaque
    unfolding the-split ⊗≡ ⊗-assoc ⊗→⊗Path ⊗Path.the-split ⊗Path.⊗≡ ⊗Path.⊗-assoc
    private
      ϕ : A ⊗ (B ⊗ C) ≅ A ⊗Path.⊗ (B ⊗Path.⊗ C)
      ϕ = ⊗≅⊗Path ≅∙ ⊗Path.⊗≅ id≅ ⊗≅⊗Path

      ψ : (A ⊗ B) ⊗ C ≅ (A ⊗Path.⊗ B) ⊗Path.⊗ C
      ψ = ⊗≅⊗Path ≅∙ ⊗Path.⊗≅ ⊗≅⊗Path id≅

    ⊗-assoc≡ : ⊗-assoc {A = A} {B = B} {C = C} ≡
      ⊗Path→⊗ ,⊗ id ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path
    ⊗-assoc≡ =
      funExt λ w → funExt λ where
      (((wa , wbc) , Eq.refl) , a , (((wb , wc) , Eq.refl) , b , c)) →
          (λ i → ((wa ++ wb , wc) ,
            isSetEqString (wa ++ wb ++ wc) ((wa ++ wb) ++ wc)
              (Eq.sym (++-assoc-Eq wa wb wc))
              (Eq.pathToEq (sym (++-assoc wa wb wc)))
              i) ,
          ((((wa , wb) ,
            isSetEqString (wa ++ wb) (wa ++ wb)
              (Eq.refl {x = wa ++ wb})
              (Eq.pathToEq {A = String} λ _ → wa ++ wb)
              i
          ) , a , b) , c))
          ∙ (cong (λ z → ψ .inv (wa ++ wb ++ wc) (((wa ++ wb , wc) , z) , (((wa , wb) , refl) , a , b) , c))
              (isSetString (wa ++ wb ++ wc) ((wa ++ wb) ++ wc)
                (sym (++-assoc wa wb wc))
                (refl ∙ cong (wa ++_) refl ∙ sym (++-assoc wa wb wc))))

    ⊗-assoc⁻≡ : ⊗-assoc⁻ {A = A} {B = B} {C = C} ≡
      id ,⊗ ⊗Path→⊗ ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc⁻ ∘g ⊗→⊗Path ∘g ⊗→⊗Path ,⊗ id
    ⊗-assoc⁻≡ = funExt λ w → funExt λ where
      (((wab , wc) , Eq.refl) , (((wa , wb) , Eq.refl) , a , b) , c) →
        (λ i → ((wa , wb ++ wc) ,
          isSetEqString ((wa ++ wb) ++ wc) (wa ++ wb ++ wc)
            (++-assoc-Eq wa wb wc) (Eq.pathToEq (++-assoc wa wb wc)) i) ,
            (a , ((wb , wc) ,
              isSetEqString (wb ++ wc) (wb ++ wc) Eq.refl (Eq.pathToEq {A = String} refl) i
            ) , b , c))
        ∙ cong (λ z → ϕ .inv ((wa ++ wb) ++ wc)
          (((wa , wb ++ wc) , z) , (a , (((wb , wc) , refl) , (b , c)))))
          (isSetString ((wa ++ wb) ++ wc) (wa ++ wb ++ wc) (++-assoc wa wb wc) (refl ∙ cong (_++ wc) refl ∙ ++-assoc wa wb wc))

    @0 ⊗-assoc∘⊗-assoc⁻≡id : ⊗-assoc {A = A}{B = B}{C = C} ∘g ⊗-assoc⁻ ≡ id
    ⊗-assoc∘⊗-assoc⁻≡id =
      (λ i → ⊗-assoc≡ i ∘g ⊗-assoc⁻≡ i)
      ∙ (λ i → ψ .inv ∘g ⊗Path.⊗-assoc ∘g ϕ .sec i ∘g ⊗Path.⊗-assoc⁻ ∘g ψ .fun)
      ∙ (λ i → ψ .inv ∘g ⊗Path.⊗-assoc∘⊗-assoc⁻≡id i ∘g ψ .fun)
      ∙ ψ .ret

    @0 ⊗-assoc⁻∘⊗-assoc≡id : ⊗-assoc⁻ {A = A}{B = B}{C = C} ∘g ⊗-assoc ≡ id
    ⊗-assoc⁻∘⊗-assoc≡id =
      (λ i → ⊗-assoc⁻≡ i ∘g ⊗-assoc≡ i)
      ∙ (λ i → ϕ .inv ∘g ⊗Path.⊗-assoc⁻ ∘g ψ .sec i ∘g ⊗Path.⊗-assoc ∘g ϕ .fun)
      ∙ (λ i → ϕ .inv ∘g ⊗Path.⊗-assoc⁻∘⊗-assoc≡id i ∘g ϕ .fun)
      ∙ ϕ .ret

    @0 ⊗-assoc⁻⊗-intro : ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
      → ⊗-assoc⁻ ∘g ((f ,⊗ f') ,⊗ f'') ≡ f ,⊗ (f' ,⊗ f'') ∘g ⊗-assoc⁻
    ⊗-assoc⁻⊗-intro {f = f} {f' = f'} {f'' = f''} =
      (λ i → ⊗-assoc⁻≡ i ∘g (f ,⊗ f') ,⊗ f'')
      ∙ (λ i → id ,⊗ ⊗Path→⊗ ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc⁻⊗-intro {f = f} {f' = f'} {f'' = f''} i
                             ∘g ⊗→⊗Path ∘g ⊗→⊗Path ,⊗ id)
      ∙ (λ i → f ,⊗ (f' ,⊗ f'') ∘g ⊗-assoc⁻≡ (~ i) )

    @0 ⊗-assoc⊗-intro : ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
      → ⊗-assoc ∘g f ,⊗ (f' ,⊗ f'') ≡ (f ,⊗ f') ,⊗ f'' ∘g ⊗-assoc
    ⊗-assoc⊗-intro {f = f} {f' = f'} {f'' = f''} =
      (λ i → ⊗-assoc≡ i ∘g f ,⊗ (f' ,⊗ f''))
      ∙ (λ i → ⊗Path→⊗ ,⊗ id ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc⊗-intro {f = f} {f' = f'} {f'' = f''} i
                             ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path )
      ∙ λ i → (f ,⊗ f') ,⊗ f'' ∘g ⊗-assoc≡ (~ i)

    opaque
      unfolding ⊗-unit-r⁻ ⊗Path.⊗-unit-r⁻
      @0 ⊗-assoc⁻⊗-unit-r⁻ : ⊗-assoc⁻ {A = A}{B = B} ∘g ⊗-unit-r⁻ ≡ id ,⊗ ⊗-unit-r⁻
      ⊗-assoc⁻⊗-unit-r⁻ {A = A} {B = B} =
        (λ i → ⊗-assoc⁻≡ i ∘g ⊗-unit-r⁻≡ i)
        ∙ (λ i → id ,⊗ ⊗Path→⊗ ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc⁻
                               ∘g ⊗→⊗Path ⊗Path.,⊗ id
                               ∘g id ⊗Path.,⊗ εPath→ε
                               ∘g ⊗≅⊗Path .sec i
                               ∘g ⊗Path.⊗-unit-r⁻)
        ∙ (λ i → id ,⊗ ⊗Path→⊗ ∘g ⊗Path→⊗
                               ∘g id ⊗Path.,⊗ id ⊗Path.,⊗ εPath→ε
                               ∘g ⊗Path.⊗-assoc⁻⊗-unit-r⁻ i
                               ∘g ⊗→⊗Path)
        ∙ (λ i → ⊗≅⊗Path .ret i ∘g id ,⊗ ⊗-unit-r⁻≡ (~ i))

      opaque
        unfolding ⊗-unit-l⁻ ⊗Path.⊗-unit-l⁻
        @0 ⊗-assoc⊗-unit-l⁻ : ⊗-assoc {A = A}{C = C} ∘g id ,⊗ ⊗-unit-l⁻ ≡ ⊗-unit-r⁻ ,⊗ id
        ⊗-assoc⊗-unit-l⁻ =
           funExt λ w → funExt λ where
             ((_ , Eq.refl) , a , c) → ⊗≡ _ _ (≡-× (++-unit-r _) refl)
               (ΣPathP ((⊗PathP refl refl) , refl))

        @0 ⊗-unit-l⊗-intro : ∀ (f : A ⊢ B) → f ∘g ⊗-unit-l ≡ ⊗-unit-l ∘g (id ,⊗ f)
        ⊗-unit-l⊗-intro f = cong-∘g⊗-unit-l⁻ _ _ λ i → ⊗-unit-l⁻l (~ i) ∘g f ∘g ⊗-unit-l⁻l i

      ⊗-unit-r⊗-intro : (f : A ⊢ B) → ⊗-unit-r ∘g f ,⊗ id ≡ f ∘g ⊗-unit-r
      ⊗-unit-r⊗-intro f = cong-∘g⊗-unit-r⁻ _ _ (λ i → ⊗-unit-r⁻r i ∘g f ∘g ⊗-unit-r⁻r (~ i))

  @0 ⊗-unit*-l⊗-intro : ∀ (f : A ⊢ B) → f ∘g ⊗-unit*-l {ℓ} ≡ ⊗-unit*-l ∘g (⊗-intro id f)
  ⊗-unit*-l⊗-intro f = cong₂ _∘g_ (⊗-unit-l⊗-intro f) refl

  @0 ⊗-unit*-r⊗-intro : ∀ (f : A ⊢ B) → ⊗-unit*-r {ℓ = ℓ} ∘g (⊗-intro f id) ≡ f ∘g ⊗-unit*-r
  ⊗-unit*-r⊗-intro {ℓ = ℓ} f = cong₂ _∘g_ (⊗-unit-r⊗-intro f) refl

  opaque
    unfolding ⊗-unit-r ⊗-unit-l ⊗-assoc ⊗Path.⊗-unit-r ⊗Path.⊗-unit-l ⊗Path.⊗-assoc ⊗→⊗Path
    @0 ⊗-triangle : ⊗-unit*-r ,⊗ id ∘g ⊗-assoc {A = A}{B = ε* {ℓ}}{C = B} ≡ id ,⊗ ⊗-unit*-l
    ⊗-triangle {A = A} {ℓ = ℓ} {B = B} =
      (⊗-unit-r ∘g id ,⊗ lowerG) ,⊗ id ∘g ⊗-assoc
         ≡⟨ (λ i → (⊗-unit-r≡ i ∘g id ,⊗ lowerG) ,⊗ id ∘g ⊗-assoc≡ i) ⟩
      ⊗Path.⊗-unit-r ,⊗ id
      ∘g (id ⊗Path.,⊗ ε→εPath) ,⊗ id
      ∘g (id ⊗Path.,⊗ lowerG) ,⊗ id
      ∘g (⊗→⊗Path ∘g ⊗Path→⊗) ,⊗ id
      ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path
        ≡⟨ (λ i → ⊗Path.⊗-unit-r ,⊗ id
                  ∘g (id ⊗Path.,⊗ ε→εPath) ,⊗ id
                  ∘g (id ⊗Path.,⊗ lowerG) ,⊗ id
                  ∘g (⊗≅⊗Path .sec i) ,⊗ id
                  ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path )⟩
      ⊗Path→⊗ ∘g ⊗Path.⊗-unit-r ⊗Path.,⊗ id
              ∘g (id ⊗Path.,⊗ lowerG {ℓB = ℓ}) ⊗Path.,⊗ id ∘g ⊗Path.⊗-assoc
              ∘g id ⊗Path.,⊗ (liftG ∘g ε→εPath ∘g lowerG) ⊗Path.,⊗ id
              ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path
        ≡⟨ (λ i →
             ⊗Path→⊗ ∘g ⊗Path.⊗-triangle {ℓ = ℓ} i
                     ∘g id ⊗Path.,⊗ (liftG ∘g ε→εPath ∘g lowerG) ⊗Path.,⊗ id
                     ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path
           ) ⟩
       id ,⊗ ⊗Path.⊗-unit-l ∘g id ,⊗ (ε→εPath ∘g lowerG) ⊗Path.,⊗ id
       ∘g ⊗Path→⊗ ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path
        ≡⟨ (λ i → id ,⊗ ⊗Path.⊗-unit-l ∘g id ,⊗ (ε→εPath ∘g lowerG) ⊗Path.,⊗ id
                  ∘g ⊗≅⊗Path .ret i ∘g id ,⊗ ⊗→⊗Path) ⟩
       id ,⊗ ⊗Path.⊗-unit-l ∘g id ,⊗ (ε→εPath ∘g lowerG) ⊗Path.,⊗ id ∘g id ,⊗ ⊗→⊗Path
        ≡⟨ cong (λ z → id ,⊗ (z ∘g lowerG ,⊗ id)) (sym ⊗-unit-l≡) ⟩
      id ,⊗ (⊗-unit-l ∘g lowerG ,⊗ id)
      ∎

    @0 ⊗-pentagon :
      (⊗-assoc {A = A}) ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ (⊗-assoc {A = B}{B = C}{C = D})
        ≡ ⊗-assoc ∘g ⊗-assoc
    ⊗-pentagon {A = A}{B = B}{C = C}{D = D} =
      ⊗-assoc ,⊗ id ∘g ⊗-assoc ∘g id ,⊗ ⊗-assoc
        ≡⟨ (λ i → ⊗-assoc≡ i ,⊗ id ∘g ⊗-assoc≡ i ∘g id ,⊗ ⊗-assoc≡ i) ⟩
      (⊗Path→⊗ ,⊗ id) ,⊗ id
      ∘g ⊗Path→⊗ ,⊗ id ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc ⊗Path.,⊗ id
      ∘g (⊗→⊗Path ∘g ⊗Path→⊗) ⊗Path.,⊗ id
      ∘g ⊗Path.⊗-assoc
      ∘g id ⊗Path.,⊗ ((⊗→⊗Path ∘g ⊗Path→⊗) ⊗Path.,⊗ id)
      ∘g id ⊗Path.,⊗ (⊗→⊗Path ∘g ⊗Path→⊗)
      ∘g id ⊗Path.,⊗ ⊗Path.⊗-assoc
      ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path ∘g id ,⊗ id ,⊗ ⊗→⊗Path
        ≡⟨ (λ i → (⊗Path→⊗ ,⊗ id) ,⊗ id
                  ∘g ⊗Path→⊗ ,⊗ id ∘g ⊗Path→⊗ ∘g ⊗Path.⊗-assoc ⊗Path.,⊗ id
                  ∘g (⊗≅⊗Path .sec i) ⊗Path.,⊗ id
                  ∘g ⊗Path.⊗-assoc
                  ∘g id ⊗Path.,⊗ ((⊗≅⊗Path .sec i) ⊗Path.,⊗ id)
                  ∘g id ⊗Path.,⊗ (⊗≅⊗Path .sec i)
                  ∘g id ⊗Path.,⊗ ⊗Path.⊗-assoc
                  ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path ∘g id ,⊗ id ,⊗ ⊗→⊗Path
           ) ⟩
      (⊗Path→⊗ ,⊗ id) ,⊗ id
      ∘g ⊗Path→⊗ ,⊗ id ∘g ⊗Path→⊗
      ∘g ⊗Path.⊗-assoc ⊗Path.,⊗ id
      ∘g ⊗Path.⊗-assoc
      ∘g id ⊗Path.,⊗ ⊗Path.⊗-assoc
      ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path ∘g id ,⊗ id ,⊗ ⊗→⊗Path
        ≡⟨ (λ i → (⊗Path→⊗ ,⊗ id) ,⊗ id
                  ∘g ⊗Path→⊗ ,⊗ id ∘g ⊗Path→⊗
                  ∘g ⊗Path.⊗-pentagon i
                  ∘g ⊗→⊗Path ∘g id ,⊗ ⊗→⊗Path ∘g id ,⊗ id ,⊗ ⊗→⊗Path)⟩
      ⊗Path→⊗ ,⊗ id
      ∘g ⊗Path→⊗
      ∘g ⊗Path.⊗-assoc
      ∘g ⊗Path→⊗ ⊗Path.,⊗ id
      ∘g id
      ∘g id ⊗Path.,⊗ ⊗→⊗Path
      ∘g ⊗Path.⊗-assoc
      ∘g ⊗→⊗Path
      ∘g id ,⊗ ⊗→⊗Path
        ≡⟨ {!!} ⟩
      ⊗-assoc ∘g ⊗-assoc
      ∎

-- -- @0 ⊗-assoc⁻3⊗-unit-r⁻ :
-- --   ⊗-assoc⁻3 {A = A}{B = B}{C = C} ∘g ⊗-unit-r⁻
-- --   ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
-- -- ⊗-assoc⁻3⊗-unit-r⁻ =
-- --   {!!}

-- -- @0 ⊗-assoc⁻3⊗-unit-r⁻ :
-- --   ⊗-assoc⁻3 {A = A}{B = B}{C = C} ∘g ⊗-unit-r⁻
-- --   ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
-- -- ⊗-assoc⁻3⊗-unit-r⁻ =
-- --   {!!}

-- --   @0 ⊗-assoc⁻4⊗-intro :
-- --     ∀ {f f' f'' f''' f''''} →
-- --     (⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''')
-- --     ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''' ∘g (⊗-assoc⁻4 {A = F}{B = G}{C = H}{D = K}{E = L}))
-- --   ⊗-assoc⁻4⊗-intro = {!!} -- refl

-- --   @0 ⊗-assoc4⊗-intro :
-- --     ⊗-assoc4 ∘g f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f''''
-- --     ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''' ∘g ⊗-assoc4
-- --   ⊗-assoc4⊗-intro {f = f}{f' = f'}{f'' = f''}{f''' = f'''}{f'''' = f''''} =
-- --     {!!}
