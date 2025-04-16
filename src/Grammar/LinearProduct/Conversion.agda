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
  renaming (ε to εPath)
open import Grammar.Epsilon.Conversion Alphabet
open import Grammar.LinearProduct.AsEquality.Base Alphabet
import Grammar.LinearProduct.AsPath Alphabet as ⊗Path
  -- renaming (_⊗_ to _⊗Path_
  --         ; _,⊗_ to _,⊗Path_
  --         ; ⊗≡ to ⊗Path≡
  --         ; ⊗-assoc to ⊗Path-assoc
  --         ; the-split to the-splitPath
  --         ; ⊗-intro to ⊗Path-intro
  --         ; ⊗-unit-r to ⊗Path-unit-r
  --         ; ⊗-unit-r⁻ to ⊗Path-unit-r⁻
  --         ; ⊗-unit-rr⁻ to ⊗Path-unit-rr⁻
  --         ; ⊗-unit-r⁻r to ⊗Path-unit-r⁻r
  --         ; ⊗≅ to ⊗Path≅)
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

⊗ε-eqToPath≅ : A ⊗ ε ≅ A ⊗Path.⊗ εPath
⊗ε-eqToPath≅ =
  ⊗≅⊗Path
  ≅∙ ⊗Path.⊗≅ id≅ ε≅εPath

opaque
  unfolding _⊗_ ε εPath ⊗Path.⊗-unit-r ⊗-unit-r ⊗-intro ⊗Path.⊗-intro ⊗→⊗Path ε→εPath
  -- If equalities like this one can be proven as compatibilities
  -- between the AsPath and AsEquality variants of LinearProduct,
  -- then maybe we can use them as fixes to port old proofs over
  -- to the new definitons using Data.Equality
  ⊗-unit-r⁻≡ : ⊗-unit-r⁻ {A = A} ≡ ⊗ε-eqToPath≅ .inv ∘g ⊗Path.⊗-unit-r⁻
  ⊗-unit-r⁻≡ =
    funExt λ w → funExt λ where
     a →
      ΣPathP ((SplittingPathP refl) ,
              Σ≡Prop (λ _ → isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString _ _))
                     refl)

  ⊗-unit-r≡ : ⊗-unit-r {A = A} ≡ ⊗Path.⊗-unit-r ∘g ⊗ε-eqToPath≅ .fun
  ⊗-unit-r≡ {A = A} =
    funExt λ w → funExt λ where
      (((w' , _) , Eq.refl) , a , Eq.refl) →
          (cong (λ z → Eq.transport A z a)
            (Eq.eqToPath (Eq.isPropPathToIsProp
              (isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString _ _))
                _ (Eq.pathToEq (sym (++-unit-r w'))))))
          ∙ (Eq.eqToPath (Eq.transportPathToEq→transportPath A (sym (++-unit-r w')) a))
          ∙ (cong (λ z → subst A z a) (isSetString _ _ _ _))

⊗-unit-rr⁻ :
  ∀ {A : Grammar ℓA}
  → ⊗-unit-r⁻ {A = A} ∘g ⊗-unit-r ≡ id
⊗-unit-rr⁻ {A = A} =
  (λ i → ⊗-unit-r⁻≡ i ∘g ⊗-unit-r≡ i)
  ∙ (λ i → ⊗ε-eqToPath≅ .inv ∘g ⊗Path.⊗-unit-rr⁻ i ∘g ⊗ε-eqToPath≅ .fun)
  ∙ ⊗ε-eqToPath≅ .ret

⊗-unit-r⁻r :
  ∀ {A : Grammar ℓA}
  → ⊗-unit-r {A = A} ∘g ⊗-unit-r⁻ ≡ id
⊗-unit-r⁻r {A = A} =
  (λ i → ⊗-unit-r≡ i ∘g ⊗-unit-r⁻≡ i)
  ∙ (λ i → ⊗Path.⊗-unit-r ∘g ⊗ε-eqToPath≅ .sec i ∘g ⊗Path.⊗-unit-r⁻)
  ∙ ⊗Path.⊗-unit-r⁻r

opaque
  unfolding _⊗_ the-split ⊗-intro ⊗≡ ⊗-assoc ⊗→⊗Path ⊗Path._⊗_ ⊗Path.the-split ⊗Path.⊗-intro ⊗Path.⊗≡ ⊗Path.⊗-assoc
  private
    ϕ : A ⊗ (B ⊗ C) ≅ A ⊗Path.⊗ (B ⊗Path.⊗ C)
    ϕ = ⊗≅⊗Path ≅∙ ⊗Path.⊗≅ id≅ ⊗≅⊗Path

    ψ : (A ⊗ B) ⊗ C ≅ (A ⊗Path.⊗ B) ⊗Path.⊗ C
    ψ = ⊗≅⊗Path ≅∙ ⊗Path.⊗≅ ⊗≅⊗Path id≅

  ⊗-assoc≡ : ⊗-assoc {A = A} {B = B} {C = C} ≡ ψ .inv ∘g ⊗Path.⊗-assoc ∘g ϕ .fun
  ⊗-assoc≡ = funExt λ w → funExt λ where
    (((wa , wbc) , Eq.refl) , a , (((wb , wc) , Eq.refl) , b , c)) →
      let
        -- TODO make this a global lemma
        isPropEqString : ∀ (u v : String) → isProp (u Eq.≡ v)
        isPropEqString u v = isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetString _ _)
      in
        (λ i → ((wa ++ wb , wc) ,
        isPropEqString (wa ++ wb ++ wc) ((wa ++ wb) ++ wc)
          (Eq.sym (++-assoc-Eq wa wb wc))
          (Eq.pathToEq (sym (++-assoc wa wb wc)))
          i) ,
        ((((wa , wb) ,
          isPropEqString (wa ++ wb) (wa ++ wb)
            (Eq.refl {x = wa ++ wb})
            (Eq.pathToEq {A = String} λ _ → wa ++ wb)
            i
        ) , a , b) , c))
        ∙ (cong (λ z → ψ .inv (wa ++ wb ++ wc) (((wa ++ wb , wc) , z) , (((wa , wb) , refl) , a , b) , c))
            (isSetString (wa ++ wb ++ wc) ((wa ++ wb) ++ wc)
              (sym (++-assoc wa wb wc))
              (refl ∙ cong (wa ++_) refl ∙ sym (++-assoc wa wb wc))))

  -- @0 ⊗-assoc∘⊗-assoc⁻≡id :
  --  ⊗-assoc {A = A}{B = B}{C = C} ∘g ⊗-assoc⁻ ≡ id
  -- ⊗-assoc∘⊗-assoc⁻≡id = funExt λ w → funExt λ where
  --   ((_ , Eq.refl) , ((_ , Eq.refl) , a , b) , c) → {!!}

--   @0 ⊗-assoc⁻∘⊗-assoc≡id :
--    ⊗-assoc⁻ {A = A}{B = B}{C = C} ∘g ⊗-assoc ≡ id
--   ⊗-assoc⁻∘⊗-assoc≡id = {!!}

--   @0 ⊗-assoc⁻⊗-intro :
--     ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
--     → ⊗-assoc⁻ ∘g (⊗-intro (⊗-intro f f') f'')
--     ≡ ⊗-intro f (⊗-intro f' f'') ∘g ⊗-assoc⁻
--   ⊗-assoc⁻⊗-intro = {!!}

--   @0 ⊗-assoc⊗-intro :
--     ∀ {f : A ⊢ B}{f' : C ⊢ D}{f'' : E ⊢ F}
--     → ⊗-assoc ∘g ⊗-intro f (⊗-intro f' f'')
--       ≡ ⊗-intro (⊗-intro f f') f'' ∘g ⊗-assoc
--   ⊗-assoc⊗-intro = {!!}

--   opaque
--     unfolding ⊗-unit-r⁻
--     @0 ⊗-assoc⁻⊗-unit-r⁻ :
--       ⊗-assoc⁻ {A = A}{B = B} ∘g ⊗-unit-r⁻ ≡ ⊗-intro id ⊗-unit-r⁻
--     ⊗-assoc⁻⊗-unit-r⁻ =
--       {!!}
--     -- funExt λ w → funExt λ p →
--     --   ⊗≡ _ _ (≡-× refl (++-unit-r _))
--     --     (ΣPathP (refl , ⊗PathP refl refl))

--   opaque
--     unfolding ⊗-unit-l⁻
--     ⊗-assoc⊗-unit-l⁻ :
--      ⊗-assoc {A = A}{C = C} ∘g ⊗-intro id ⊗-unit-l⁻ ≡ ⊗-intro ⊗-unit-r⁻ id
--     ⊗-assoc⊗-unit-l⁻ = funExt λ w → funExt λ p →
--       -- ⊗≡ _ _ (≡-× (++-unit-r _) refl) (ΣPathP (⊗PathP refl refl , refl))
--       {!!}

--     ⊗-unit-l⊗-intro :
--       ∀ (f : A ⊢ B)
--       → f ∘g ⊗-unit-l
--         ≡ ⊗-unit-l ∘g (⊗-intro id f)
--     ⊗-unit-l⊗-intro f =
--       {!!}

--     ⊗-unit-r⊗-intro :
--       (f : A ⊢ B) →
--       ⊗-unit-r ∘g ⊗-intro f id ≡ f ∘g ⊗-unit-r
--     ⊗-unit-r⊗-intro f =
--       {!!}

--   @0 ⊗-unit*-l⊗-intro :
--       ∀ (f : A ⊢ B)
--       → f ∘g ⊗-unit*-l {ℓ}
--         ≡ ⊗-unit*-l ∘g (⊗-intro id f)
--   ⊗-unit*-l⊗-intro f =
--     cong₂ _∘g_ (⊗-unit-l⊗-intro f) refl

--   @0 ⊗-unit*-r⊗-intro :
--       ∀ (f : A ⊢ B)
--       → ⊗-unit*-r {ℓ = ℓ} ∘g (⊗-intro f id)
--         ≡ f ∘g ⊗-unit*-r
--   ⊗-unit*-r⊗-intro {ℓ = ℓ} f = cong₂ _∘g_ (⊗-unit-r⊗-intro f) refl

--   @0 ⊗-triangle :
--     ⊗-intro ⊗-unit*-r id ∘g ⊗-assoc {A = A}{B = ε* {ℓ}}{C = B}
--     ≡ ⊗-intro id ⊗-unit*-l
--   ⊗-triangle {A = A}{B = B} =
--     {!!}

--   @0 ⊗-pentagon :
--     ⊗-intro (⊗-assoc {A = A}) id
--     ∘g ⊗-assoc
--     ∘g ⊗-intro id (⊗-assoc {A = B}{B = C}{C = D})
--       ≡
--     ⊗-assoc
--     ∘g ⊗-assoc
--   ⊗-pentagon {A = A}{B = B}{C = C}{D = D} =
--     {!!}

-- @0 ⊗-assoc⁻3⊗-unit-r⁻ :
--   ⊗-assoc⁻3 {A = A}{B = B}{C = C} ∘g ⊗-unit-r⁻
--   ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
-- ⊗-assoc⁻3⊗-unit-r⁻ =
--   {!!}

-- @0 ⊗-assoc⁻3⊗-unit-r⁻ :
--   ⊗-assoc⁻3 {A = A}{B = B}{C = C} ∘g ⊗-unit-r⁻
--   ≡ id ,⊗ id ,⊗ ⊗-unit-r⁻
-- ⊗-assoc⁻3⊗-unit-r⁻ =
--   {!!}

--   @0 ⊗-assoc⁻4⊗-intro :
--     ∀ {f f' f'' f''' f''''} →
--     (⊗-assoc⁻4 {A = A}{B = B}{C = C}{D = D}{E = E} ∘g (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''')
--     ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f'''' ∘g (⊗-assoc⁻4 {A = F}{B = G}{C = H}{D = K}{E = L}))
--   ⊗-assoc⁻4⊗-intro = {!!} -- refl

--   @0 ⊗-assoc4⊗-intro :
--     ⊗-assoc4 ∘g f ,⊗ f' ,⊗ f'' ,⊗ f''' ,⊗ f''''
--     ≡ (f ,⊗ f' ,⊗ f'' ,⊗ f''') ,⊗ f'''' ∘g ⊗-assoc4
--   ⊗-assoc4⊗-intro {f = f}{f' = f'}{f'' = f''}{f''' = f'''}{f'''' = f''''} =
--     {!!}
