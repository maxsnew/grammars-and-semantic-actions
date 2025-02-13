open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

module Grammar.LinearProduct.SplittingTrichotomy (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List as List hiding (rec)
open import Cubical.Data.List.Properties
open import Cubical.Data.List.More
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.MoreMore
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Sum.More
open import Cubical.Data.FinSet
open import Cubical.Data.Nat
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥* ; rec)

open import Cubical.Relation.Nullary.Base

open import Grammar.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Properties Alphabet
open import Grammar.HLevels Alphabet hiding (⟨_⟩)
open import Grammar.HLevels.Properties Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Dependent.Properties Alphabet
open import Grammar.Dependent.Unambiguous Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Epsilon.Properties Alphabet
open import Grammar.Top Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Lift.Properties Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.KleeneStar.Properties Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.String.Properties Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)
open import Grammar.Inductive.Properties Alphabet

open import Term.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh ℓk ℓl : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

{--
-- Building some axioms for splitting a ⊗ across a &
--
-- That is, the grammar (g ⊗ h) & (k ⊗ l)
-- should break into a trichotomy that reasons if
-- the splitting is the same across the tensors,
-- if the first splitting forms a prefix of the second,
-- of symmetrically if the second forms a prefix of the first
--
--
--   |    g     |         h          |
-- w ---------------------------------
--   |    k     |         l          |
--
--
--   |    g     |         h          |
-- w ---------------------------------
--   |  k  |           l             |
--
--
--   |  g  |           h             |
-- w ---------------------------------
--   |    k     |         l          |
--
--}
module _
  (g : Grammar ℓg)
  (h : Grammar ℓh)
  (k : Grammar ℓk)
  (l : Grammar ℓl)
  where

  sameSplittingG : Grammar (ℓ-max (ℓ-max (ℓ-max ℓg ℓh) ℓk) ℓl)
  sameSplittingG = (g & k) ⊗ (h & l)

  firstPrefixG : Grammar (ℓ-max (ℓ-max (ℓ-max ℓg ℓh) ℓk) ℓl)
  firstPrefixG =
    ⊕[ w ∈ String ]
    ⊕[ x ∈ String ]
    ⊕[ y ∈ String ]
    ⊕[ z ∈ String ]
    ⊕[ v ∈ NonEmptyString ]
      (
      ((g & ⌈ w ⌉) & (⌈ y ⌉ ⊗ ⌈ v .fst ⌉) ⊗ (h & ⌈ x ⌉))
      &
      ((k & ⌈ y ⌉) ⊗ ((l & ⌈ z ⌉) & (⌈ v .fst ⌉ ⊗ ⌈ x ⌉)))
      )

  secondPrefixG : Grammar (ℓ-max (ℓ-max (ℓ-max ℓg ℓh) ℓk) ℓl)
  secondPrefixG =
    ⊕[ w ∈ String ]
    ⊕[ x ∈ String ]
    ⊕[ y ∈ String ]
    ⊕[ z ∈ String ]
    ⊕[ v ∈ NonEmptyString ]
      (
      ((k & ⌈ y ⌉) & (⌈ w ⌉ ⊗ ⌈ v .fst ⌉) ⊗ (l & ⌈ z ⌉))
      &
      ((g & ⌈ w ⌉) ⊗ ((h & ⌈ x ⌉) & (⌈ v .fst ⌉ ⊗ ⌈ z ⌉)))
      )

  splittingTrichotomyG : Grammar (ℓ-max (ℓ-max (ℓ-max ℓg ℓh) ℓk) ℓl)
  splittingTrichotomyG = sameSplittingG ⊕ (secondPrefixG ⊕ firstPrefixG)

  module _ (w : String) (s s' : Splitting w) where
    splittingTrichotomyGTy : splittingTrichotomyTy' w s s' → Type _
    splittingTrichotomyGTy (inl x) =
      (g & k) (s .fst .fst) × (h & l) (s .fst .snd)
    splittingTrichotomyGTy (inr (inl (([] , notmt) , x))) = Empty.⊥*
    splittingTrichotomyGTy (inr (inl ((c ∷ v , notmt) , x))) =
      g (s .fst .fst) ×
      h (s .fst .snd) ×
      k (s' .fst .fst) ×
      l (s' .fst .snd) ×
      (s .fst .fst ++ c ∷ v ≡ s' .fst .fst) ×
      (s .fst .snd ≡ c ∷ v ++ s' .fst .snd)
    splittingTrichotomyGTy (inr (inr (([] , notmt) , x))) = Empty.⊥*
    splittingTrichotomyGTy (inr (inr ((c ∷ v , notmt) , x))) =
      g (s .fst .fst) ×
      h (s .fst .snd) ×
      k (s' .fst .fst) ×
      l (s' .fst .snd) ×
      (s' .fst .fst ++ c ∷ v ≡ s .fst .fst ) ×
      (s' .fst .snd ≡ c ∷ v ++ s . fst .snd)

    open Iso
    opaque
      unfolding ⊗-intro _&_ has-split
      toTrichotomyIso :
        ∀ (st : splittingTrichotomyTy' w s s') →
        Iso
          (g (s .fst .fst) ×
           h (s .fst .snd) ×
           k (s' .fst .fst) ×
           l (s' .fst .snd))
          (splittingTrichotomyGTy st)
      toTrichotomyIso (inl x) .fun y =
        (y .fst  , subst k (sym (x .fst)) (y .snd .snd .fst)) ,
        (y .snd .fst , subst l (sym (x .snd)) (y .snd .snd .snd))
      toTrichotomyIso (inl x) .inv y =
        (y .fst .fst) , ((y .snd .fst) ,
        ((subst k (x .fst) (y .fst .snd)) ,
        (subst l (x .snd) (y .snd .snd))))
      toTrichotomyIso (inl x) .rightInv y =
        ≡-× (≡-× refl (subst⁻Subst k (x .fst) (y .fst .snd)))
            (≡-× refl (subst⁻Subst l (x .snd) (y .snd .snd)))
      toTrichotomyIso (inl x) .leftInv y =
        ≡-× refl (≡-× refl
          (≡-×
            (substSubst⁻ k (x .fst) (y .snd .snd .fst))
            (substSubst⁻ l (x .snd) (y .snd .snd .snd))))
      toTrichotomyIso (inr (inl (([] , notmt) , st))) =
        Empty.rec (notmt refl)
      toTrichotomyIso (inr (inl ((c ∷ v , _) , st))) .fun y =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd ,
        st .fst ,
        st .snd
      toTrichotomyIso (inr (inl ((c ∷ v , _) , st))) .inv y =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd .fst
      toTrichotomyIso (inr (inl ((c ∷ v , _) , st))) .rightInv y i =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd .fst ,
        isSetString _ _ (st .fst) (y .snd .snd .snd .snd .fst) i ,
        isSetString _ _ (st .snd) (y .snd .snd .snd .snd .snd) i
      toTrichotomyIso (inr (inl ((c ∷ v , _) , st))) .leftInv y = refl
      toTrichotomyIso (inr (inr (([] , notmt) , st))) =
        Empty.rec (notmt refl)
      toTrichotomyIso (inr (inr ((c ∷ v , _) , st))) .fun y =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd ,
        st .fst ,
        st .snd
      toTrichotomyIso (inr (inr ((c ∷ v , _) , st))) .inv y =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd .fst
      toTrichotomyIso (inr (inr ((c ∷ v , _) , st))) .rightInv y i =
        y .fst ,
        y .snd .fst ,
        y .snd .snd .fst ,
        y .snd .snd .snd .fst ,
        isSetString _ _ (st .fst) (y .snd .snd .snd .snd .fst) i ,
        isSetString _ _ (st .snd) (y .snd .snd .snd .snd .snd) i
      toTrichotomyIso (inr (inr ((c ∷ v , _) , st))) .leftInv y = refl

  open Iso
  opaque
    unfolding toTrichotomyIso ⊗-intro _&_ mk&⌈⌉
    toTrichotomyIso' :
      (w : String) →
      Iso
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
          (g (s .fst .fst) ×
           h (s .fst .snd) ×
           k (s' .fst .fst) ×
           l (s' .fst .snd)))
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
           splittingTrichotomyGTy w s s' (splittingTrichotomy' w s s')
         )
    toTrichotomyIso' w .fun (s , s' , p) =
      s , (s' , toTrichotomyIso w s s' (splittingTrichotomy' w s s') .fun p)
    toTrichotomyIso' w .inv (s , s' , p) =
     s , (s' , (toTrichotomyIso w s s' (splittingTrichotomy' w s s') .inv p))
    toTrichotomyIso' w .rightInv (s , s' , p) =
      ΣPathP (refl , (ΣPathP (refl ,
        toTrichotomyIso w s s' (splittingTrichotomy' w s s') .rightInv p
      )))
    toTrichotomyIso' w .leftInv (s , s' , p) =
      ΣPathP (refl , (ΣPathP (refl ,
        toTrichotomyIso w s s' (splittingTrichotomy' w s s') .leftInv p
      )))

    splittingTrichotomyGTy-inl≅ :
      (w : String) →
      Iso
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
         Σ[ x ∈ sameSplitting w s s' ]
           splittingTrichotomyGTy w s s' (inl x)
         )
        (sameSplittingG w)
    splittingTrichotomyGTy-inl≅ w .fun (s , s' , x , p) =
      s , ((p .fst) , (p .snd))
    splittingTrichotomyGTy-inl≅ w .inv (s , pgk , phl) =
      s , s , (refl , refl) , pgk , phl
    splittingTrichotomyGTy-inl≅ w .rightInv (s , pgk , phl) = refl
    splittingTrichotomyGTy-inl≅ w .leftInv (s , s' , x , p) =
      ΣPathP (refl , (ΣPathP ((Splitting≡ (≡-× (x .fst) (x .snd))) ,
        (ΣPathP ((ΣPathP (
          isProp→PathP (λ _ → isSetString _ _) refl (x .fst) ,
          isProp→PathP (λ _ → isSetString _ _) refl (x .snd)
          )) ,
          refl)))))

    splittingTrichotomyGTy-inr-inl≅ :
      (w : String) →
      Iso
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
         Σ[ x ∈ splittingPrefix w s' s ]
           splittingTrichotomyGTy w s s' (inr (inl x))
         )
        (secondPrefixG w)
    splittingTrichotomyGTy-inr-inl≅ ww .fun
      (s' , s , ((c ∷ v , notmt) , split++) , p) =
        s' .fst .fst , s' .fst .snd ,
        s .fst .fst , s .fst .snd ,
        ((c ∷ v , notmt)) ,
        (s , ((mk&⌈⌉ k (p .snd .snd .fst) ,
          (_ , (sym (split++ .fst))) , ((mk⌈⌉ (s' .fst .fst)) , (mk⌈⌉ (c ∷ v)))) ,
          mk&⌈⌉ l (p .snd .snd .snd .fst))) ,
        s' , ((mk&⌈⌉ g(p .fst)) ,
          ((mk&⌈⌉ h (p .snd .fst)) ,
          ((_ , split++ .snd) , ((mk⌈⌉ (c ∷ v)) , (mk⌈⌉ (s .fst .snd))))))
    splittingTrichotomyGTy-inr-inl≅ ww .inv
      (w , x , y , z , ([] , notmt) ,
      (s , (pg , (t , py , pv)) , ph) ,
      (s' , pk , (pl , (t' , pv' , px)))
      ) =
      Empty.rec (notmt refl)
    splittingTrichotomyGTy-inr-inl≅ ww .inv
      (w , x , y , z , (c ∷ v , notmt) ,
      (s' , (pk , (t , pw , pv)) , pl) ,
      (s , pg , (ph , (t' , pv' , pz)))
      ) =
      s , s' ,
      ((c ∷ v , notmt) ,
        s'11≡ ,
        s12≡) ,
      pg .fst ,
      ph .fst ,
      pk .fst ,
      pl .fst ,
      s'11≡ ,
      s12≡
      where
      s11≡t11 : s .fst .fst ≡ t .fst .fst
      s11≡t11 =
        sym (⌈⌉→≡ w (s .fst .fst) (pg .snd))
        ∙ (⌈⌉→≡ w (t .fst .fst) pw)

      cv≡t12 : c ∷ v ≡ t .fst .snd
      cv≡t12 = ⌈⌉→≡ (c ∷ v) (t .fst .snd) pv

      s'11≡ : s .fst .fst ++ c ∷ v ≡ s' .fst .fst
      s'11≡ = cong₂ _++_ s11≡t11 cv≡t12 ∙ sym (t .snd)

      s12≡ : s .fst .snd ≡ c ∷ v ++ s' .fst .snd
      s12≡ =
        t' .snd
        ∙ cong₂ _++_
          (sym (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv'))
          (sym (⌈⌉→≡ z (t' .fst .snd) pz)
            ∙ (⌈⌉→≡ z (s' .fst .snd) (pl .snd)))
    splittingTrichotomyGTy-inr-inl≅ ww .rightInv
      (w , x , y , z , ([] , notmt) ,
      (s , (pk , (t , pw , pv)) , pl) ,
      (s' , pg , (ph , (t' , pv' , pz)))) =
      Empty.rec (notmt refl)
    splittingTrichotomyGTy-inr-inl≅ ww .rightInv
      (w , x , y , z , (c ∷ v , notmt) ,
      (s , (pk , (t , pw , pv)) , pl) ,
      (s' , pg , (ph , (t' , pv' , pz)))) =
      ΣPathP5 (
        sym (⌈⌉→≡ _ _ (pg .snd)) ,
        sym (⌈⌉→≡ _ _ (ph .snd)) ,
        sym (⌈⌉→≡ _ _ (pk .snd)) ,
        sym (⌈⌉→≡ _ _ (pl .snd)) ,
        refl ,
        ΣPathP5 (
          ΣPathP2 (
            refl ,
            ΣPathP3 (
              ΣPathPProp (λ _ → isLang⌈⌉ y (s .fst .fst)) refl ,
              Splitting≡
                (≡-×
                  (sym (⌈⌉→≡ w (s' .fst .fst) (pg .snd)) ∙ ⌈⌉→≡ w (t .fst .fst) pw)
                  (⌈⌉→≡ _ _ pv)
                ) ,
              isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (⌈⌉→≡ w (s' .fst .fst) (pg .snd) (~ i) )
                  (Splitting≡ {s = _ , sym s11≡} {s' = t}
                    (≡-×
                     ((λ i₁ → ⌈⌉→≡ w (s' .fst .fst) (pg .snd) (~ i₁)) ∙
                      ⌈⌉→≡ w (t .fst .fst) pw)
                     (⌈⌉→≡ (c ∷ v) (t .fst .snd) pv))
                    i .fst .fst)
                  )
                (mk⌈⌉ (s' .fst .fst))
                pw ,
              isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (c ∷ v)
                  (Splitting≡ {s = _ , sym s11≡} {s' = t}
                    (≡-×
                     ((λ i₁ → ⌈⌉→≡ w (s' .fst .fst) (pg .snd) (~ i₁)) ∙
                      ⌈⌉→≡ w (t .fst .fst) pw)
                     (⌈⌉→≡ (c ∷ v) (t .fst .snd) pv))
                    i .fst .snd)
                  )
                (mk⌈⌉ (c ∷ v))
                pv
              ) ,
            ΣPathPProp (λ _ → isLang⌈⌉ z (s .fst .snd)) refl
            ) ,
          refl ,
          ΣPathPProp (λ _ → isLang⌈⌉ w (s' .fst .fst)) refl ,
          ΣPathPProp (λ _ → isLang⌈⌉ x (s' .fst .snd)) refl ,
          Splitting≡
            (≡-×
              (⌈⌉→≡ _ _ pv')
              (sym (⌈⌉→≡ z _ (pl .snd)) ∙ ⌈⌉→≡ z _ pz)
            ) ,
          ΣPathP (
            isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (c ∷ v)
                  (Splitting≡ {s = _ , s'12≡} {s' = t'}
                   (≡-× (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv')
                    ((λ i₁ → ⌈⌉→≡ z (s .fst .snd) (pl .snd) (~ i₁)) ∙
                     ⌈⌉→≡ z (t' .fst .snd) pz))
                   i .fst .fst)
                )
                (mk⌈⌉ (c ∷ v))
                pv' ,
            isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (⌈⌉→≡ z (s .fst .snd) (pl .snd) (~ i))
                  (Splitting≡ {s = _ , s'12≡} {s' = t'}
                   (≡-× (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv')
                    ((λ i₁ → ⌈⌉→≡ z (s .fst .snd) (pl .snd) (~ i₁)) ∙
                     ⌈⌉→≡ z (t' .fst .snd) pz))
                   i .fst .snd)
                )
                (mk⌈⌉ (s .fst .snd))
                pz

          ))
        )
      where
      s'11≡t11 : s' .fst .fst ≡ t .fst .fst
      s'11≡t11 =
        sym (⌈⌉→≡ w (s' .fst .fst) (pg .snd))
        ∙ (⌈⌉→≡ w (t .fst .fst) pw)

      cv≡t12 : c ∷ v ≡ t .fst .snd
      cv≡t12 = ⌈⌉→≡ (c ∷ v) (t .fst .snd) pv

      s11≡ : s' .fst .fst ++ c ∷ v ≡ s .fst .fst
      s11≡ = cong₂ _++_ s'11≡t11 cv≡t12 ∙ sym (t .snd)

      s'12≡ : s' .fst .snd ≡ c ∷ v ++ s .fst .snd
      s'12≡ =
        t' .snd
        ∙ cong₂ _++_
          (sym (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv'))
          (sym (⌈⌉→≡ z (t' .fst .snd) pz)
            ∙ (⌈⌉→≡ z (s .fst .snd) (pl .snd)))
    splittingTrichotomyGTy-inr-inl≅ ww .leftInv
      (s , s' , ((c ∷ v , notmt) , split++) , p) =
      ΣPathP3 (
        refl ,
        refl ,
        ΣPathP2 (
          refl ,
          isSetString _ _ _ _ ,
          isSetString _ _ _ _
        ) ,
        ΣPathP5 (
          refl ,
          refl ,
          refl ,
          refl ,
          isSetString _ _ _ _ ,
          isSetString _ _ _ _
        )
      )

    splittingTrichotomyGTy-inr-inr≅ :
      (w : String) →
      Iso
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
         Σ[ x ∈ splittingPrefix w s s' ]
           splittingTrichotomyGTy w s s' (inr (inr x))
         )
        (firstPrefixG w)
    splittingTrichotomyGTy-inr-inr≅ ww .fun
      (s' , s , ((c ∷ v , notmt) , split++) , p) =
      s' .fst .fst , s' .fst .snd ,
      s .fst .fst , s .fst .snd ,
      ((c ∷ v , notmt)) ,
      (s' , ((mk&⌈⌉ g (p .fst) ,
        (_ , (sym (split++ .fst))) , ((mk⌈⌉ (s .fst .fst)) , (mk⌈⌉ (c ∷ v)))) ,
        mk&⌈⌉ h (p .snd .fst))) ,
      (s , ((mk&⌈⌉ k (p .snd .snd .fst)) ,
        ((mk&⌈⌉ l (p .snd .snd .snd .fst)) ,
        ((_ , split++ .snd) , ((mk⌈⌉ (c ∷ v)) , (mk⌈⌉ (s' .fst .snd)))))))
    splittingTrichotomyGTy-inr-inr≅ ww .inv
      (w , x , y , z , ([] , notmt) ,
      (s , (pg , (t , py , pv)) , ph) ,
      (s' , pk , (pl , (t' , pv' , px)))
      ) =
      Empty.rec (notmt refl)
    splittingTrichotomyGTy-inr-inr≅ ww .inv
      (w , x , y , z , (c ∷ v , notmt) ,
      (s' , (pg , (t , py , pv)) , ph) ,
      (s , pk , (pl , (t' , pv' , px)))
      ) =
      s' ,
      s ,
      ((c ∷ v , notmt) ,
        s'11≡ ,
        s12≡) ,
      pg .fst ,
      ph .fst ,
      pk .fst ,
      pl .fst ,
      s'11≡ ,
      s12≡
      where
      s11≡t11 : s .fst .fst ≡ t .fst .fst
      s11≡t11 =
        sym (⌈⌉→≡ y (s .fst .fst) (pk .snd))
        ∙ (⌈⌉→≡ y (t .fst .fst) py)

      cv≡t12 : c ∷ v ≡ t .fst .snd
      cv≡t12 = ⌈⌉→≡ (c ∷ v) (t .fst .snd) pv

      s'11≡ : s .fst .fst ++ c ∷ v ≡ s' .fst .fst
      s'11≡ = cong₂ _++_ s11≡t11 cv≡t12 ∙ sym (t .snd)

      s12≡ : s .fst .snd ≡ c ∷ v ++ s' .fst .snd
      s12≡ =
        t' .snd
        ∙ cong₂ _++_
          (sym (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv'))
          (sym (⌈⌉→≡ x (t' .fst .snd) px)
            ∙ (⌈⌉→≡ x (s' .fst .snd) (ph .snd)))
    splittingTrichotomyGTy-inr-inr≅ ww .rightInv
      (w , x , y , z , ([] , notmt) ,
      (s , (pk , (t , pw , pv)) , pl) ,
      (s' , pg , (ph , (t' , pv' , pz)))) =
      Empty.rec (notmt refl)
    splittingTrichotomyGTy-inr-inr≅ ww .rightInv
      (w , x , y , z , (c ∷ v , notmt) ,
      (s , (pg , (t , py , pv)) , ph) ,
      (s' , pk , (pl , (t' , pv' , px)))) =
      ΣPathP5 (
        sym (⌈⌉→≡ _ _ (pg .snd)) ,
        sym (⌈⌉→≡ _ _ (ph .snd)) ,
        sym (⌈⌉→≡ _ _ (pk .snd)) ,
        sym (⌈⌉→≡ _ _ (pl .snd)) ,
        refl ,
        ΣPathP5 (
          ΣPathP2 (
            refl ,
            ΣPathP3 (
              ΣPathPProp (λ _ → isLang⌈⌉ w (s .fst .fst)) refl ,
              Splitting≡
                (≡-×
                  (sym (⌈⌉→≡ y (s' .fst .fst) (pk .snd))
                    ∙ ⌈⌉→≡ y (t .fst .fst) py)
                  (⌈⌉→≡ _ _ pv)
                ) ,
              isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (⌈⌉→≡ y (s' .fst .fst) (pk .snd) (~ i) )
                  (Splitting≡ {s = _ , sym s11≡} {s' = t}
                    (≡-×
                     ((λ i₁ → ⌈⌉→≡ y (s' .fst .fst) (pk .snd) (~ i₁)) ∙
                      ⌈⌉→≡ y (t .fst .fst) py)
                     (⌈⌉→≡ (c ∷ v) (t .fst .snd) pv))
                    i .fst .fst)
                  )
                (mk⌈⌉ (s' .fst .fst))
                py ,
              isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (c ∷ v)
                  (Splitting≡ {s = _ , sym s11≡} {s' = t}
                    (≡-×
                     ((λ i₁ → ⌈⌉→≡ y (s' .fst .fst) (pk .snd) (~ i₁)) ∙
                      ⌈⌉→≡ y (t .fst .fst) py)
                     (⌈⌉→≡ (c ∷ v) (t .fst .snd) pv))
                    i .fst .snd)
                  )
                (mk⌈⌉ (c ∷ v))
                pv
              ) ,
            ΣPathPProp (λ _ → isLang⌈⌉ x (s .fst .snd)) refl
            ) ,
          refl ,
          ΣPathPProp (λ _ → isLang⌈⌉ y (s' .fst .fst)) refl ,
          ΣPathPProp (λ _ → isLang⌈⌉ z (s' .fst .snd)) refl ,
          Splitting≡
            (≡-×
              (⌈⌉→≡ _ _ pv')
              (sym (⌈⌉→≡ x _ (ph .snd)) ∙ ⌈⌉→≡ x _ px)
            ) ,
          ΣPathP (
            isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (c ∷ v)
                  (Splitting≡ {s = _ , s'12≡} {s' = t'}
                   (≡-× (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv')
                    ((λ i₁ → ⌈⌉→≡ x (s .fst .snd) (ph .snd) (~ i₁)) ∙
                     ⌈⌉→≡ x (t' .fst .snd) px))
                   i .fst .fst)
                )
                (mk⌈⌉ (c ∷ v))
                pv' ,
            isProp→PathP
                (λ i →
                  isLang⌈⌉
                  (⌈⌉→≡ x (s .fst .snd) (ph .snd) (~ i))
                  (Splitting≡ {s = _ , s'12≡} {s' = t'}
                   (≡-× (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv')
                    ((λ i₁ → ⌈⌉→≡ x (s .fst .snd) (ph .snd) (~ i₁)) ∙
                     ⌈⌉→≡ x (t' .fst .snd) px))
                   i .fst .snd)
                )
                (mk⌈⌉ (s .fst .snd))
                px
          ))
        )
      where
      s'11≡t11 : s' .fst .fst ≡ t .fst .fst
      s'11≡t11 =
        sym (⌈⌉→≡ y (s' .fst .fst) (pk .snd))
        ∙ (⌈⌉→≡ y (t .fst .fst) py)

      cv≡t12 : c ∷ v ≡ t .fst .snd
      cv≡t12 = ⌈⌉→≡ (c ∷ v) (t .fst .snd) pv

      s11≡ : s' .fst .fst ++ c ∷ v ≡ s .fst .fst
      s11≡ = cong₂ _++_ s'11≡t11 cv≡t12 ∙ sym (t .snd)

      s'12≡ : s' .fst .snd ≡ c ∷ v ++ s .fst .snd
      s'12≡ =
        t' .snd
        ∙ cong₂ _++_
          (sym (⌈⌉→≡ (c ∷ v) (t' .fst .fst) pv'))
          (sym (⌈⌉→≡ x (t' .fst .snd) px)
            ∙ (⌈⌉→≡ x (s .fst .snd) (ph .snd)))
    splittingTrichotomyGTy-inr-inr≅ ww .leftInv
      (s , s' , ((c ∷ v , notmt) , split++) , p) =
      ΣPathP3 (
        refl ,
        refl ,
        ΣPathP2 (
          refl ,
          isSetString _ _ _ _ ,
          isSetString _ _ _ _
        ) ,
        ΣPathP5 (
          refl ,
          refl ,
          refl ,
          refl ,
          isSetString _ _ _ _ ,
          isSetString _ _ _ _
        )
      )

    splittingTrichotomyGTyΣ≅ :
      (w : String) →
      Iso
        (
        Σ[ s ∈ Splitting w ]
        Σ[ s' ∈ Splitting w ]
        Σ[ x ∈ splittingTrichotomyTy' w s s' ]
           splittingTrichotomyGTy w s s' x
         )
        (
        sameSplittingG w ⊎
        (secondPrefixG w ⊎ firstPrefixG w)
        )
    splittingTrichotomyGTyΣ≅ w =
      compIso
        (invIso Σ-assoc-Iso)
        (compIso
          (Σ-cong-iso-snd (λ _ →
            Σ⊎Iso
          ))
          (compIso
            (ΣDistR⊎Iso _ _ _)
            (⊎Iso
              (compIso Σ-assoc-Iso (splittingTrichotomyGTy-inl≅ w))
              (compIso
                (Σ-cong-iso-snd (λ _ →
                  Σ⊎Iso
                ))
                (compIso
                  (ΣDistR⊎Iso _ _ _)
                  (⊎Iso
                    (compIso Σ-assoc-Iso (splittingTrichotomyGTy-inr-inl≅ w))
                    (compIso Σ-assoc-Iso (splittingTrichotomyGTy-inr-inr≅ w))
                  )
                )
              )
            )
          )
        )

    ⊗&⊗parse≅ :
      (w : String) →
      Iso
        (((g ⊗ h) & (k ⊗ l)) w)
        (Σ[ s ∈ Splitting w ]
         Σ[ s' ∈ Splitting w ]
          (g (s .fst .fst) ×
           h (s .fst .snd) ×
           k (s' .fst .fst) ×
           l (s' .fst .snd)))
    ⊗&⊗parse≅ w .fun ((s , pg , ph) , (s' , pk , pl)) =
      s , s' , pg , ph , pk , pl
    ⊗&⊗parse≅ w .inv (s , s' , pg , ph , pk , pl) =
      (s , pg , ph) , (s' , pk , pl)
    ⊗&⊗parse≅ w .rightInv _ = refl
    ⊗&⊗parse≅ w .leftInv _ = refl

    opaque
      unfolding _⊕_
      splittingTrichotomy≅ :
        (g ⊗ h) & (k ⊗ l)
        ≅
        splittingTrichotomyG
      splittingTrichotomy≅ = pointwiseIso→≅ _ _
        (λ w →
          compIso
            (compIso
              (⊗&⊗parse≅ w)
              (compIso
                (toTrichotomyIso' w)
                (compIso
                  (invIso Σ-assoc-Iso)
                  (compIso
                    (Σ-cong-iso-snd (λ (s , s') →
                      invIso (Σ-contractFstIso
                        ((splittingTrichotomy' w s s') ,
                        (isPropSplittingTrichotomyTy' w s s' _)))
                    ))
                    Σ-assoc-Iso
                  ))
              ))
            (splittingTrichotomyGTyΣ≅ w)
        )

  ⊗&-split :
    (g ⊗ h) & (k ⊗ l)
    ≅
    ((g & k) ⊗ (h & l)) ⊕
    (
    (
      ⊕[ w ∈ String ]
      ⊕[ x ∈ String ]
      ⊕[ y ∈ String ]
      ⊕[ z ∈ String ]
      ⊕[ v ∈ NonEmptyString ]
        (
        ((k & ⌈ y ⌉) & (⌈ w ⌉ ⊗ ⌈ v .fst ⌉) ⊗ (l & ⌈ z ⌉))
        &
        ((g & ⌈ w ⌉) ⊗ ((h & ⌈ x ⌉) & (⌈ v .fst ⌉ ⊗ ⌈ z ⌉)))
        )
    )
    ⊕
    (
      ⊕[ w ∈ String ]
      ⊕[ x ∈ String ]
      ⊕[ y ∈ String ]
      ⊕[ z ∈ String ]
      ⊕[ v ∈ NonEmptyString ]
        (
        ((g & ⌈ w ⌉) & (⌈ y ⌉ ⊗ ⌈ v .fst ⌉) ⊗ (h & ⌈ x ⌉))
        &
        ((k & ⌈ y ⌉) ⊗ ((l & ⌈ z ⌉) & (⌈ v .fst ⌉ ⊗ ⌈ x ⌉)))
        )

    )
    )
  ⊗&-split = splittingTrichotomy≅

