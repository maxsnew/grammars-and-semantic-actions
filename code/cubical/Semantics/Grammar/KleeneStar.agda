open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.KleeneStar ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)

private
  variable
    ℓG ℓH : Level
    g : Grammar ℓG
    h : Grammar ℓH

module _ (g : Grammar ℓG) where
  data KL* : Grammar ℓG
    where
    nil : ε-grammar ⊢ KL*
    cons : g ⊗ KL* ⊢ KL*

  record *r-Algebra : Typeω where
    field
      the-ℓ : Level
      G : Grammar the-ℓ
      nil-case : ε-grammar ⊢ G
      cons-case : g ⊗ G ⊢ G

  record *l-Algebra : Typeω where
    field
      the-ℓ : Level
      G : Grammar the-ℓ
      nil-case : ε-grammar ⊢ G
      cons-case : G ⊗ g ⊢ G

  open *l-Algebra
  open *r-Algebra

  *r-initial : *r-Algebra
  *r-initial .the-ℓ = _
  *r-initial .G = KL*
  *r-initial .nil-case = nil
  *r-initial .cons-case = cons

  -- *l-initial : *l-Algebra
  -- *l-initial .the-ℓ = _
  -- *l-initial .G = KL*
  -- *l-initial .nil-case = nil
  -- *l-initial .cons-case = {!!}

  record *r-AlgebraHom (alg alg' : *r-Algebra) : Typeω where
    field
      f : alg .G ⊢ alg' .G
      on-nil : f ∘g alg .nil-case ≡ alg' .nil-case
      on-cons : f ∘g alg .cons-case ≡ alg' .cons-case ∘g ⊗-intro id f

  open *r-AlgebraHom

  module _ (the-alg : *r-Algebra) where
    id*r-AlgebraHom : *r-AlgebraHom the-alg the-alg
    id*r-AlgebraHom .f = id
    id*r-AlgebraHom .on-nil = refl
    id*r-AlgebraHom .on-cons = refl

    KL*-elim : KL* ⊢ the-alg .G
    KL*-elim _ (nil _ x) = the-alg .nil-case _ x
    KL*-elim _ (cons _ x) =
      the-alg .cons-case _
        ((x .fst) , ((x .snd .fst) , (KL*-elim _ (x .snd .snd))))

    foldKL*r = KL*-elim

    ∃*r-AlgebraHom : *r-AlgebraHom *r-initial the-alg
    ∃*r-AlgebraHom .f = KL*-elim
    ∃*r-AlgebraHom .on-nil = refl
    ∃*r-AlgebraHom .on-cons = refl

    !*r-AlgebraHom :
      (e : *r-AlgebraHom *r-initial the-alg) →
      ∀ w p →
      e .f w p ≡ KL*-elim w p
    !*r-AlgebraHom e _ (nil _ x) = funExt⁻ (funExt⁻ (e .on-nil) _) x
    !*r-AlgebraHom e _ (cons _ x) =
      funExt⁻ (funExt⁻ (e .on-cons) _) x ∙
      (λ i → the-alg .cons-case _
        (x .fst , x .snd .fst , !*r-AlgebraHom e _ (x .snd .snd) i))

    !*r-AlgebraHom' :
      (e e' : *r-AlgebraHom *r-initial the-alg) →
      e .f ≡ e' .f
    !*r-AlgebraHom' e e' = funExt λ w → funExt λ p →
      !*r-AlgebraHom e w p ∙ sym (!*r-AlgebraHom e' w p)



-- foldKL*l :
--   ε-grammar ⊢ g →
--   g ⊗ h ⊢ g →
--   KL* h ⊢ g
-- foldKL*l {g = g}{h = h} pε p⊗ =
--   seq {g = KL* h}{h = g -⊗ g}{k = g}
--     (foldKL*r {g = g -⊗ g}{h = h}
--       (-⊗-intro {g = g}{h = ε-grammar}{k = g} ⊗-unit-r)
--       (-⊗-intro {g = g}{h = h ⊗ (g -⊗ g)}{k = g}
--         (seq {h = (g ⊗ h) ⊗ (g -⊗ g)}
--           (⊗-assoc {g = g}{h = h}{k = g -⊗ g})
--           (seq {h = g ⊗ (g -⊗ g)}
--             (⊗-intro {g = g ⊗ h}{h = g}{k = g -⊗ g}{l = g -⊗ g} p⊗ (id {g = g -⊗ g}))
--             -⊗-app))))
--     (seq {g = g -⊗ g}{h = g ⊗ (g -⊗ g)}{k = g}
--       (seq {h = ε-grammar ⊗ (g -⊗ g)}
--         (⊗-unit-l⁻ {g = g -⊗ g})
--         (⊗-intro {g = ε-grammar}{h = g}{k = g -⊗ g}{l = g -⊗ g} pε (id {g = g -⊗ g})))
--       -⊗-app)



--   -- -- Use IW trees to prove that Kleene star forms a set
--   -- -- (provided that the original grammar outputs sets)
--   -- module isSetKL*TyProof
--   --   (hg : hGrammar)
--   --   where
--   --   g = hg .fst
--   --   setParses = hg .snd

--   --   KL*Ty-X = String

--   --   KL*Ty-S : KL*Ty-X → Type ℓ
--   --   KL*Ty-S w =
--   --     (w ≡ []) ⊎
--   --     (Σ[ s ∈ Splitting w ] g (s .fst .fst))

--   --   KL*Ty-P : ∀ w → KL*Ty-S w → Type ℓ-zero
--   --   KL*Ty-P w (inl x) = ⊥
--   --   KL*Ty-P w (inr x) = ⊤

--   --   KL*Ty-inX : ∀ w (s : KL*Ty-S w) → KL*Ty-P w s → KL*Ty-X
--   --   KL*Ty-inX w (inr (s , sp)) x = s .fst .snd

--   --   KL*Ty→W : ∀ {w} → KL*Ty g w → IW KL*Ty-S KL*Ty-P KL*Ty-inX w
--   --   KL*Ty→W (nil x) = node (inl x) λ ()
--   --   KL*Ty→W (cons x) =
--   --     node (inr ((x .fst) , (x .snd .fst)))
--   --       λ _ → KL*Ty→W (x .snd .snd)

--   --   W→KL*Ty : ∀ {w} → IW KL*Ty-S KL*Ty-P KL*Ty-inX w → KL*Ty g w
--   --   W→KL*Ty (node (inl x) subtree) = nil x
--   --   W→KL*Ty (node (inr x) subtree) =
--   --     cons ((x .fst) , ((x .snd) , (W→KL*Ty (subtree _))))

--   --   KL*TyRetractofW :
--   --     ∀ {w} (p : KL*Ty g w) →
--   --     W→KL*Ty (KL*Ty→W p) ≡ p
--   --   KL*TyRetractofW (nil x) = refl
--   --   KL*TyRetractofW (cons x) =
--   --     cong cons
--   --       (ΣPathP (refl ,
--   --         (ΣPathP (refl ,
--   --           (KL*TyRetractofW (x .snd .snd))))))


--   --   isSetKL*Ty-S : ∀ w → isSet (KL*Ty-S w)
--   --   isSetKL*Ty-S w =
--   --     isSet⊎
--   --       (isGroupoidString _ _)
--   --       (isSetΣ (isSetSplitting _) λ _ → setParses _)

--   --   isSetKL*Ty : ∀ w → isSet (KL*Ty g w)
--   --   isSetKL*Ty w =
--   --     isSetRetract
--   --       KL*Ty→W W→KL*Ty
--   --       KL*TyRetractofW
--   --       (isOfHLevelSuc-IW 1 isSetKL*Ty-S w)

--   -- open isSetKL*TyProof
--   -- KL* : Grammar → Grammar
--   -- KL* g w = KL*Ty g w

--   -- isHGrammar-KL* : (g : hGrammar) → isHGrammar (KL* (g .fst))
--   -- isHGrammar-KL* g _ = isSetKL*Ty g _
