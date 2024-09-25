open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Helper
open import Grammar Alphabet
open import Term Alphabet

private
  variable ℓG ℓG' ℓ ℓ' : Level

module _ where
  data Endofunctor ℓ : Type (ℓ-suc ℓ) where
    k : Grammar ℓ → Endofunctor ℓ
    Var : Endofunctor ℓ -- identity
    &e ⊕e : ∀ (X : Type ℓ) → (X → Endofunctor ℓ) → Endofunctor ℓ
    ⊗e : Endofunctor ℓ → Endofunctor ℓ → Endofunctor ℓ

  ⟦_⟧ : Endofunctor ℓ → Grammar ℓ → Grammar ℓ
  ⟦ k x ⟧ g = x
  ⟦ Var ⟧ g = g
  ⟦ &e X F_x ⟧ g = LinΠ[ x ∈ X ] (⟦ F_x x ⟧ g)
  ⟦ ⊕e X F_x ⟧ g = LinΣ[ x ∈ X ] (⟦ F_x x ⟧ g)
  ⟦ ⊗e F F' ⟧ g = ⟦ F ⟧ g ⊗ ⟦ F' ⟧ g

  map : ∀ (F : Endofunctor ℓ) {g h} → g ⊢ h → ⟦ F ⟧ g ⊢ ⟦ F ⟧ h
  map (k x) f    = id
  map Var f      = f
  map (&e X Fx) f = LinΠ-intro λ x → map (Fx x) f ∘g LinΠ-app x
  map (⊕e X Fx) f = LinΣ-elim (λ x → LinΣ-intro x ∘g map (Fx x) f)
  map (⊗e F G) f = map F f ,⊗ map G f

  map-id : ∀ (F : Endofunctor ℓ) {g} → map F (id {g = g}) ≡ id
  map-id (k h) i w x = x
  map-id Var i w x = x
  map-id (&e A F) i w x a = map-id (F a) i w (x a)
  map-id (⊕e A F) i w (a , x) = a , (map-id (F a) i w x)
  map-id (⊗e F F') i w (sp , x , x') = sp , map-id F i _ x , map-id F' i _ x'

  map-∘ :  ∀ (F : Endofunctor ℓ) {g h k} (f : h ⊢ k)(f' : g ⊢ h)
    → map F (f ∘g f') ≡ map F f ∘g map F f'
  map-∘ (k g') f f' i w x = x
  map-∘ Var f f' i w x = f w (f' w x)
  map-∘ (&e A F) f f' i w  x   a  = map-∘ (F a) f f' i w (x a)
  map-∘ (⊕e A F) f f' i w (a , x) = a , map-∘ (F a) f f' i w x
  map-∘ (⊗e F F') f f' i w (sp , x , x') = sp , map-∘ F f f' i _ x , map-∘ F' f f' i _ x'
  data μ (F : Endofunctor ℓ) : Grammar ℓ where
    roll : ⟦ F ⟧ (μ F) ⊢ μ F
  module _ (F : Endofunctor ℓ) where
    Algebra : Grammar ℓ → Type _
    Algebra X = ⟦ F ⟧ X ⊢ X

    initialAlgebra : Algebra (μ F)
    initialAlgebra = roll

    Homomorphism : ∀ {g h} → Algebra g → Algebra h → Type _
    Homomorphism {g = g}{h = h} ϕ ψ = Σ[ f ∈ g ⊢ h ]
      f ∘g ϕ ≡ ψ ∘g map F f

    idHomo : ∀ {g} → (ϕ : Algebra g) → Homomorphism ϕ ϕ
    idHomo ϕ = id , λ i → ϕ ∘g map-id F (~ i)

    compHomo : ∀ {g h k} (ϕ : Algebra g)(ψ : Algebra h)(χ : Algebra k)
      → Homomorphism ψ χ → Homomorphism ϕ ψ
      → Homomorphism ϕ χ
    compHomo ϕ ψ χ α β = (α .fst ∘g β .fst) ,
      ( (λ i → α .fst ∘g β .snd i)
      ∙ (λ i → α .snd i ∘g map F (β .fst))
      ∙ (λ i → χ ∘g map-∘ F (α .fst) (β .fst) (~ i)))

  {-# TERMINATING #-}
  rec : ∀ {F : Endofunctor ℓ}{X} → Algebra F X → μ F ⊢ X
  rec {F = F} alg w (roll _ x) = alg w (map F (rec alg) w x)

  μ-β : ∀ {F : Endofunctor ℓ}{X} → (alg : Algebra F X) → rec {F = F} alg ∘g roll ≡ alg ∘g map F (rec {F = F} alg)
  μ-β alg = refl


  module _ {F : Endofunctor ℓ}{X} (alg : Algebra F X) (ϕ : Homomorphism F (initialAlgebra F) alg) where
    private
      {-# TERMINATING #-}
      μ-η' : ∀ w x → ϕ .fst w x ≡ rec alg w x
      μ-η' w (roll _ x) = funExt⁻ (funExt⁻ (ϕ .snd) _) x
        ∙ cong (alg _) (funExt⁻ (funExt⁻ (cong (map F) (funExt λ _ → funExt (μ-η' _))) w) x)

    μ-η : ϕ .fst ≡ rec alg
    μ-η = funExt λ w → funExt (μ-η' w)
    
  μ-ind : ∀ {F : Endofunctor ℓ}{X} (alg : Algebra F X) (ϕ ϕ' : Homomorphism F (initialAlgebra F) alg)
    → ϕ .fst ≡ ϕ' .fst
  μ-ind α ϕ ϕ' = μ-η α ϕ ∙ sym (μ-η α ϕ')

  μ-ind-id : ∀ {F : Endofunctor ℓ} (ϕ : Homomorphism F (initialAlgebra F) (initialAlgebra F))
    → ϕ .fst ≡ id
  μ-ind-id {F = F} ϕ = μ-ind (initialAlgebra F) ϕ (idHomo F (initialAlgebra F))

open import Cubical.Data.Bool
module _ (g : Grammar ℓ-zero) where
  -- TODO define sugar for binary sum via Σ[ bool ]
  *endo : Endofunctor ℓ-zero
  *endo = ⊕e Bool (λ { false → k ε ; true → ⊗e (k g) Var})

  * : Grammar ℓ-zero
  * = μ *endo

  open *r-Algebra
  KLalg : *r-Algebra g
  KLalg .the-ℓ = ℓ-zero
  KLalg .G = *
  KLalg .nil-case = roll ∘g LinΣ-intro false
  KLalg .cons-case = roll ∘g LinΣ-intro true

  KL*→* : KL* g ⊢ *
  KL*→* = foldKL*r g KLalg

  *alg : Algebra *endo (KL* g)
  *alg w (false , x) = nil w x
  *alg w (true , x) = cons w x

  *→KL* : * ⊢ KL* g
  *→KL* = rec *alg

  open import Grammar.Equivalence Alphabet
  open StrongEquivalence
  *≅KL* : StrongEquivalence * (KL* g)
  *≅KL* .fun = *→KL*
  *≅KL* .inv = KL*→*
  *≅KL* .sec =
    !*r-AlgebraHom' g (*r-initial g)
      (record {
        f = *→KL* ∘g KL*→*
      ; on-nil = refl
      ; on-cons = refl })
      (id*r-AlgebraHom g (*r-initial g))
  *≅KL* .ret =
    μ-ind-id
      (KL*→* ∘g *→KL* ,
      funExt (λ w → funExt λ {
        (false , x) → refl
      ; (true , x) → refl }))
