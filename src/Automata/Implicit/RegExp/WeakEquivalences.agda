{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module Automata.Implicit.RegExp.WeakEquivalences (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.FinSet
open import Cubical.Data.Bool as Bool hiding (_⊕_)
open import Cubical.Data.Unit
open import Cubical.Data.Sum as Sum hiding (rec ; inl ; inr ; map)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Grammar Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Unambiguous Alphabet
open import Grammar.SequentialUnambiguity Alphabet
open import Automata.Implicit.RegExp Alphabet
  renaming ( ⊥Aut to ⊥AutR
           ; εAut to εAutR
           ; litAut to litAutR
           ; ⊕Aut to ⊕AutR
           ; ⊗Aut to ⊗AutR
           ; *Aut to *AutR
           )
open import Term Alphabet

open StrongEquivalence
open WeakEquivalence
open ImplicitDeterministicAutomaton

private
  variable
    ℓ ℓ' ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

-- TODO move to Grammar.Bottom
⊗⊥*-elim : ∀ {ℓ*} → A ⊗ ⊥* {ℓ*} ⊢ B
⊗⊥*-elim = ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ ⊥*-elim

⊥*⊗-elim : ∀ {ℓ*} → ⊥* {ℓ*} ⊗ A ⊢ B
⊥*⊗-elim = ⊥-elim ∘g ⊥⊗ ∘g ⊥*-elim ,⊗ id

-- TODO move elsewhere
decElim :
  ∀ {ℓP ℓR} {P : Type ℓP} {R : Dec P → Type ℓR} →
  ((p : P) → R (yes p)) → ((¬p : ¬ P) → R (no ¬p)) →
  (d : Dec P) → R d
decElim ifyes _    (yes p)  = ifyes p
decElim _    ifno  (no ¬p)  = ifno ¬p

module _
  (discAlpha : Discrete ⟨ Alphabet ⟩)
  where

  private
    ⊥Aut = ⊥AutR discAlpha
    εAut = εAutR discAlpha

  ⊥≈ : Parse ⊥Aut ≈ ⊥
  ⊥≈ = mkLogEq (rec _ ⊥Alg _) ⊥-elim
    where
    ⊥Alg : ParseAlg ⊥Aut λ { initial → ⊥ }
    ⊥Alg fail = ParseAlgFail ⊥Aut _
    ⊥Alg initial =
      ⊕ᴰ-elim λ where
        (stepᵢ c) →
          ⊗⊥*-elim
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  ε≈ : Parse εAut ≈ ε
  ε≈ = mkLogEq (rec _ εAlg _) (STOPᵢ εAut)
    where
    εAlg : ParseAlg εAut λ { initial → ε }
    εAlg fail = ParseAlgFail εAut _
    εAlg initial =
      ⊕ᴰ-elim λ where
        (stopᵢ Eq.refl) → lowerG ∘g lowerG
        (stepᵢ c) →
          ⊗⊥*-elim
          ∘g (lowerG ∘g lowerG) ,⊗ lowerG

  module _ (c : ⟨ Alphabet ⟩) where

    private
      litAut = litAutR discAlpha c

    lit≈ : Parse litAut ≈ ＂ c ＂
    lit≈ = mkLogEq (rec _ litAlg _) (toAut initial)
      where
      ⟦_⟧lit : FreelyAddInitial Unit → Grammar ℓ-zero
      ⟦ initial ⟧lit = ＂ c ＂
      ⟦ ↑i _ ⟧lit = ε

      litAlg : ParseAlg litAut ⟦_⟧lit
      litAlg fail = ParseAlgFail litAut _
      litAlg initial =
        ⊕ᴰ-elim λ where
          (stepᵢ c') →
            initialStep c'
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        initialStep :
          (c' : ⟨ Alphabet ⟩) →
          ＂ c' ＂ ⊗ ParseAlgCarrier litAut ⟦_⟧lit (↑f→q (litAut .δᵢ c')) ⊢ ＂ c ＂
        initialStep c' =
          decElim
            {R = λ x →
              ＂ c' ＂ ⊗
                  ParseAlgCarrier litAut ⟦_⟧lit
                    (↑f→q
                      (decRec
                        (λ _ → ↑f _)
                        (λ _ → fail)
                        x
                      )
                    )
                  ⊢ ＂ c ＂
            }
            (J (λ c'' c≡c'' → ＂ c'' ＂ ⊗ ε ⊢ ＂ c ＂) ⊗-unit-r)
            (λ _ → ⊗⊥*-elim)
            (discAlpha c c')

      litAlg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q Eq.refl) → lowerG ∘g lowerG
          (step .q c) → ⊥-elim ∘g ⊗⊥ ∘g id ,⊗ ⊥*-elim ∘g (lowerG ∘g lowerG) ,⊗ lowerG

      toAut : ∀ q → ParseAlgCarrier litAut ⟦_⟧lit q ⊢ Trace litAut true q
      toAut fail = ⊥*-elim
      toAut initial =
        STEPᵢ litAut c
        ∘g id ,⊗
          decElim
            {R =
              λ x →
              Trace litAut true (↑q _)
              ⊢
              Trace litAut true
                (↑f→q (decRec (λ _ → ↑f _) (λ _ → fail) x))
            }
            (λ _ → id)
            (λ ¬p → Empty.rec (¬p refl))
            (discAlpha c c)
        ∘g id ,⊗ toAut (↑q _)
        ∘g ⊗-unit-r⁻
      toAut (↑q _) = STOP litAut _

  module _
    (M : ImplicitDeterministicAutomaton ℓ)
    (M' : ImplicitDeterministicAutomaton ℓ')
    (notBothNull : (M .null ≡ false) ⊎ (M' .null ≡ false))
    (disjointFirsts :
      ∀ (c : ⟨ Alphabet ⟩) →
      (fail ≡ M .δᵢ c) ⊎ (fail ≡ M' .δᵢ c)
    )
    where

    private
      ⊕Aut = ⊕AutR discAlpha M M' notBothNull disjointFirsts

      ⟦_⟧M : FreelyAddInitial (M .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M = Parse ⊕Aut
      ⟦ ↑i q ⟧M = Trace ⊕Aut true (↑q Sum.inl q)

      ⟦_⟧M' : FreelyAddInitial (M' .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M' = Parse ⊕Aut
      ⟦ ↑i q' ⟧M' = Trace ⊕Aut true (↑q Sum.inr q')

      ⟦_⟧⊕ : FreelyAddInitial (⊕Aut .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧⊕ = Parse M ⊕ Parse M'
      ⟦ ↑i (Sum.inl q) ⟧⊕ = LiftG ℓ' (Trace M true (↑q q))
      ⟦ ↑i (Sum.inr q') ⟧⊕ = LiftG ℓ (Trace M' true (↑q q'))

      MAlg : ParseAlg M ⟦_⟧M
      MAlg fail = ParseAlgFail M _
      MAlg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) →
            Sum.elim
              {C = λ x →
                Trace ⊕Aut
                  (Sum.rec
                    (λ _ → M' .null)
                    (λ _ → M .null)
                    x)
                  initial ⊢
                  Parse ⊕Aut}
              (λ x → Empty.rec (true≢false x))
              (λ _ → id)
              notBothNull
            ∘g STOPᵢ ⊕Aut
            ∘g lowerG ∘g lowerG
          (stepᵢ c) →
            stepInitial c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        stepInitial : (c : ⟨ Alphabet ⟩) →
          ＂ c ＂ ⊗ ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c))
            ⊢ ParseAlgCarrier M ⟦_⟧M initial
        stepInitial c =
          STEPᵢ ⊕Aut c
          ∘g id ,⊗
            Sum.elim
              {C = λ x →
                ParseAlgCarrier M ⟦_⟧M
                  (↑f→q (M .δᵢ c))
                ⊢
                Trace ⊕Aut true
                  (↑f→q
                    (Sum.rec
                      (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
                      (λ _ → mapFreelyAddFail Sum.inl (M .δᵢ c))
                      x
                    )
                  )
              }
              (J
                (λ x y →
                  ParseAlgCarrier M ⟦_⟧M (↑f→q x)
                  ⊢
                  Trace ⊕Aut true (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
                )
                ⊥*-elim)
              (λ _ → help)
              (disjointFirsts c)
            where
            help :
              ParseAlgCarrier M ⟦_⟧M
                (↑f→q (M .δᵢ c))
              ⊢
              Trace ⊕Aut true
               (↑f→q
                (mapFreelyAddFail Sum.inl
                 (M .δᵢ c)))
            help with M .δᵢ c
            ... | fail = ⊥*-elim
            ... | ↑f x = id
      MAlg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q x) →
            Eq.J (λ b tEq≡b → ε ⊢ Trace ⊕Aut b (↑q Sum.inl q)) (STOP ⊕Aut (Sum.inl q)) (Eq.sym x)
            ∘g lowerG ∘g lowerG
          (step .q c) →
            STEP ⊕Aut (Sum.inl q) c
            ∘g id ,⊗ help c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            where
            help : (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier M ⟦_⟧M
                (↑f→q
                  (M .δq q c)
                )
              ⊢
              Trace ⊕Aut true
                (↑f→q
                  (mapFreelyAddFail Sum.inl (M .δq q c))
                )
            help c with M .δq q c
            ... | fail = ⊥*-elim
            ... | ↑f x = id

      M'Alg : ParseAlg M' ⟦_⟧M'
      M'Alg fail = ParseAlgFail M' _
      M'Alg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) →
            Sum.elim
              {C = λ x →
                Trace ⊕Aut
                  (Sum.rec
                    (λ _ → M' .null)
                    (λ _ → M .null)
                    x)
                  initial ⊢
                  Parse ⊕Aut}
              (λ _ → id)
              (λ x → Empty.rec (true≢false x))
              notBothNull
            ∘g STOPᵢ ⊕Aut
            ∘g lowerG ∘g lowerG
          (stepᵢ c) →
            stepInitial c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        stepInitial : (c : ⟨ Alphabet ⟩) →
          ＂ c ＂ ⊗ ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
            ⊢ ParseAlgCarrier M' ⟦_⟧M' initial
        stepInitial c =
          STEPᵢ ⊕Aut c
          ∘g id ,⊗
            Sum.elim
              {C = λ x →
                ParseAlgCarrier M' ⟦_⟧M'
                  (↑f→q (M' .δᵢ c))
                ⊢
                Trace ⊕Aut true
                  (↑f→q
                    (Sum.rec
                      (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
                      (λ _ → mapFreelyAddFail Sum.inl (M .δᵢ c))
                      x
                    )
                  )
              }
              (λ _ → help)
              (J
                (λ x y →
                  ParseAlgCarrier M' ⟦_⟧M' (↑f→q x)
                  ⊢
                  Trace ⊕Aut true (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c)))
                )
                ⊥*-elim)
              (disjointFirsts c)
            where
            help :
              ParseAlgCarrier M' ⟦_⟧M'
                (↑f→q (M' .δᵢ c))
              ⊢
              Trace ⊕Aut true
               (↑f→q
                (mapFreelyAddFail Sum.inr
                 (M' .δᵢ c)))
            help with M' .δᵢ c
            ... | fail = ⊥*-elim
            ... | ↑f x = id
      M'Alg (↑q q') =
        ⊕ᴰ-elim λ where
          (stop .q' x) →
            Eq.J (λ b tEq≡b → ε ⊢ Trace ⊕Aut b (↑q Sum.inr q')) (STOP ⊕Aut (Sum.inr q')) (Eq.sym x)
            ∘g lowerG ∘g lowerG
          (step .q' c) →
            STEP ⊕Aut (Sum.inr q') c
            ∘g id ,⊗ help c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            where
            help : (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier M' ⟦_⟧M'
                (↑f→q
                  (M' .δq q' c)
                )
              ⊢
              Trace ⊕Aut true
                (↑f→q
                  (mapFreelyAddFail Sum.inr (M' .δq q' c))
                )
            help c with M' .δq q' c
            ... | fail = ⊥*-elim
            ... | ↑f x = id

      ⊕Alg : ParseAlg ⊕Aut ⟦_⟧⊕
      ⊕Alg fail = ParseAlgFail ⊕Aut _
      ⊕Alg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ x) →
            Sum.elim
              {C =
                λ y →
                true Eq.≡
                  Sum.rec
                    (λ _ → M' .null)
                    (λ _ → M .null)
                    y
                → ε ⊢ Parse M ⊕ Parse M'}
              (λ _ → λ {Eq.refl → inr ∘g STOPᵢ M'})
              (λ _ → λ {Eq.refl → inl ∘g STOPᵢ M})
              notBothNull
              x
            ∘g lowerG ∘g lowerG
          (stepᵢ c) →
            Sum.elim
              {C = λ x →
                ＂ c ＂ ⊗
                  ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                    (↑f→q
                      (Sum.rec
                        (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
                        (λ _ → mapFreelyAddFail Sum.inl (M .δᵢ c))
                        x
                      )
                    )
                  ⊢ Parse M ⊕ Parse M'
              }
              (λ _ →
                inr
                ∘g STEPᵢ M' c
                ∘g id ,⊗ helpL c
              )
              (λ _ →
                inl
                ∘g STEPᵢ M c
                ∘g id ,⊗ helpR c
              )
              (disjointFirsts c)
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG

            where
            helpL :
              (c : ⟨ Alphabet ⟩) →
                ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                  (↑f→q
                    (mapFreelyAddFail Sum.inr (M' .δᵢ c))
                  )
                ⊢ Trace M' true (↑f→q (M' .δᵢ c))
            helpL c with M' .δᵢ c
            ... | fail = ⊥*-elim
            ... | ↑f q' = lowerG

            helpR :
              (c : ⟨ Alphabet ⟩) →
                ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                  (↑f→q
                    (mapFreelyAddFail Sum.inl (M .δᵢ c))
                  )
                ⊢ Trace M true (↑f→q (M .δᵢ c))
            helpR c with M .δᵢ c
            ... | fail = ⊥*-elim
            ... | ↑f q = lowerG
      ⊕Alg (↑q (Sum.inl q)) =
        ⊕ᴰ-elim λ where
          (stop .(Sum.inl q) x) →
            liftG
            ∘g Eq.J (λ x y → ε ⊢ Trace M x (↑q q)) (STOP M q) (Eq.sym x)
            ∘g lowerG ∘g lowerG
          (step .(Sum.inl q) c) →
            liftG
            ∘g STEP M q c
            ∘g id ,⊗ help q c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            where
            help :
              (q : M .Q) →
              (c : ⟨ Alphabet ⟩) →
                ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                  (↑f→q
                    (mapFreelyAddFail Sum.inl (M .δq q c))
                  )
                ⊢ Trace M true (↑f→q (M .δq q c))
            help q c with M .δq q c
            ... | fail = ⊥*-elim
            ... | ↑f q = lowerG
      ⊕Alg (↑q (Sum.inr q')) =
        ⊕ᴰ-elim λ where
          (stop .(Sum.inr q') x) →
            liftG
            ∘g Eq.J (λ x y → ε ⊢ Trace M' x (↑q q')) (STOP M' q') (Eq.sym x)
            ∘g lowerG ∘g lowerG
          (step .(Sum.inr q') c) →
            liftG
            ∘g STEP M' q' c
            ∘g id ,⊗ help q' c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
            where
            help :
              (q' : (M' .Q)) →
              (c : ⟨ Alphabet ⟩) →
                ParseAlgCarrier ⊕Aut ⟦_⟧⊕
                  (↑f→q
                    (mapFreelyAddFail Sum.inr (M' .δq q' c))
                  )
                ⊢ Trace M' true (↑f→q (M' .δq q' c))
            help q' c with M' .δq q' c
            ... | fail = ⊥*-elim
            ... | ↑f q' = lowerG

      M→⊕Aut : Parse M ⊢ Parse ⊕Aut
      M→⊕Aut = rec _ MAlg initial

      M'→⊕Aut : Parse M' ⊢ Parse ⊕Aut
      M'→⊕Aut = rec _ M'Alg initial

      ⊕Aut→M⊕M' : Parse ⊕Aut ⊢ (Parse M ⊕ Parse M')
      ⊕Aut→M⊕M' = rec _ ⊕Alg initial

    ⊕Aut≈ : Parse ⊕Aut ≈ Parse M ⊕ Parse M'
    ⊕Aut≈ = mkLogEq ⊕Aut→M⊕M' (⊕-elim M→⊕Aut M'→⊕Aut)

  module _
    (M : ImplicitDeterministicAutomaton ℓ)
    (M' : ImplicitDeterministicAutomaton ℓ')
    (notNullM : (M .null ≡ false))
    (seqUnambig :
      ∀ (c : ⟨ Alphabet ⟩) →
      (∀ (q : M .Q) → M .acc q ≡ true → fail ≡ M .δq q c) ⊎ (fail ≡ M' .δᵢ c)
    )
    where

    private
      ⊗Aut = ⊗AutR discAlpha M M' notNullM seqUnambig

      -- Continuation-passing carrier: the M-trace is interpreted as
      -- "given a Parse M' to splice in once M finishes, build a Parse ⊗Aut
      -- (resp. Trace ⊗Aut at the corresponding inl-state)."
      ⟦_⟧M : FreelyAddInitial (M .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M = Parse M' ⊸ Parse ⊗Aut
      ⟦ ↑i q ⟧M = Parse M' ⊸ Trace ⊗Aut true (↑q Sum.inl q)

      ⟦_⟧M' : FreelyAddInitial (M' .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧M' =
        &[ q ∈ M .Q ]
        &[ _ ∈ true Eq.≡ M .acc q ]
          Trace ⊗Aut true (↑q Sum.inl q)
      ⟦ ↑i q' ⟧M' = Trace ⊗Aut true (↑q Sum.inr q')

      ⟦_⟧⊗ : FreelyAddInitial (⊗Aut .Q) → Grammar (ℓ-max ℓ ℓ')
      ⟦ initial ⟧⊗ = Parse M ⊗ Parse M'
      ⟦ ↑i (Sum.inl q) ⟧⊗ = Trace M true (↑q q) ⊗ Parse M'
      ⟦ ↑i (Sum.inr q') ⟧⊗ = LiftG ℓ (Trace M' true (↑q q'))

      M'Alg : ParseAlg M' ⟦_⟧M'
      M'Alg fail = ParseAlgFail M' _
      M'Alg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) →
            &ᴰ-intro (λ q →
              &ᴰ-intro (λ accEq →
                Eq.J
                  (λ b _ → ε ⊢ Trace ⊗Aut (b and true) (↑q Sum.inl q))
                  (STOP ⊗Aut (Sum.inl q))
                  (Eq.sym accEq)
              )
            )
            ∘g lowerG ∘g lowerG
          (stepᵢ c) →
            &ᴰ-intro (λ q →
              &ᴰ-intro (λ accEq →
                STEP ⊗Aut (Sum.inl q) c
                ∘g id ,⊗ convertM'next c q accEq
              )
            )
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        convertInlSeq : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
          ⊢ Trace ⊗Aut true (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
        convertInlSeq c with M' .δᵢ c
        ... | fail   = ⊥*-elim
        ... | ↑f q'  = id

        convertInrSeq : (c : ⟨ Alphabet ⟩) →
          (eq : fail ≡ M' .δᵢ c) (q : M .Q) →
          ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
          ⊢ Trace ⊗Aut true (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
        convertInrSeq c eq q with M' .δᵢ c
        ... | fail   = ⊥*-elim
        ... | ↑f q'  = Empty.rec (fail≢↑f (Eq.pathToEq eq))

        convertM'nextBase : (c : ⟨ Alphabet ⟩) (q : M .Q) →
          ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
          ⊢ Trace ⊗Aut true (↑f→q
              (Sum.rec
                (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
                (λ _ → mapFreelyAddFail Sum.inl (M .δq q c))
                (seqUnambig c)))
        convertM'nextBase c q with seqUnambig c
        ... | Sum.inl _   = convertInlSeq c
        ... | Sum.inr eq  = convertInrSeq c eq q

        convertM'next : (c : ⟨ Alphabet ⟩) (q : M .Q) (accEq : true Eq.≡ M .acc q) →
          ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
          ⊢ Trace ⊗Aut true (↑f→q (⊗Aut .δq (Sum.inl q) c))
        convertM'next c q accEq =
          Eq.J
            (λ b _ →
              ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δᵢ c))
              ⊢ Trace ⊗Aut true (↑f→q
                  (if b
                    then Sum.rec
                      (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
                      (λ _ → mapFreelyAddFail Sum.inl (M .δq q c))
                      (seqUnambig c)
                    else mapFreelyAddFail Sum.inl (M .δq q c))))
            (convertM'nextBase c q)
            accEq
      M'Alg (↑q q') =
        ⊕ᴰ-elim λ where
          (stop .q' x) →
            Eq.J (λ b _ → ε ⊢ Trace ⊗Aut b (↑q Sum.inr q')) (STOP ⊗Aut (Sum.inr q')) (Eq.sym x)
            ∘g lowerG ∘g lowerG
          (step .q' c) →
            STEP ⊗Aut (Sum.inr q') c
            ∘g id ,⊗ helpM' c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        helpM' : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier M' ⟦_⟧M' (↑f→q (M' .δq q' c))
          ⊢ Trace ⊗Aut true (↑f→q (mapFreelyAddFail Sum.inr (M' .δq q' c)))
        helpM' c with M' .δq q' c
        ... | fail    = ⊥*-elim
        ... | ↑f q''  = id

      M'→⊗Aut-internal : Parse M' ⊢ ⟦ initial ⟧M'
      M'→⊗Aut-internal = rec _ M'Alg initial

      MAlg : ParseAlg M ⟦_⟧M
      MAlg fail = ParseAlgFail M _
      MAlg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) → Empty.rec (true≢false notNullM)
          (stepᵢ c) →
            ⊸-intro
              (STEPᵢ ⊗Aut c
              ∘g id ,⊗ stepInitConv c
              ∘g ⊗-assoc⁻)
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        stepInitConv : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c)) ⊗ Parse M'
          ⊢ Trace ⊗Aut true (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c)))
        stepInitConv c with M .δᵢ c
        ... | fail   = ⊥*⊗-elim
        ... | ↑f q'' = ⊸-app
      MAlg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q x) →
            ⊸-intro
              (π x
              ∘g π q
              ∘g M'→⊗Aut-internal
              ∘g ⊗-unit-l)
            ∘g lowerG ∘g lowerG
          (step .q c) →
            ⊸-intro
              (STEP ⊗Aut (Sum.inl q) c
              ∘g id ,⊗ stepConv c
              ∘g ⊗-assoc⁻)
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        stepConvStay : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse M'
          ⊢ Trace ⊗Aut true (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
        stepConvStay c with M .δq q c
        ... | fail   = ⊥*⊗-elim
        ... | ↑f q'' = ⊸-app

        stepConvContra : (c : ⟨ Alphabet ⟩) →
          (h : (q : M .Q) → M .acc q ≡ true → fail ≡ M .δq q c) →
          (accEq : M .acc q Eq.≡ true) →
          ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse M'
          ⊢ Trace ⊗Aut true (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
        stepConvContra c h accEq with M .δq q c in dqEq
        ... | fail   = ⊥*⊗-elim
        ... | ↑f q'' =
          Empty.rec
            (fail≢↑f (Eq.pathToEq (h q (Eq.eqToPath accEq) ∙ Eq.eqToPath dqEq)))

        stepConv : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse M'
          ⊢ Trace ⊗Aut true (↑f→q (⊗Aut .δq (Sum.inl q) c))
        stepConv c with M .acc q in accEq
        ... | false = stepConvStay c
        ... | true with seqUnambig c
        ...   | Sum.inr _ = stepConvStay c
        ...   | Sum.inl h = stepConvContra c h accEq

      and-elim-l : ∀ {a b : Bool} → true Eq.≡ a and b → true Eq.≡ a
      and-elim-l {true}  {_} _ = Eq.refl
      and-elim-l {false} {_} x = x

      and-elim-r : ∀ {a b : Bool} → true Eq.≡ a and b → true Eq.≡ b
      and-elim-r {true}  {_} x = x
      and-elim-r {false} {_} x = Empty.rec (true≢false (Eq.eqToPath x))

      ⊗Alg : ParseAlg ⊗Aut ⟦_⟧⊗
      ⊗Alg fail = ParseAlgFail ⊗Aut _

      ⊗Alg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ x) → Empty.rec (true≢false (Eq.eqToPath x))
          (stepᵢ c) →
            (STEPᵢ M c ,⊗ id)
            ∘g ⊗-assoc
            ∘g id ,⊗ helpInit c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        helpInit : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier ⊗Aut ⟦_⟧⊗ (↑f→q (mapFreelyAddFail Sum.inl (M .δᵢ c)))
            ⊢ Trace M true (↑f→q (M .δᵢ c)) ⊗ Parse M'
        helpInit c with M .δᵢ c
        ... | fail = ⊥*-elim
        ... | ↑f q = id

      ⊗Alg (↑q (Sum.inl q)) =
        ⊕ᴰ-elim λ where
          (stop .(Sum.inl q) x) →
            stopInl x ∘g lowerG ∘g lowerG
          (step .(Sum.inl q) c) →
            stepInl c ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        traceOnAcc : ∀ {q : M .Q} → true Eq.≡ M .acc q → ε ⊢ Trace M true (↑q q)
        traceOnAcc {q} accEq =
          Eq.J (λ b _ → ε ⊢ Trace M b (↑q q)) (STOP M q) (Eq.sym accEq)

        traceOnNull : true Eq.≡ M' .null → ε ⊢ Parse M'
        traceOnNull nullEq =
          Eq.J (λ b _ → ε ⊢ Trace M' b initial) (STOPᵢ M') (Eq.sym nullEq)

        stopInl : true Eq.≡ (M .acc q and M' .null) →
          ε ⊢ Trace M true (↑q q) ⊗ Parse M'
        stopInl x =
          (traceOnAcc {q} (and-elim-l x)) ,⊗ (traceOnNull (and-elim-r x))
          ∘g ⊗-unit-l⁻

        helpStayM : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier ⊗Aut ⟦_⟧⊗ (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
            ⊢ Trace M true (↑f→q (M .δq q c)) ⊗ Parse M'
        helpStayM c with M .δq q c
        ... | fail   = ⊥*-elim
        ... | ↑f q'' = id

        helpJumpM' : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier ⊗Aut ⟦_⟧⊗ (↑f→q (mapFreelyAddFail Sum.inr (M' .δᵢ c)))
            ⊢ Trace M' true (↑f→q (M' .δᵢ c))
        helpJumpM' c with M' .δᵢ c
        ... | fail  = ⊥*-elim
        ... | ↑f q' = lowerG

        stayMstep : (c : ⟨ Alphabet ⟩) →
          ＂ c ＂ ⊗ ParseAlgCarrier ⊗Aut ⟦_⟧⊗
            (↑f→q (mapFreelyAddFail Sum.inl (M .δq q c)))
            ⊢ Trace M true (↑q q) ⊗ Parse M'
        stayMstep c =
          (STEP M q c ,⊗ id)
          ∘g ⊗-assoc
          ∘g id ,⊗ helpStayM c

        stepInl : (c : ⟨ Alphabet ⟩) →
          ＂ c ＂ ⊗ ParseAlgCarrier ⊗Aut ⟦_⟧⊗
            (↑f→q
              (if M .acc q
                then Sum.rec
                  (λ _ → mapFreelyAddFail Sum.inr (M' .δᵢ c))
                  (λ _ → mapFreelyAddFail Sum.inl (M .δq q c))
                  (seqUnambig c)
                else mapFreelyAddFail Sum.inl (M .δq q c)))
            ⊢ Trace M true (↑q q) ⊗ Parse M'
        stepInl c with M .acc q in accEq
        ... | false = stayMstep c
        ... | true with seqUnambig c
        ...    | Sum.inr _ = stayMstep c
        ...    | Sum.inl _ =
          Eq.J (λ b _ → ε ⊢ Trace M b (↑q q)) (STOP M q) accEq ,⊗ STEPᵢ M' c
          ∘g ⊗-unit-l⁻
          ∘g id ,⊗ helpJumpM' c

      ⊗Alg (↑q (Sum.inr q')) =
        ⊕ᴰ-elim λ where
          (stop .(Sum.inr q') x) →
            liftG
            ∘g Eq.J (λ b _ → ε ⊢ Trace M' b (↑q q')) (STOP M' q') (Eq.sym x)
            ∘g lowerG ∘g lowerG
          (step .(Sum.inr q') c) →
            liftG
            ∘g STEP M' q' c
            ∘g id ,⊗ help c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        help : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier ⊗Aut ⟦_⟧⊗ (↑f→q (mapFreelyAddFail Sum.inr (M' .δq q' c)))
            ⊢ Trace M' true (↑f→q (M' .δq q' c))
        help c with M' .δq q' c
        ... | fail    = ⊥*-elim
        ... | ↑f q''  = lowerG

      M→⊗Aut : Parse M ⊢ ⟦ initial ⟧M
      M→⊗Aut = rec _ MAlg initial

      M'→⊗Aut : Parse M' ⊢ ⟦ initial ⟧M'
      M'→⊗Aut = rec _ M'Alg initial

      M⊗M'→⊗Aut : Parse M ⊗ Parse M' ⊢ Parse ⊗Aut
      M⊗M'→⊗Aut = ⊸-app ∘g M→⊗Aut ,⊗ id

      ⊗Aut→M⊗M' : Parse ⊗Aut ⊢ Parse M ⊗ Parse M'
      ⊗Aut→M⊗M' = rec _ ⊗Alg initial

    ⊗Aut≈ : Parse ⊗Aut ≈ Parse M ⊗ Parse M'
    ⊗Aut≈ = mkLogEq ⊗Aut→M⊗M' M⊗M'→⊗Aut

  module _
    (M : ImplicitDeterministicAutomaton ℓ)
    (notNullM : (M .null ≡ false))
    (seqUnambig :
      ∀ (c : ⟨ Alphabet ⟩) →
      (∀ (q : M .Q) → M .acc q ≡ true → fail ≡ M .δq q c) ⊎ (fail ≡ M .δᵢ c)
    )
    where

    private
      *Aut = *AutR discAlpha M notNullM seqUnambig

      -- pasteAt q accEq: splice a Parse *Aut continuation as a Trace *Aut
      -- starting from (↑q q) at an accepting M-state.
      module Paste (q : M .Q) (accEq : true Eq.≡ M .acc q) where
        ⟦_⟧Paste : FreelyAddInitial (M .Q) → Grammar ℓ
        ⟦ initial ⟧Paste = Trace *Aut true (↑q q)
        ⟦ ↑i q' ⟧Paste = Trace *Aut true (↑q q')

        pasteAlg : ParseAlg *Aut ⟦_⟧Paste
        pasteAlg fail = ParseAlgFail *Aut _
        pasteAlg initial =
          ⊕ᴰ-elim λ where
            (stopᵢ Eq.refl) →
              Eq.J (λ b _ → ε ⊢ Trace *Aut b (↑q q)) (STOP *Aut q) (Eq.sym accEq)
              ∘g lowerG ∘g lowerG
            (stepᵢ c) →
              STEP *Aut q c
              ∘g id ,⊗ initialStepConv c
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          where
          initialStepConvBase : (c : ⟨ Alphabet ⟩) →
            ParseAlgCarrier *Aut ⟦_⟧Paste (↑f→q (M .δᵢ c))
            ⊢ Trace *Aut true (↑f→q
                (Sum.rec
                  (λ _ → M .δᵢ c)
                  (λ _ → M .δq q c)
                  (seqUnambig c)))
          initialStepConvBase c with seqUnambig c
          ... | Sum.inl _  = stay c
            where
            stay : (c : ⟨ Alphabet ⟩) →
              ParseAlgCarrier *Aut ⟦_⟧Paste (↑f→q (M .δᵢ c))
              ⊢ Trace *Aut true (↑f→q (M .δᵢ c))
            stay c with M .δᵢ c
            ... | fail   = ⊥*-elim
            ... | ↑f q'' = id
          ... | Sum.inr eq = contradiction c eq
            where
            contradiction : (c : ⟨ Alphabet ⟩) → fail ≡ M .δᵢ c →
              ParseAlgCarrier *Aut ⟦_⟧Paste (↑f→q (M .δᵢ c))
              ⊢ Trace *Aut true (↑f→q (M .δq q c))
            contradiction c eq with M .δᵢ c
            ... | fail   = ⊥*-elim
            ... | ↑f q'' = Empty.rec (fail≢↑f (Eq.pathToEq eq))

          initialStepConv : (c : ⟨ Alphabet ⟩) →
            ParseAlgCarrier *Aut ⟦_⟧Paste (↑f→q (M .δᵢ c))
            ⊢ Trace *Aut true (↑f→q (*Aut .δq q c))
          initialStepConv c =
            Eq.J
              (λ b _ →
                ParseAlgCarrier *Aut ⟦_⟧Paste (↑f→q (M .δᵢ c))
                ⊢ Trace *Aut true (↑f→q
                    (if b
                      then Sum.rec
                        (λ _ → M .δᵢ c)
                        (λ _ → M .δq q c)
                        (seqUnambig c)
                      else M .δq q c)))
              (initialStepConvBase c)
              accEq
        pasteAlg (↑q q') =
          ⊕ᴰ-elim λ where
            (stop .q' x) →
              Eq.J (λ b _ → ε ⊢ Trace *Aut b (↑q q')) (STOP *Aut q') (Eq.sym x)
              ∘g lowerG ∘g lowerG
            (step .q' c) →
              STEP *Aut q' c
              ∘g id ,⊗ stepRelay c
              ∘g (lowerG ∘g lowerG) ,⊗ lowerG
          where
          stepRelay : (c : ⟨ Alphabet ⟩) →
            ParseAlgCarrier *Aut ⟦_⟧Paste (↑f→q (*Aut .δq q' c))
            ⊢ Trace *Aut true (↑f→q (*Aut .δq q' c))
          stepRelay c with *Aut .δq q' c
          ... | fail    = ⊥*-elim
          ... | ↑f q''' = id

        pasteAt : Parse *Aut ⊢ Trace *Aut true (↑q q)
        pasteAt = rec _ pasteAlg initial

      ⟦_⟧M : FreelyAddInitial (M .Q) → Grammar ℓ
      ⟦ initial ⟧M = Parse *Aut ⊸ Parse *Aut
      ⟦ ↑i q ⟧M = Parse *Aut ⊸ Trace *Aut true (↑q q)

      MAlg : ParseAlg M ⟦_⟧M
      MAlg fail = ParseAlgFail M _
      MAlg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) → Empty.rec (true≢false notNullM)
          (stepᵢ c) →
            ⊸-intro
              (STEPᵢ *Aut c
              ∘g id ,⊗ stepInitConv c
              ∘g ⊗-assoc⁻)
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        stepInitConv : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δᵢ c)) ⊗ Parse *Aut
          ⊢ Trace *Aut true (↑f→q (M .δᵢ c))
        stepInitConv c with M .δᵢ c
        ... | fail   = ⊥*⊗-elim
        ... | ↑f q'' = ⊸-app
      MAlg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q accEq) →
            ⊸-intro (Paste.pasteAt q accEq ∘g ⊗-unit-l)
            ∘g lowerG ∘g lowerG
          (step .q c) →
            ⊸-intro
              (STEP *Aut q c
              ∘g id ,⊗ stepConv c
              ∘g ⊗-assoc⁻)
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        stepConvStay : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse *Aut
          ⊢ Trace *Aut true (↑f→q (M .δq q c))
        stepConvStay c with M .δq q c
        ... | fail   = ⊥*⊗-elim
        ... | ↑f q'' = ⊸-app

        stepConvContra : (c : ⟨ Alphabet ⟩) →
          (h : (q : M .Q) → M .acc q ≡ true → fail ≡ M .δq q c) →
          (accEqTrue : M .acc q Eq.≡ true) →
          ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse *Aut
          ⊢ Trace *Aut true (↑f→q (M .δᵢ c))
        stepConvContra c h accEqTrue with M .δq q c in dqEq
        ... | fail   = ⊥*⊗-elim
        ... | ↑f q'' =
          Empty.rec
            (fail≢↑f (Eq.pathToEq (h q (Eq.eqToPath accEqTrue) ∙ Eq.eqToPath dqEq)))

        stepConv : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier M ⟦_⟧M (↑f→q (M .δq q c)) ⊗ Parse *Aut
          ⊢ Trace *Aut true (↑f→q (*Aut .δq q c))
        stepConv c with M .acc q in accEq
        ... | false = stepConvStay c
        ... | true with seqUnambig c
        ...     | Sum.inr _ = stepConvStay c
        ...     | Sum.inl h = stepConvContra c h accEq

      ⟦_⟧* : FreelyAddInitial (M .Q) → Grammar ℓ
      ⟦ initial ⟧* = KL* (Parse M)
      ⟦ ↑i q ⟧* = Trace M true (↑q q) ⊗ KL* (Parse M)

      *Alg : ParseAlg *Aut ⟦_⟧*
      *Alg fail = ParseAlgFail *Aut _
      *Alg initial =
        ⊕ᴰ-elim λ where
          (stopᵢ Eq.refl) → NIL ∘g lowerG ∘g lowerG
          (stepᵢ c) →
            CONS
            ∘g (STEPᵢ M c ,⊗ id)
            ∘g ⊗-assoc
            ∘g id ,⊗ helpInit c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        helpInit : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier *Aut ⟦_⟧* (↑f→q (M .δᵢ c))
          ⊢ Trace M true (↑f→q (M .δᵢ c)) ⊗ KL* (Parse M)
        helpInit c with M .δᵢ c
        ... | fail   = ⊥*-elim
        ... | ↑f q'' = id
      *Alg (↑q q) =
        ⊕ᴰ-elim λ where
          (stop .q accEq) →
            ((Eq.J (λ b _ → ε ⊢ Trace M b (↑q q)) (STOP M q) (Eq.sym accEq)) ,⊗ NIL)
            ∘g ⊗-unit-l⁻
            ∘g lowerG ∘g lowerG
          (step .q c) →
            stepHandler c
            ∘g (lowerG ∘g lowerG) ,⊗ lowerG
        where
        helpStay : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier *Aut ⟦_⟧* (↑f→q (M .δq q c))
          ⊢ Trace M true (↑f→q (M .δq q c)) ⊗ KL* (Parse M)
        helpStay c with M .δq q c
        ... | fail   = ⊥*-elim
        ... | ↑f q'' = id

        stepStay : (c : ⟨ Alphabet ⟩) →
          ＂ c ＂ ⊗ ParseAlgCarrier *Aut ⟦_⟧* (↑f→q (M .δq q c))
          ⊢ Trace M true (↑q q) ⊗ KL* (Parse M)
        stepStay c =
          (STEP M q c ,⊗ id)
          ∘g ⊗-assoc
          ∘g id ,⊗ helpStay c

        helpJump : (c : ⟨ Alphabet ⟩) →
          ParseAlgCarrier *Aut ⟦_⟧* (↑f→q (M .δᵢ c))
          ⊢ Trace M true (↑f→q (M .δᵢ c)) ⊗ KL* (Parse M)
        helpJump c with M .δᵢ c
        ... | fail   = ⊥*-elim
        ... | ↑f q'' = id

        stepJump : (c : ⟨ Alphabet ⟩) → (accEqTrue : M .acc q Eq.≡ true) →
          ＂ c ＂ ⊗ ParseAlgCarrier *Aut ⟦_⟧* (↑f→q (M .δᵢ c))
          ⊢ Trace M true (↑q q) ⊗ KL* (Parse M)
        stepJump c accEqTrue =
          ((Eq.J (λ b _ → ε ⊢ Trace M b (↑q q)) (STOP M q) accEqTrue)
            ,⊗
            (CONS
              ∘g (STEPᵢ M c ,⊗ id)
              ∘g ⊗-assoc
              ∘g id ,⊗ helpJump c))
          ∘g ⊗-unit-l⁻

        stepHandler : (c : ⟨ Alphabet ⟩) →
          ＂ c ＂ ⊗ ParseAlgCarrier *Aut ⟦_⟧* (↑f→q (*Aut .δq q c))
          ⊢ Trace M true (↑q q) ⊗ KL* (Parse M)
        stepHandler c with M .acc q in accEq
        ... | false = stepStay c
        ... | true with seqUnambig c
        ...     | Sum.inr _ = stepStay c
        ...     | Sum.inl _ = stepJump c accEq

      M→*Aut : Parse M ⊢ ⟦ initial ⟧M
      M→*Aut = rec _ MAlg initial

      KL*→*Aut : KL* (Parse M) ⊢ Parse *Aut
      KL*→*Aut = fold*r (Parse M) (STOPᵢ *Aut) (⊸-app ∘g M→*Aut ,⊗ id)

      *Aut→KL* : Parse *Aut ⊢ KL* (Parse M)
      *Aut→KL* = rec _ *Alg initial

    *Aut≈ : Parse *Aut ≈ KL* (Parse M)
    *Aut≈ = mkLogEq *Aut→KL* KL*→*Aut
