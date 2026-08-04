-- Tinyness + other distribution laws for char
--
-- char ⊗ (A ⊕ B) ≅ (char ⊗ A) ⊕ (char ⊗ B)
-- (A ⊕ B) ⊗ char ≅ (A ⊗ char) ⊕ (B ⊗ char)
-- (A & B) ⊗ char ≅ (A ⊗ char) & (B ⊗ char)
--
-- Similarly, for all w : String,
-- ⌈⌉-⊗&-distR≅ : (A & B) ⊗ ⌈ w ⌉ ≅ (A ⊗ ⌈ w ⌉) & (B ⊗ ⌈ w ⌉)
--
-- These are useful for establishing sequential unambiguity axioms
-- in the shallow embedding
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.External.String.Tiny (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List as List hiding (rec)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.External.HLevels.Properties Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.String.Unambiguous Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.String.Properties Alphabet

open import Term.Base Alphabet

private
  variable
    w : String
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

open StrongEquivalence

char-⊗⊕-distL⁻ : (char ⊗ A) ⊕ (char ⊗ B) ⊢ char ⊗ (A ⊕ B)
char-⊗⊕-distL⁻ = ⊕-elim (id ,⊗ inl) (id ,⊗ inr)

char-⊗⊕-distR⁻ : (A ⊗ char) ⊕ (B ⊗ char) ⊢ (A ⊕ B) ⊗ char
char-⊗⊕-distR⁻ = ⊕-elim (inl ,⊗ id) (inr ,⊗ id)

⌈⌉-⊗⊕-distL⁻ : (⌈ w ⌉ ⊗ A) ⊕ (⌈ w ⌉ ⊗ B) ⊢ ⌈ w ⌉ ⊗ (A ⊕ B)
⌈⌉-⊗⊕-distL⁻ = ⊕-elim (id ,⊗ inl) (id ,⊗ inr)

⌈⌉-⊗⊕-distR⁻ : (A ⊗ ⌈ w ⌉) ⊕ (B ⊗ ⌈ w ⌉) ⊢ (A ⊕ B) ⊗ ⌈ w ⌉
⌈⌉-⊗⊕-distR⁻ = ⊕-elim (inl ,⊗ id) (inr ,⊗ id)

char-⊗⊕-distL≅ : char ⊗ (A ⊕ B) ≅ (char ⊗ A) ⊕ (char ⊗ B)
char-⊗⊕-distL≅ .fun = ⊗⊕-distL
char-⊗⊕-distL≅ .inv = char-⊗⊕-distL⁻
char-⊗⊕-distL≅ {A = A} {B = B} .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_
    the-sec : char-⊗⊕-distL≅ {A = A} {B = B} .fun ∘g char-⊗⊕-distL≅ .inv ≡ id
    the-sec i w (Sum.inl p) = Sum.inl p
    the-sec i w (Sum.inr p) = Sum.inr p
char-⊗⊕-distL≅ .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_ _⊗_
    the-ret : char-⊗⊕-distL≅ {A = A} {B = B} .inv ∘g char-⊗⊕-distL≅ .fun ≡ id
    the-ret i w (s , p , Sum.inl q) = s , p , Sum.inl q
    the-ret i w (s , p , Sum.inr q) = s , p , Sum.inr q

char-⊗⊕-distR≅ : (A ⊕ B) ⊗ char ≅ (A ⊗ char) ⊕ (B ⊗ char)
char-⊗⊕-distR≅ .fun = ⊗⊕-distR
char-⊗⊕-distR≅ .inv = char-⊗⊕-distR⁻
char-⊗⊕-distR≅ {A = A} {B = B} .sec = the-sec
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distL _⊕_
    the-sec : char-⊗⊕-distR≅ {A = A} {B = B} .fun ∘g char-⊗⊕-distR≅ .inv ≡ id
    the-sec i w (Sum.inl p) = Sum.inl p
    the-sec i w (Sum.inr p) = Sum.inr p
char-⊗⊕-distR≅ .ret = the-ret
  where
  opaque
    unfolding ⊗-intro ⊕-elim ⊗⊕-distR _⊕_ _⊗_
    the-ret : char-⊗⊕-distR≅ {A = A} {B = B} .inv ∘g char-⊗⊕-distR≅ .fun ≡ id
    the-ret i w (s , Sum.inl p , q) = s , Sum.inl p , q
    the-ret i w (s , Sum.inr p , q) = s , Sum.inr p , q

opaque
  unfolding the-split _⊗_ literal
  unique-splitting-charL :
    (w : String) →
    (p : (char ⊗ A) w) →
    (q : (char ⊗ B) w) →
    same-splits {w = λ _ → w} p q
  unique-splitting-charL  w (s , (c , p) , q) (s' , (c' , p') , q') =
    ≡-×
      (Eq.eqToPath p ∙ cong (_∷ []) (cons-inj₁ w≡) ∙ sym (Eq.eqToPath p'))
      (cons-inj₂ w≡)
    where
    w≡ : [ c ] ++ s .fst .snd ≡ [ c' ] ++ s' .fst .snd
    w≡ = sym (Eq.eqToPath (s .snd) ∙ cong (_++ s. fst .snd) (Eq.eqToPath p)) ∙ Eq.eqToPath (s' .snd) ∙ cong (_++ s' .fst .snd) (Eq.eqToPath p')


  opaque
    unfolding ⊗-intro
    unique-splitting-literalL :
      {c : ⟨ Alphabet ⟩} →
      (w : String) →
      (p : (＂ c ＂ ⊗ A) w) →
      (q : (＂ c ＂ ⊗ B) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-literalL {A = A} {c = c} w p q =
      unique-splitting-charL w ((literal→char c  ,⊗ id) w p ) ((literal→char c ,⊗ id) w q)

  unique-splitting-charR :
    (w : String) →
    (p : (A ⊗ char) w) →
    (q : (B ⊗ char) w) →
    same-splits {w = λ _ → w} p q
  unique-splitting-charR {A = A} w (s , p , (c , q)) (s' , p' , (c' , q')) =
    ≡-×
      (snoc-inj₁ w≡)
      (Eq.eqToPath q ∙ cong (_∷ []) (snoc-inj₂ w≡) ∙ sym (Eq.eqToPath q'))
    where
    w≡ : s .fst .fst ++ [ c ] ≡ s' .fst .fst ++ [ c' ]
    w≡ = sym (Eq.eqToPath (s .snd) ∙ cong (s .fst .fst ++_) (Eq.eqToPath q)) ∙ Eq.eqToPath (s' .snd) ∙ cong (s' .fst .fst ++_) (Eq.eqToPath q')

  opaque
    unfolding ⊗-intro
    unique-splitting-literalR :
      {c : ⟨ Alphabet ⟩} →
      (w : String) →
      (p : (A ⊗ ＂ c ＂) w) →
      (q : (B ⊗ ＂ c ＂) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-literalR {A = A} {c = c} w p q =
      unique-splitting-charR w ((id ,⊗ literal→char c) w p ) ((id ,⊗ literal→char c) w q)


module _ (x : String) where
  opaque
    unfolding the-split _⊗_ literal
    unique-splitting-⌈⌉L :
      (w : String) →
      (p : (⌈ x ⌉ ⊗ A) w) →
      (q : (⌈ x ⌉ ⊗ B) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-⌈⌉L w (s , px , q) (s' , px' , q') =
      ≡-× 11≡
        (
        sym (dropLength++ (s' .fst .fst))
        ∙ cong (drop (length (s' .fst .fst)))
          (cong (_++ s .fst .snd) (sym 11≡)
          ∙ sym (Eq.eqToPath (s .snd)) ∙ (Eq.eqToPath (s' .snd)))
        ∙ dropLength++ (s' .fst .fst)
        )
        where
        11≡ : s .fst .fst ≡ s' .fst .fst
        11≡ = (sym (⌈⌉→≡ x (s .fst .fst) px) ∙ ⌈⌉→≡ x (s' .fst .fst) px')

    unique-splitting-⌈⌉R :
      (w : String) →
      (p : (A ⊗ ⌈ x ⌉) w) →
      (q : (B ⊗ ⌈ x ⌉) w) →
      same-splits {w = λ _ → w} p q
    unique-splitting-⌈⌉R w (s , q , px) (s' , q' , px') =
      ≡-×
        (
        sym (dropBackLength++ (s .fst .fst) (s .fst .snd))
        ∙ cong (dropBack (length (s .fst .snd)))
           (sym (Eq.eqToPath (s .snd)) ∙ (Eq.eqToPath (s' .snd)) ∙ cong (s' .fst .fst ++_) (sym 12≡))
        ∙ dropBackLength++ (s' .fst .fst) (s .fst .snd)
        )
        12≡
        where
        12≡ : s .fst .snd ≡ s' .fst .snd
        12≡ = (sym (⌈⌉→≡ x (s .fst .snd) px) ∙ ⌈⌉→≡ x (s' .fst .snd) px')

opaque
  unfolding _⊗_ _&_ the-split literal
  char-⊗&-distL⁻ :
    (char ⊗ A) & (char ⊗ B) ⊢ char ⊗ (A & B)
  char-⊗&-distL⁻ {B = B} w ((s , p , q) , (s' , p' , q')) =
    s , (p , (q , subst B s≡ q'))
    where
    s≡ : s' .fst .snd ≡ s .fst .snd
    s≡ = cons-inj₂
      (cong (_++ s' .fst .snd) (sym (Eq.eqToPath (p' .snd)))
      ∙ sym (Eq.eqToPath (s' .snd))
      ∙ Eq.eqToPath (s .snd)
      ∙ cong (_++ s .fst .snd) (Eq.eqToPath (p .snd))
      )

  ⌈⌉-⊗&-distL⁻ :
    (⌈ w ⌉ ⊗ A) & (⌈ w ⌉ ⊗ B) ⊢ ⌈ w ⌉ ⊗ (A & B)
  ⌈⌉-⊗&-distL⁻ {w = w} {A = A} {B = B} w' ((s , p , q) , (s' , p' , q')) =
    s , (p , q , subst B 12≡ q')
    where
    s≡ : same-splits
      {A = ⌈ w ⌉} {B = A} {C = ⌈ w ⌉} {D = B}
      {w = λ _ → w'}
      (s , p , q)
      (s' , p' , q')
    s≡ =
      unique-splitting-⌈⌉L
        w
        {A = A}
        {B = B}
        w'
        (s , p , q)
        (s' , p' , q')

    12≡ : s' .fst .snd ≡ s .fst .snd
    12≡ = sym (cong snd s≡)

  -- Generalization of ⌈⌉-⊗&-distL⁻ where the left factor P of the
  -- first ⊗ is any grammar with a chosen morphism P ⊢ ⌈ w ⌉.  The
  -- output keeps P (not just ⌈ w ⌉), so we can refine the right
  -- factor while preserving the original prefix witness.
  ⌈⌉-prefix-push : ∀ {w} {P : Grammar ℓA} {A : Grammar ℓB} {B : Grammar ℓC}
    → (P ⊢ ⌈ w ⌉)
    → (P ⊗ A) & (⌈ w ⌉ ⊗ B) ⊢ P ⊗ (A & B)
  ⌈⌉-prefix-push {w = w} {A = A} {B = B} P→⌈⌉ w'
    ((s , p , q) , (s' , p' , q')) =
    s , (p , q , subst B 12≡ q')
    where
    pw : ⌈ w ⌉ (s .fst .fst)
    pw = P→⌈⌉ (s .fst .fst) p

    s≡ : same-splits
           {A = ⌈ w ⌉} {B = A} {C = ⌈ w ⌉} {D = B}
           {w = λ _ → w'}
           (s , pw , q) (s' , p' , q')
    s≡ = unique-splitting-⌈⌉L w {A = A} {B = B} w'
           (s , pw , q) (s' , p' , q')

    12≡ : s' .fst .snd ≡ s .fst .snd
    12≡ = sym (cong snd s≡)

  char-⊗&-distR⁻ :
    (A ⊗ char) & (B ⊗ char) ⊢ (A & B) ⊗ char
  char-⊗&-distR⁻ {A = A} {B = B} w ((s , p , q) , (s' , p' , q')) =
    s ,
    ((p ,
    subst B
      (cong (λ z → z .fst)
      (sym (unique-splitting-charR {A = A} {B = B}
        w (s , p , q) (s' , p' , q')))) p') , q)

  ⌈⌉-⊗&-distR⁻ :
    (A ⊗ ⌈ w ⌉) & (B ⊗ ⌈ w ⌉) ⊢ (A & B) ⊗ ⌈ w ⌉
  ⌈⌉-⊗&-distR⁻ {A = A} {w = w} {B = B} w' ((s , p , q) , (s' , p' , q')) =
    s , (p ,
      (subst B
        (cong fst (sym (
          unique-splitting-⌈⌉R
            w
            {A = A}
            {B = B}
            w'
            (s , p , q)
            (s' , p' , q')
        )))
        p')
      ) , q

  char-⊗&-distL⁻Eq :
    (char ⊗ A) & (char ⊗ B) ⊢ char ⊗ (A & B)
  char-⊗&-distL⁻Eq {B = B} w ((s , p , q) , (s' , p' , q')) =
    s , (p , q , Eq.transport B s≡-Eq q')
    where
    chain : p' .fst ∷ s' .fst .snd Eq.≡ p .fst ∷ s .fst .snd
    chain =
      Eq.ap (_++ s' .fst .snd) (Eq.sym (p' .snd))
      Eq.∙ Eq.sym (s' .snd)
      Eq.∙ s .snd
      Eq.∙ Eq.ap (_++ s .fst .snd) (p .snd)

    s≡-Eq : s' .fst .snd Eq.≡ s .fst .snd
    s≡-Eq = cons-inj₂Eq chain

  ⌈⌉-⊗&-distL⁻Eq :
    (⌈ w ⌉ ⊗ A) & (⌈ w ⌉ ⊗ B) ⊢ ⌈ w ⌉ ⊗ (A & B)
  ⌈⌉-⊗&-distL⁻Eq {w = w} {B = B} w' ((s , p , q) , (s' , p' , q')) =
    s , (p , q , Eq.transport B 12≡-Eq q')
    where
    w≡s11 : w Eq.≡ s .fst .fst
    w≡s11 = uniquely-supported-⌈⌉Eq w (s .fst .fst) p

    w≡s'11 : w Eq.≡ s' .fst .fst
    w≡s'11 = uniquely-supported-⌈⌉Eq w (s' .fst .fst) p'

    s11≡ : s .fst .fst Eq.≡ s' .fst .fst
    s11≡ = Eq.sym w≡s11 Eq.∙ w≡s'11

    chain : s .fst .fst ++ s' .fst .snd Eq.≡ s .fst .fst ++ s .fst .snd
    chain =
      Eq.ap (_++ s' .fst .snd) s11≡
      Eq.∙ Eq.sym (s' .snd)
      Eq.∙ s .snd

    12≡-Eq : s' .fst .snd Eq.≡ s .fst .snd
    12≡-Eq = ++-cancelˡEq (s .fst .fst) chain

  -- "Keep" variant: when the left factor carries an extra `P`-witness
  -- alongside the `⌈ w ⌉` prefix, the merged splitting preserves it.
  ⌈⌉-⊗&-keep-distL⁻Eq :
    ∀ {ℓP ℓQ ℓR} {P : Grammar ℓP} {Q : Grammar ℓQ} {R : Grammar ℓR}
      {w : String} →
    ((P & ⌈ w ⌉) ⊗ Q) & (⌈ w ⌉ ⊗ R) ⊢ (P & ⌈ w ⌉) ⊗ (Q & R)
  ⌈⌉-⊗&-keep-distL⁻Eq {R = R} {w = w} w'
    ((s , (pP , p⌈⌉) , q) , (s' , p' , q')) =
    s , ((pP , p⌈⌉) , q , Eq.transport R 12≡-Eq q')
    where
    w≡s11 : w Eq.≡ s .fst .fst
    w≡s11 = uniquely-supported-⌈⌉Eq w (s .fst .fst) p⌈⌉

    w≡s'11 : w Eq.≡ s' .fst .fst
    w≡s'11 = uniquely-supported-⌈⌉Eq w (s' .fst .fst) p'

    s11≡ : s .fst .fst Eq.≡ s' .fst .fst
    s11≡ = Eq.sym w≡s11 Eq.∙ w≡s'11

    chain : s .fst .fst ++ s' .fst .snd Eq.≡ s .fst .fst ++ s .fst .snd
    chain =
      Eq.ap (_++ s' .fst .snd) s11≡
      Eq.∙ Eq.sym (s' .snd)
      Eq.∙ s .snd

    12≡-Eq : s' .fst .snd Eq.≡ s .fst .snd
    12≡-Eq = ++-cancelˡEq (s .fst .fst) chain

  char-⊗&-distR⁻Eq :
    (A ⊗ char) & (B ⊗ char) ⊢ (A & B) ⊗ char
  char-⊗&-distR⁻Eq {A = A} {B = B} w ((s , p , q) , (s' , p' , q')) =
    s , (p , Eq.transport B 11≡-Eq p') , q
    where
    chain : s' .fst .fst ++ (q' .fst ∷ []) Eq.≡ s .fst .fst ++ (q .fst ∷ [])
    chain =
      Eq.ap (s' .fst .fst ++_) (Eq.sym (q' .snd))
      Eq.∙ Eq.sym (s' .snd)
      Eq.∙ s .snd
      Eq.∙ Eq.ap (s .fst .fst ++_) (q .snd)

    rev-chain :
      q' .fst ∷ List.rev (s' .fst .fst)
        Eq.≡ q .fst ∷ List.rev (s .fst .fst)
    rev-chain =
      Eq.sym (++-rev-Eq (s' .fst .fst) (q' .fst ∷ []))
      Eq.∙ Eq.ap List.rev chain
      Eq.∙ ++-rev-Eq (s .fst .fst) (q .fst ∷ [])

    rev≡ : List.rev (s' .fst .fst) Eq.≡ List.rev (s .fst .fst)
    rev≡ = cons-inj₂Eq rev-chain

    11≡-Eq : s' .fst .fst Eq.≡ s .fst .fst
    11≡-Eq =
      Eq.sym (rev-rev-Eq (s' .fst .fst))
      Eq.∙ Eq.ap List.rev rev≡
      Eq.∙ rev-rev-Eq (s .fst .fst)

  ⌈⌉-⊗&-distR⁻Eq :
    (A ⊗ ⌈ w ⌉) & (B ⊗ ⌈ w ⌉) ⊢ (A & B) ⊗ ⌈ w ⌉
  ⌈⌉-⊗&-distR⁻Eq {w = w} {B = B} w' ((s , p , q) , (s' , p' , q')) =
    s , (p , Eq.transport B 11≡-Eq p') , q
    where
    w≡s12 : w Eq.≡ s .fst .snd
    w≡s12 = uniquely-supported-⌈⌉Eq w (s .fst .snd) q

    w≡s'12 : w Eq.≡ s' .fst .snd
    w≡s'12 = uniquely-supported-⌈⌉Eq w (s' .fst .snd) q'

    s12≡ : s' .fst .snd Eq.≡ s .fst .snd
    s12≡ = Eq.sym w≡s'12 Eq.∙ w≡s12

    chain : s' .fst .fst ++ s .fst .snd Eq.≡ s .fst .fst ++ s .fst .snd
    chain =
      Eq.ap (s' .fst .fst ++_) (Eq.sym s12≡)
      Eq.∙ Eq.sym (s' .snd)
      Eq.∙ s .snd

    11≡-Eq : s' .fst .fst Eq.≡ s .fst .fst
    11≡-Eq = ++-cancelʳEq (s .fst .snd) chain

char-⊗&-distR≅ : (A & B) ⊗ char ≅ (A ⊗ char) & (B ⊗ char)
char-⊗&-distR≅ .fun = ⊗&-distR
char-⊗&-distR≅ .inv = char-⊗&-distR⁻
char-⊗&-distR≅ {A = A} {B = B} .sec = the-sec
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR π₁
    the-sec : char-⊗&-distR≅ {A = A} {B = B} .fun ∘g char-⊗&-distR≅ .inv ≡ id
    the-sec = funExt λ w → funExt λ p →
      ΣPathP (refl ,
        ΣPathP (
          (SplittingEq≡ (unique-splitting-charR w (p .fst) (p .snd))) ,
          ΣPathP (
            symP (transport-filler _ (fst (p .snd .snd))) ,
            isProp→PathP (λ i → unambiguous→isLang unambiguous-char _) _ _
          )
        )
      )
char-⊗&-distR≅ .ret = the-ret
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR π₁
    the-ret : char-⊗&-distR≅ {A = A} {B = B} .inv ∘g char-⊗&-distR≅ .fun ≡ id
    the-ret {B = B} = funExt λ w → funExt λ p →
      ΣPathP (
        refl ,
        (ΣPathP (
          (ΣPathP (
            refl ,
            symP (transport-filler _ (p .snd .fst .snd)
            ∙ cong (λ z → transport (λ i → B (z i)) (p .snd .fst .snd))
              (isSetString _ _ _ _))
          )) ,
          refl
        ))
      )

⌈⌉-⊗&-distR≅ : (A & B) ⊗ ⌈ w ⌉ ≅ (A ⊗ ⌈ w ⌉) & (B ⊗ ⌈ w ⌉)
⌈⌉-⊗&-distR≅ .fun = ⊗&-distR
⌈⌉-⊗&-distR≅ {w = w} .inv = ⌈⌉-⊗&-distR⁻ {w = w}
⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .sec = the-sec
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR π₁
    the-sec :
      ⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .fun
      ∘g ⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .inv ≡ id
    the-sec = funExt λ w' → funExt λ p →
      ΣPathP (
        refl ,
        (ΣPathP (
          SplittingEq≡
            (unique-splitting-⌈⌉R w w' (p .fst) (p .snd))
            ,
          ΣPathP (
            (symP (transport-filler _ (p .snd .snd .fst))) ,
            (isProp→PathP (λ i → isLang⌈⌉ w _) _ _)
          )
        ))
      )
⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .ret = the-ret
  where
  opaque
    unfolding _⊗_ ⊗-intro _&_ the-split literal char-⊗&-distL⁻ &-intro unique-splitting-charR π₁
    the-ret :
      ⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .inv
      ∘g ⌈⌉-⊗&-distR≅ {A = A} {B = B} {w = w} .fun ≡ id
    the-ret = funExt λ w → funExt λ p →
      ΣPathP (
        refl ,
        (ΣPathP (
          (ΣPathP (
            refl ,
            symP (transport-filler _ (p .snd .fst .snd)
            ∙ cong (λ z → transport (λ i → B (z i)) (p .snd .fst .snd))
              (isSetString _ _ _ _))
          )) ,
          refl
        ))
      )

opaque
  unfolding unique-splitting-charL unique-splitting-charR
            unique-splitting-literalL unique-splitting-literalR
            unique-splitting-⌈⌉L unique-splitting-⌈⌉R
            char-⊗&-distL⁻ char-⊗&-distR⁻
            ⌈⌉-⊗&-distL⁻ ⌈⌉-⊗&-distR⁻
            char-⊗&-distL⁻Eq char-⊗&-distR⁻Eq
            ⌈⌉-⊗&-distL⁻Eq ⌈⌉-⊗&-distR⁻Eq
            ⌈⌉-⊗&-keep-distL⁻Eq
  unfoldTinyDefs : Unit
  unfoldTinyDefs = tt
