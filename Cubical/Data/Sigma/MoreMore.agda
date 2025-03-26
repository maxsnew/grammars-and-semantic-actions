module Cubical.Data.Sigma.MoreMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit.Base
open import Cubical.Data.Empty.Base

open import Cubical.Relation.Nullary

open import Cubical.Reflection.StrictEquiv

open Iso

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
    C : (a : A) (b : B a) → Type ℓ

module _
  {A : I → Type ℓ}
  {B : (i : I) → A i → Type ℓ'}
  {C : (i : I) → (a : A i) → B i a → Type ℓ''}
  {x : Σ[ a ∈ A i0 ] Σ[ b ∈ B i0 a ] C i0 a b}
  {y : Σ[ a ∈ A i1 ] Σ[ b ∈ B i1 a ] C i1 a b}
  where

  ΣPathP2 :
    Σ[ p ∈ PathP A (fst x) (fst y) ]
    Σ[ p' ∈ PathP (λ i → B i (p i)) (x .snd .fst) (y .snd .fst) ]
      (PathP (λ i → C i (p i) (p' i)) (x .snd .snd) (y .snd .snd)) →
    PathP (λ i → Σ[ a ∈ A i ] Σ[ b ∈ B i a ] C i a b) x y
  ΣPathP2 eq = ΣPathP ((eq .fst) , (ΣPathP ((eq .snd .fst) , (eq .snd .snd))))

module _
  {A : I → Type ℓ}
  {B : (i : I) → A i → Type ℓ'}
  {C : (i : I) → (a : A i) → B i a → Type ℓ''}
  {D : (i : I) → (a : A i) → (b : B i a) → C i a b → Type ℓ'''}
  {x :
    Σ[ a ∈ A i0 ]
    Σ[ b ∈ B i0 a ]
    Σ[ c ∈ C i0 a b ]
      D i0 a b c
  }
  {y :
    Σ[ a ∈ A i1 ]
    Σ[ b ∈ B i1 a ]
    Σ[ c ∈ C i1 a b ]
      D i1 a b c
  }
  where

  ΣPathP3 :
    Σ[ p ∈ PathP A (fst x) (fst y) ]
    Σ[ p' ∈ PathP (λ i → B i (p i)) (x .snd .fst) (y .snd .fst) ]
    Σ[ p'' ∈ PathP (λ i → C i (p i) (p' i)) (x .snd .snd .fst) (y .snd .snd .fst) ]
      (PathP (λ i → D i (p i) (p' i) (p'' i)) (x .snd .snd .snd) (y .snd .snd .snd)) →
    PathP (λ i → Σ[ a ∈ A i ] Σ[ b ∈ B i a ] Σ[ c ∈ C i a b ] D i a b c) x y
  ΣPathP3 eq = ΣPathP ((eq .fst) , (ΣPathP2 (eq .snd)))

module _
  {A : I → Type ℓ}
  {B : (i : I) → A i → Type ℓ'}
  {C : (i : I) → (a : A i) → B i a → Type ℓ''}
  {D : (i : I) → (a : A i) → (b : B i a) → C i a b → Type ℓ'''}
  {E : (i : I) → (a : A i) → (b : B i a) → (c : C i a b) → D i a b c → Type ℓ''''}
  {x :
    Σ[ a ∈ A i0 ]
    Σ[ b ∈ B i0 a ]
    Σ[ c ∈ C i0 a b ]
    Σ[ d ∈ D i0 a b c ]
      E i0 a b c d
  }
  {y :
    Σ[ a ∈ A i1 ]
    Σ[ b ∈ B i1 a ]
    Σ[ c ∈ C i1 a b ]
    Σ[ d ∈ D i1 a b c ]
      E i1 a b c d
  }
  where

  ΣPathP4 :
    Σ[ p ∈ PathP A (fst x) (fst y) ]
    Σ[ p' ∈ PathP (λ i → B i (p i)) (x .snd .fst) (y .snd .fst) ]
    Σ[ p'' ∈ PathP (λ i → C i (p i) (p' i)) (x .snd .snd .fst) (y .snd .snd .fst) ]
    Σ[ p''' ∈ PathP (λ i → D i (p i) (p' i) (p'' i)) (x .snd .snd .snd .fst) (y .snd .snd .snd .fst) ]
      (PathP (λ i → E i (p i) (p' i) (p'' i) (p''' i)) (x .snd .snd .snd .snd) (y .snd .snd .snd .snd)) →
    PathP (λ i → Σ[ a ∈ A i ] Σ[ b ∈ B i a ] Σ[ c ∈ C i a b ] Σ[ d ∈ D i a b c ] E i a b c d) x y
  ΣPathP4 eq = ΣPathP ((eq .fst) , (ΣPathP3 (eq .snd)))

module _
  {A : I → Type ℓ}
  {B : (i : I) → A i → Type ℓ'}
  {C : (i : I) → (a : A i) → B i a → Type ℓ''}
  {D : (i : I) → (a : A i) → (b : B i a) → C i a b → Type ℓ'''}
  {E : (i : I) → (a : A i) → (b : B i a) → (c : C i a b) → D i a b c → Type ℓ''''}
  {F : (i : I) → (a : A i) → (b : B i a) → (c : C i a b) → (d : D i a b c) → E i a b c d → Type ℓ'''''}
  {x :
    Σ[ a ∈ A i0 ]
    Σ[ b ∈ B i0 a ]
    Σ[ c ∈ C i0 a b ]
    Σ[ d ∈ D i0 a b c ]
    Σ[ e ∈ E i0 a b c d ]
      F i0 a b c d e
  }
  {y :
    Σ[ a ∈ A i1 ]
    Σ[ b ∈ B i1 a ]
    Σ[ c ∈ C i1 a b ]
    Σ[ d ∈ D i1 a b c ]
    Σ[ e ∈ E i1 a b c d ]
      F i1 a b c d e
  }
  where

  ΣPathP5 :
    Σ[ p ∈ PathP A (fst x) (fst y) ]
    Σ[ p' ∈ PathP (λ i → B i (p i)) (x .snd .fst) (y .snd .fst) ]
    Σ[ p'' ∈ PathP (λ i → C i (p i) (p' i)) (x .snd .snd .fst) (y .snd .snd .fst) ]
    Σ[ p''' ∈ PathP (λ i → D i (p i) (p' i) (p'' i)) (x .snd .snd .snd .fst) (y .snd .snd .snd .fst) ]
    Σ[ p'''' ∈ PathP (λ i → E i (p i) (p' i) (p'' i) (p''' i)) (x .snd .snd .snd .snd .fst) (y .snd .snd .snd .snd .fst) ]
      (PathP (λ i → F i (p i) (p' i) (p'' i) (p''' i) (p'''' i)) (x .snd .snd .snd .snd .snd) (y .snd .snd .snd .snd .snd)) →
    PathP (λ i → Σ[ a ∈ A i ] Σ[ b ∈ B i a ] Σ[ c ∈ C i a b ] Σ[ d ∈ D i a b c ] Σ[ e ∈ E i a b c d ] F i a b c d e) x y
  ΣPathP5 eq = ΣPathP ((eq .fst) , (ΣPathP4 (eq .snd)))
