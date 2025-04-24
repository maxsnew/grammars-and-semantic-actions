{-# OPTIONS --safe #-}
module Cubical.Data.Equality.Conversion.More where

open import Cubical.Foundations.Prelude
  hiding (_≡_ ; step-≡ ; _∎ ; isPropIsContr)
  renaming ( refl      to reflPath
           ; transport to transportPath
           ; J         to JPath
           ; JRefl     to JPathRefl
           ; sym       to symPath
           ; _∙_       to compPath
           ; cong      to congPath
           ; subst     to substPath
           ; substRefl to substPathReflPath
           ; funExt    to funExtPath
           ; isContr   to isContrPath
           ; isProp    to isPropPath
           )
open import Cubical.Foundations.Equiv
  renaming ( fiber     to fiberPath
           ; isEquiv   to isEquivPath
           ; _≃_       to EquivPath
           ; equivFun  to equivFunPath
           ; isPropIsEquiv to isPropIsEquivPath
           )
  hiding   ( equivCtr
           ; equivIsEquiv )
open import Cubical.Foundations.Isomorphism
  using ()
  renaming ( Iso to IsoPath
           ; iso to isoPath
           ; isoToPath to isoPathToPath
           ; isoToEquiv to isoPathToEquivPath
           )

open import Cubical.Data.Equality.Base
open import Cubical.Data.Equality.Conversion

private
 variable
  a b ℓ ℓ' : Level
  A : Type a
  B : Type b
  x y z : A

path≡Eq' : {A : Type ℓ} {a a' : A} → Path _ (Path _ a a') (a ≡ a')
path≡Eq' = isoPathToPath (isoPath pathToEq eqToPath pathToEq-eqToPath eqToPath-pathToEq)
