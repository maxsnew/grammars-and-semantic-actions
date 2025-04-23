open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Grammar.Epsilon.Base Alphabet
open import Grammar.LinearProduct.Interface Alphabet
import Grammar.LinearProduct.AsEquality.Base Alphabet as asEquality
import Grammar.LinearProduct.AsPath.Base Alphabet as asPath

open εStr
open ⊗Defs
open ⊗Equalities

module ⊗AsEquality where
  module Defs where
    instance
      ⊗AsEqualityDefs : ⊗Defs
      ⊗AsEqualityDefs ._⊗_ = asEquality._⊗_
      ⊗AsEqualityDefs .⊗-intro = asEquality.⊗-intro
      ⊗AsEqualityDefs .⊗-unit-r = asEquality.⊗-unit-r
      ⊗AsEqualityDefs .⊗-unit-r⁻ = asEquality.⊗-unit-r⁻
      ⊗AsEqualityDefs .⊗-unit-l = asEquality.⊗-unit-l
      ⊗AsEqualityDefs .⊗-unit-l⁻ = asEquality.⊗-unit-l⁻
      ⊗AsEqualityDefs .⊗-assoc = asEquality.⊗-assoc
      ⊗AsEqualityDefs .⊗-assoc⁻ = asEquality.⊗-assoc⁻
      ⊗AsEqualityDefs .has-split = asEquality.has-split
      ⊗AsEqualityDefs .isProp-has-split = asEquality.isProp-has-split
      ⊗AsEqualityDefs .the-split = asEquality.the-split
      ⊗AsEqualityDefs .same-splits {A = A} {B = B} {C = C} {D = D} {w = w} =
        asEquality.same-splits {A = A} {B} {C} {D} {w}
      ⊗AsEqualityDefs .same-parses {A = A} {B = B} {w = w} =
        asEquality.same-parses {A = A} {B} {w}
      ⊗AsEqualityDefs .⊗PathP = asEquality.⊗PathP
      ⊗AsEqualityDefs .⊗≡ = asEquality.⊗≡

      @0 ⊗AsEqualityEqs : ⊗Equalities
      ⊗AsEqualityEqs .isSetGrammar⊗ = asEquality.isSetGrammar⊗
      ⊗AsEqualityEqs .id,⊗id≡id = asEquality.id,⊗id≡id
      ⊗AsEqualityEqs .⊗-intro⊗-intro = asEquality.⊗-intro⊗-intro
      ⊗AsEqualityEqs .⊗-unit-rr⁻ = {!asEquality.⊗-unit-rr⁻!}
      ⊗AsEqualityEqs .⊗-unit-r⁻r = {!asEquality.⊗-unit-r⁻r!}
      ⊗AsEqualityEqs .⊗-unit-ll⁻ = asEquality.⊗-unit-ll⁻
      ⊗AsEqualityEqs .⊗-unit-l⁻l = asEquality.⊗-unit-l⁻l
      ⊗AsEqualityEqs .⊗-unit-rl⁻ = asEquality.⊗-unit-rl⁻
      ⊗AsEqualityEqs .⊗-unit-lr⁻ = asEquality.⊗-unit-lr⁻
      ⊗AsEqualityEqs .⊗-unit-r⊗-intro = {!asEquality.⊗-unit-r⊗-intro!}
      ⊗AsEqualityEqs .⊗-unit-r⁻⊗-intro = asEquality.⊗-unit-r⁻⊗-intro
      ⊗AsEqualityEqs .⊗-unit-l⊗-intro = {!asEquality.⊗-unit-l⊗-intro!}
      ⊗AsEqualityEqs .⊗-unit-l⁻⊗-intro = asEquality.⊗-unit-l⁻⊗-intro
      ⊗AsEqualityEqs .⊗-assoc∘⊗-assoc⁻≡id = {!asEquality.⊗-assoc∘⊗-assoc⁻≡id!}
      ⊗AsEqualityEqs .⊗-assoc⁻∘⊗-assoc≡id = {!asEquality.⊗-assoc⁻∘⊗-assoc≡id!}
      ⊗AsEqualityEqs .⊗-assoc⁻⊗-intro = {!asEquality.⊗-assoc⁻⊗-intro!}
      ⊗AsEqualityEqs .⊗-assoc⊗-intro = {!asEquality.⊗-assoc⊗-intro!}
      ⊗AsEqualityEqs .⊗-assoc⁻⊗-unit-r⁻ = {!asEquality.⊗-assoc⁻⊗-unit-r⁻!}
      ⊗AsEqualityEqs .⊗-assoc⊗-unit-l⁻ = {!asEquality.⊗-assoc⊗-unit-l⁻!}
      ⊗AsEqualityEqs .⊗-triangle = {!asEquality.⊗-triangle!}
      ⊗AsEqualityEqs .⊗-pentagon = {!asEquality.⊗-pentagon!}

module @0 ⊗AsPath where
  module Defs where
    instance
      ⊗AsPathDefs : ⊗Defs
      ⊗AsPathDefs ._⊗_ = asPath._⊗_
      ⊗AsPathDefs .⊗-intro = asPath.⊗-intro
      ⊗AsPathDefs .⊗-unit-r = asPath.⊗-unit-r
      ⊗AsPathDefs .⊗-unit-r⁻ = asPath.⊗-unit-r⁻
      ⊗AsPathDefs .⊗-unit-l = asPath.⊗-unit-l
      ⊗AsPathDefs .⊗-unit-l⁻ = asPath.⊗-unit-l⁻
      ⊗AsPathDefs .⊗-assoc = asPath.⊗-assoc
      ⊗AsPathDefs .⊗-assoc⁻ = asPath.⊗-assoc⁻
      ⊗AsPathDefs .has-split = asPath.has-split
      ⊗AsPathDefs .isProp-has-split = asPath.isProp-has-split
      ⊗AsPathDefs .the-split = asPath.the-split
      ⊗AsPathDefs .same-splits {A = A} {B = B} {C = C} {D = D} {w = w} =
        asPath.same-splits {A = A} {B} {C} {D} {w}
      ⊗AsPathDefs .same-parses {A = A} {B = B} {w = w} =
        asPath.same-parses {A = A} {B} {w}
      ⊗AsPathDefs .⊗PathP = asPath.⊗PathP
      ⊗AsPathDefs .⊗≡ = asPath.⊗≡

      @0 ⊗AsPathEqs : ⊗Equalities
      ⊗AsPathEqs .isSetGrammar⊗ = asPath.isSetGrammar⊗
      ⊗AsPathEqs .id,⊗id≡id = asPath.id,⊗id≡id
      ⊗AsPathEqs .⊗-intro⊗-intro = asPath.⊗-intro⊗-intro
      ⊗AsPathEqs .⊗-unit-rr⁻ = {!asPath.⊗-unit-rr⁻!}
      ⊗AsPathEqs .⊗-unit-r⁻r = {!asPath.⊗-unit-r⁻r!}
      ⊗AsPathEqs .⊗-unit-ll⁻ = asPath.⊗-unit-ll⁻
      ⊗AsPathEqs .⊗-unit-l⁻l = asPath.⊗-unit-l⁻l
      ⊗AsPathEqs .⊗-unit-rl⁻ = asPath.⊗-unit-rl⁻
      ⊗AsPathEqs .⊗-unit-lr⁻ = asPath.⊗-unit-lr⁻
      ⊗AsPathEqs .⊗-unit-r⊗-intro = {!asPath.⊗-unit-r⊗-intro!}
      ⊗AsPathEqs .⊗-unit-r⁻⊗-intro = asPath.⊗-unit-r⁻⊗-intro
      ⊗AsPathEqs .⊗-unit-l⊗-intro = {!asPath.⊗-unit-l⊗-intro!}
      ⊗AsPathEqs .⊗-unit-l⁻⊗-intro = asPath.⊗-unit-l⁻⊗-intro
      ⊗AsPathEqs .⊗-assoc∘⊗-assoc⁻≡id = {!asPath.⊗-assoc∘⊗-assoc⁻≡id!}
      ⊗AsPathEqs .⊗-assoc⁻∘⊗-assoc≡id = {!asPath.⊗-assoc⁻∘⊗-assoc≡id!}
      ⊗AsPathEqs .⊗-assoc⁻⊗-intro = {!asPath.⊗-assoc⁻⊗-intro!}
      ⊗AsPathEqs .⊗-assoc⊗-intro = {!asPath.⊗-assoc⊗-intro!}
      ⊗AsPathEqs .⊗-assoc⁻⊗-unit-r⁻ = {!asPath.⊗-assoc⁻⊗-unit-r⁻!}
      ⊗AsPathEqs .⊗-assoc⊗-unit-l⁻ = {!asPath.⊗-assoc⊗-unit-l⁻!}
      ⊗AsPathEqs .⊗-triangle = {!asPath.⊗-triangle!}
      ⊗AsPathEqs .⊗-pentagon = {!asPath.⊗-pentagon!}
