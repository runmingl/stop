open import Algebra.Core
open import Algebra.Structures
open import Algebra.Definitions
open import Algebra.Bundles
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)
open import Level

module Prelude where

record MonoidWithLeftZero c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  field 
    Carrier                           : Set c
    _∙_                               : Op₂ Carrier
    0#                                : Carrier
    1#                                : Carrier
    isMonoid                          : IsMonoid _≡_ _∙_ 1#
    isLeftZero                        : LeftZero _≡_ 0# _∙_

  open IsMonoid isMonoid public

  monoidInstance : Monoid c c
  monoidInstance = record { Carrier = Carrier ; _≈_ = _≡_ ; _∙_ = _∙_ ; ε = 1# ; isMonoid = isMonoid }

