open import Algebra.Core
open import Algebra.Structures
open import Algebra.Definitions
open import Algebra.Bundles
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)
open import Level
open import Data.Unit
open import Data.Product

module Prelude where

postulate 
  funext : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

cong₃ : ∀ {ℓ : Level} {A B C D : Set ℓ} (f : A → B → C → D) {x y u v i j} → x ≡ y → u ≡ v → i ≡ j → f x u i ≡ f y v j
cong₃ f Eq.refl Eq.refl Eq.refl = Eq.refl

record MonoidWithLeftZero ℓ : Set (suc ℓ) where
  infixl 7 _∙_
  field 
    Carrier                           : Set ℓ
    _∙_                               : Op₂ Carrier
    0#                                : Carrier
    1#                                : Carrier
    isMonoid                          : IsMonoid _≡_ _∙_ 1#
    isLeftZero                        : LeftZero _≡_ 0# _∙_

  open IsMonoid isMonoid public

  monoidInstance : Monoid ℓ ℓ
  monoidInstance = record { Carrier = Carrier ; _≈_ = _≡_ ; _∙_ = _∙_ ; ε = 1# ; isMonoid = isMonoid }

trivialMonoidWithLeftZero : MonoidWithLeftZero zero
trivialMonoidWithLeftZero = record
  { Carrier = ⊤
  ; _∙_ = λ _ _ → tt
  ; 0# = tt
  ; 1# = tt
  ; isMonoid = record { 
        isSemigroup = record { 
            isMagma = record { 
                isEquivalence = Eq.isEquivalence 
              ; ∙-cong = λ _ _ → Eq.refl 
            } 
            ; assoc = λ _ _ _ → Eq.refl 
        } 
        ; identity = (λ { tt → Eq.refl }) , λ { tt → Eq.refl }
    } 
  ; isLeftZero = λ _ → Eq.refl
  }

infix 1 _⇔_
_⇔_ : {ℓ : Level} → Set ℓ → Set ℓ → Set ℓ
_⇔_ A B = (A → B) × (B → A)
