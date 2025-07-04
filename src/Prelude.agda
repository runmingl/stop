open import Algebra.Core
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Level
open import Data.Product

module Prelude where

postulate 
  funext : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

cong₃ : ∀ {ℓ : Level} {A B C D : Set ℓ} (f : A → B → C → D) {x y u v i j} → x ≡ y → u ≡ v → i ≡ j → f x u i ≡ f y v j
cong₃ f Eq.refl Eq.refl Eq.refl = Eq.refl

record Monoid ℓ : Set (suc ℓ) where
  infixl 7 _∙_
  field 
    Carrier                           : Set ℓ
    _∙_                               : Op₂ Carrier
    0#                                : Carrier
    1#                                : Carrier
    isMonoid                          : IsMonoid _≡_ _∙_ 1#

  open IsMonoid isMonoid public hiding (refl; sym; trans)

infix 1 _⇔_
_⇔_ : {ℓ : Level} → Set ℓ → Set ℓ → Set ℓ
_⇔_ A B = (A → B) × (B → A)
