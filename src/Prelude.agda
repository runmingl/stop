open import Algebra.Core
open import Algebra.Structures
open import Algebra.Bundles renaming (Monoid to MonoidBundle)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Level
open import Data.Product

module Prelude where

record Monoid ℓ : Set (suc ℓ) where
  infixl 7 _∙_
  field 
    Carrier                           : Set ℓ
    _∙_                               : Op₂ Carrier
    1#                                : Carrier
    isMonoid                          : IsMonoid _≡_ _∙_ 1#

  open IsMonoid isMonoid public hiding (refl; sym; trans)

  monoidInstance : MonoidBundle _ _ 
  monoidInstance .MonoidBundle.Carrier = Carrier
  monoidInstance .MonoidBundle._≈_ = _≡_
  monoidInstance .MonoidBundle._∙_ = _∙_
  monoidInstance .MonoidBundle.ε = 1#
  monoidInstance .MonoidBundle.isMonoid = isMonoid

infix 1 _⇔_
_⇔_ : {ℓ : Level} → Set ℓ → Set ℓ → Set ℓ
_⇔_ A B = (A → B) × (B → A)


module MonoidArithmetic {ℓ : Level} (monoid : Monoid ℓ) where 
  
  open Monoid monoid
  open import Tactic.MonoidSolver using (solve)
  
  arithmetic₁ : (a b c : Carrier) → a ∙ (b ∙ c) ≡ a ∙ b ∙ c
  arithmetic₁ a b c = solve (Monoid.monoidInstance monoid)

  arithmetic₂ : (a b c d : Carrier) → a ∙ (b ∙ c ∙ d) ≡ a ∙ b ∙ c ∙ d
  arithmetic₂ a b c d = solve (Monoid.monoidInstance monoid)

  arithmetic₃ : (a b c : Carrier) → a ∙ (1# ∙ b ∙ c) ≡ 1# ∙ (a ∙ b) ∙ c
  arithmetic₃ a b c = solve (Monoid.monoidInstance monoid)

  arithmetic₄ : (a : Carrier) → 1# ∙ a ≡ 1# ∙ 1# ∙ a
  arithmetic₄ a = solve (Monoid.monoidInstance monoid)

  arithmetic₅ : (a : Carrier) → a ∙ 1# ≡ 1# ∙ (a ∙ 1#)
  arithmetic₅ a = solve (Monoid.monoidInstance monoid)

  arithmetic₆ : (a b : Carrier) → a ∙ (1# ∙ b) ≡ 1# ∙ (a ∙ b)
  arithmetic₆ a b = solve (Monoid.monoidInstance monoid)

  arithmetic₇ : (a b : Carrier) → a ∙ b ≡ 1# ∙ a ∙ (1# ∙ b)
  arithmetic₇ a b = solve (Monoid.monoidInstance monoid)

  arithmetic₈ : (a b c : Carrier) → a ∙ b ∙ c ≡ 1# ∙ a ∙ (1# ∙ b ∙ (1# ∙ c)) 
  arithmetic₈ a b c = solve (Monoid.monoidInstance monoid)

  arithmetic₉ : (a : Carrier) → 1# ∙ a ∙ (1# ∙ 1#) ≡ a 
  arithmetic₉ a = solve (Monoid.monoidInstance monoid)

  arithmetic₁₀ : (a b c : Carrier) → 1# ∙ (a ∙ b) ∙ c ≡ a ∙ (b ∙ (1# ∙ c))
  arithmetic₁₀ a b c = solve (Monoid.monoidInstance monoid)

  arithmetic₁₁ : (a b c d : Carrier) → a ∙ b ∙ c ∙ d ≡ a ∙ (b ∙ (c ∙ (1# ∙ d)))
  arithmetic₁₁ a b c d = solve (Monoid.monoidInstance monoid)

  arithmetic₁₂ : (a b c : Carrier) → a ∙ b ∙ c ≡ a ∙ (b ∙ (1# ∙ c))
  arithmetic₁₂ a b c = solve (Monoid.monoidInstance monoid)
