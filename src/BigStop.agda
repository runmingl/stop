{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude 

open import Level 

module BigStop {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid
open import Substitution monoid

private
  variable
    τ σ : Type

infix 2 _⇓_↝_
data _⇓_↝_ : · ⊢ τ → · ⊢ τ → Effect → Set ℓ where
  be-suc : {e v : · ⊢ Nat} {a : Effect} →
      e ⇓ v ↝ a 
    ------------------------
    → `suc e ⇓ `suc v ↝ a

  be-case-z : {e : · ⊢ Nat} {e₁ v₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a b : Effect} →
      e ⇓ `zero ↝ a 
    → e₁ ⇓ v₁ ↝ b
    ------------------------
    → `case e e₁ e₂ ⇓ v₁ ↝ a ∙ b

  be-case-s : {e v : · ⊢ Nat} {e₁ v₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a b : Effect} →
      e ⇓ `suc v ↝ a
    → e₂ [ v ] ⇓ v₁ ↝ b
    ------------------------
    → `case e e₁ e₂ ⇓ v₁ ↝ a ∙ b

  be-app : {e₁ : · ⊢ τ ⇒ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ v : · ⊢ τ} {v₁ : · ⊢ σ} {a b c : Effect} →
      e₁ ⇓ `fun e ↝ a
    → e₂ ⇓ v ↝ b
    → e [ (`fun e) ][ v ] ⇓ v₁ ↝ c
    ------------------------
    → `app e₁ e₂ ⇓ v₁ ↝ a ∙ b ∙ c  

  be-eff : {e v : · ⊢ τ} {a b : Effect} →
      e ⇓ v ↝ a
    ------------------------
    → `eff b e ⇓ v ↝ a ∙ b 

  be-val : {e v : · ⊢ τ} {a : Effect} → 
      v val
    ------------------------
    → v ⇓ v ↝ 1#

  ste-stop : {e : · ⊢ τ} →

    ------------------------
    e ⇓ e ↝ 1#
