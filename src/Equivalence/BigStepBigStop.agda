{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (cong; _≡_; module ≡-Reasoning)

module Equivalence.BigStepBigStop {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid
open import Substitution monoid

open import BigStep monoid 
open import BigStop monoid renaming (_⇓_↝_ to _↧_↝_)

private
  variable
    τ σ : Type

⇓→↧ : {e v : · ⊢ τ} {a : Effect} → 
    e ⇓ v ↝ a 
  ------------------------
  → e ↧ v ↝ a
⇓→↧ be-zero               = ste-zero
⇓→↧ (be-suc e⇓v)          = ste-suc (⇓→↧ e⇓v)
⇓→↧ (be-case-z e⇓z e₁⇓v)  = ste-case-z (⇓→↧ e⇓z) (⇓→↧ e₁⇓v)
⇓→↧ (be-case-s e⇓s e₂⇓v) with ⇓-val e⇓s 
... | v-suc v-val         = ste-case-s (⇓→↧ e⇓s) v-val (⇓→↧ e₂⇓v)
⇓→↧ be-fun                = ste-fun
⇓→↧ (be-app e⇓f e₂⇓v e⇓v) = ste-app (⇓→↧ e⇓f) (⇓→↧ e₂⇓v) (⇓-val e₂⇓v) (⇓→↧ e⇓v)
⇓→↧ (be-eff e⇓v)          = ste-eff (⇓→↧ e⇓v)

↧→⇓ : {e v : · ⊢ τ} {a : Effect} → 
    e ↧ v ↝ a
  → v val 
  ------------------------
  → e ⇓ v ↝ a
↧→⇓ ste-zero v-val                        = be-zero
↧→⇓ (ste-suc e↧v) (v-suc v-val)           = be-suc (↧→⇓ e↧v v-val)
↧→⇓ ste-fun v-val                         = be-fun
↧→⇓ (ste-app e₁↧f e₂↧v₂ v₂-val e↧v) v-val = be-app (↧→⇓ e₁↧f v-fun) (↧→⇓ e₂↧v₂ v₂-val) (↧→⇓ e↧v v-val)
↧→⇓ (ste-case-z e↧z e₁↧v) v-val           = be-case-z (↧→⇓ e↧z v-zero) (↧→⇓ e₁↧v v-val)
↧→⇓ (ste-case-s e↧s sv-val e₂↧v) v-val    = be-case-s (↧→⇓ e↧s (v-suc sv-val)) (↧→⇓ e₂↧v v-val)
↧→⇓ (ste-eff e↧v) v-val                   = be-eff (↧→⇓ e↧v v-val)
↧→⇓ ste-stop v-val                        = v⇓v v-val

⇓⇔↧ : {e v : · ⊢ τ} {a : Effect} → 
    e ⇓ v ↝ a 
  ------------------------
  ⇔ 
  ------------------------
    (v val) × (e ↧ v ↝ a)
⇓⇔↧ = (λ e⇓v → ⇓-val e⇓v , ⇓→↧ e⇓v) , λ (v-val , e↧v) → ↧→⇓ e↧v v-val
