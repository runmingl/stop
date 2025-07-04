open import Prelude 

open import Level 

module Language.BigStep {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

private
  variable
    τ σ : Type

infix 2 _⇓_↝_
data _⇓_↝_ : · ⊢ τ → · ⊢ τ → Effect → Set ℓ where
  be-zero : 

    ------------------------
    `zero ⇓ `zero ↝ 1# 

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

  be-fun : {e : · # τ ⇒ σ # τ ⊢ σ} →
    
    ------------------------
    `fun e ⇓ `fun e ↝ 1#

  be-app : {e₁ : · ⊢ τ ⇒ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ v : · ⊢ τ} {v₁ : · ⊢ σ} {a b c : Effect} →
      e₁ ⇓ `fun e ↝ a
    → e₂ ⇓ v ↝ b
    → e [ (`fun e) ][ v ] ⇓ v₁ ↝ c
    ------------------------
    → `app e₁ e₂ ⇓ v₁ ↝ a ∙ b ∙ c  

  be-eff : {e v : · ⊢ τ} {a b : Effect} →
      e ⇓ v ↝ b
    ------------------------
    → `eff a e ⇓ v ↝ a ∙ b 

⇓-val : {e v : · ⊢ τ} {a : Effect} → 
    e ⇓ v ↝ a 
  ------------------------
  → v val
⇓-val (be-zero)                     = v-zero
⇓-val (be-suc e⇓v↝a)                = v-suc (⇓-val e⇓v↝a)
⇓-val (be-case-z _ e₁⇓v↝b)          = ⇓-val e₁⇓v↝b
⇓-val (be-case-s _ e₂[v₁]⇓v↝b)      = ⇓-val e₂[v₁]⇓v↝b
⇓-val (be-fun)                      = v-fun
⇓-val (be-app _ _ e[`fune][v₁]⇓v↝c) = ⇓-val e[`fune][v₁]⇓v↝c
⇓-val (be-eff e⇓v↝a)                = ⇓-val e⇓v↝a

v⇓v : {v : · ⊢ τ} → 
    v val 
  ------------------------
  → v ⇓ v ↝ 1#
v⇓v v-zero        = be-zero
v⇓v (v-suc v-val) = be-suc (v⇓v v-val)
v⇓v v-fun         = be-fun