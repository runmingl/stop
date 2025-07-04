open import Prelude 

open import Level 

module Language.SmallStep {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

private
  variable
    τ σ : Type

infix 2 _↦_↝_
data _↦_↝_ : · ⊢ τ → · ⊢ τ → Effect → Set ℓ where
  se-suc : {e e' : · ⊢ Nat} {a : Effect} →
      e ↦ e' ↝ a 
    ------------------------
    → `suc e ↦ `suc e' ↝ a

  se-case : {e e' : · ⊢ Nat} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a : Effect} →
      e ↦ e' ↝ a 
    ------------------------
    → `case e e₁ e₂ ↦ `case e' e₁ e₂ ↝ a

  se-case-z : {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} →

    ------------------------
    `case `zero e₁ e₂ ↦ e₁ ↝ 1#

  se-case-s : {v : · ⊢ Nat} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} →
      v val
    ------------------------
    → `case (`suc v) e₁ e₂ ↦ e₂ [ v ] ↝ 1#

  se-app : {e₁ e₁' : · ⊢ τ ⇒ σ} {e₂ : · ⊢ τ} {a : Effect} →
      e₁ ↦ e₁' ↝ a 
    ------------------------
    → `app e₁ e₂ ↦ `app e₁' e₂ ↝ a

  se-app₁ : {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ e₂' : · ⊢ τ} {a : Effect} →
      e₂ ↦ e₂' ↝ a
    ------------------------
    → `app (`fun e) e₂ ↦ `app (`fun e) e₂' ↝ a

  se-app₂ : {e : · # τ ⇒ σ # τ ⊢ σ} {v : · ⊢ τ} →
      v val
    ------------------------
    → `app (`fun e) v ↦ e [ (`fun e) ][ v ] ↝ 1#

  se-eff : {e : · ⊢ τ} {a : Effect} →
     
    ------------------------
    `eff a e ↦ e ↝ a  

infix 2 _↦*_↝_
data _↦*_↝_ : · ⊢ τ → · ⊢ τ → Effect → Set ℓ where
  ↦*-refl : {e : · ⊢ τ} → 
    
    ------------------------
    e ↦* e ↝ 1#

  ↦*-step : {e e' e'' : · ⊢ τ} {a b : Effect} → 
      e ↦ e' ↝ a 
    → e' ↦* e'' ↝ b 
    ------------------------
    → e ↦* e'' ↝ a ∙ b

↦*-trans : {e e' e'' : · ⊢ τ} {a b : Effect} → 
    e ↦* e' ↝ a
  → e' ↦* e'' ↝ b
  ------------------------
  → e ↦* e'' ↝ a ∙ b
↦*-trans {b = b} ↦*-refl step rewrite identityˡ b = step
↦*-trans {b = c} (↦*-step {a = a} {b = b} step₁ step₂) step rewrite assoc a b c = 
    ↦*-step step₁ (↦*-trans step₂ step)

compatible : {p : · ⊢ τ → · ⊢ σ}
  → ({e e' : · ⊢ τ} {a : Effect} → e ↦ e' ↝ a → p e ↦ p e' ↝ a)
  → {e e' : · ⊢ τ} {a : Effect} → e ↦* e' ↝ a → p e ↦* p e' ↝ a 
compatible alift ↦*-refl       = ↦*-refl
compatible alift (↦*-step x s) = ↦*-step (alift x) (compatible alift s)
