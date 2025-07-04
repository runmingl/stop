open import Prelude 

open import Level 

module Language.BigStop {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

private
  variable
    τ σ : Type

infix 2 _↧_↝_
data _↧_↝_ : · ⊢ τ → · ⊢ τ → Effect → Set ℓ where
  ste-zero : 

    ------------------------
    `zero ↧ `zero ↝ 1# 

  ste-suc : {e e' : · ⊢ Nat} {a : Effect} →
      e ↧ e' ↝ a 
    ------------------------
    → `suc e ↧ `suc e' ↝ a

  ste-fun : {e : · # τ ⇒ σ # τ ⊢ σ} →
    
    ------------------------
    `fun e ↧ `fun e ↝ 1#

  ste-app-seq₁ : {e₁ e₁' : · ⊢ τ ⇒ σ} {e₂ : · ⊢ τ} {a : Effect} →
      e₁ ↧ e₁' ↝ a
    ------------------------
    → `app e₁ e₂ ↧ `app e₁' e₂ ↝ a 

  ste-app-seq₂ : {e₁ : · ⊢ τ ⇒ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ e₂' : · ⊢ τ} {a b : Effect} →
      e₁ ↧ `fun e ↝ a
    → e₂ ↧ e₂' ↝ b
    ------------------------
    → `app e₁ e₂ ↧ `app (`fun e) e₂' ↝ a ∙ b

  ste-app : {e₁ : · ⊢ τ ⇒ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ v₂ : · ⊢ τ} {e' : · ⊢ σ} {a b c : Effect} →
      e₁ ↧ `fun e ↝ a
    → e₂ ↧ v₂ ↝ b
    → v₂ val
    → e [ (`fun e) ][ v₂ ] ↧ e' ↝ c
    ------------------------
    → `app e₁ e₂ ↧ e' ↝ a ∙ b ∙ c  

  ste-case-seq : {e e' : · ⊢ Nat} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a : Effect} →
      e ↧ e' ↝ a
    ------------------------
    → `case e e₁ e₂ ↧ `case e' e₁ e₂ ↝ a

  ste-case-z : {e : · ⊢ Nat} {e₁ e₁' : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a b : Effect} →
      e ↧ `zero ↝ a 
    → e₁ ↧ e₁' ↝ b
    ------------------------
    → `case e e₁ e₂ ↧ e₁' ↝ a ∙ b

  ste-case-s : {e v : · ⊢ Nat} {e₁ e₂' : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a b : Effect} →
      e ↧ `suc v ↝ a
    → v val 
    → e₂ [ v ] ↧ e₂' ↝ b
    ------------------------
    → `case e e₁ e₂ ↧ e₂' ↝ a ∙ b

  ste-eff : {e e' : · ⊢ τ} {a b : Effect} →
      e ↧ e' ↝ b
    ------------------------
    → `eff a e ↧ e' ↝ a ∙ b 

  ste-stop : {e : · ⊢ τ} →

    ------------------------
    e ↧ e ↝ 1#
