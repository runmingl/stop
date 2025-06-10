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
  ste-zero : 

    ------------------------
    `zero ⇓ `zero ↝ 1# 

  ste-suc-seq : {e e' : · ⊢ Nat} {a : Effect} →
      e ⇓ e' ↝ a 
    ------------------------
    → `suc e ⇓ `suc e' ↝ a

  ste-suc-val : {e v : · ⊢ Nat} {a : Effect} →
      e ⇓ v ↝ a 
    → v val 
    ------------------------
    → `suc e ⇓ `suc v ↝ a

  ste-fun : {e : · # τ ⇒ σ # τ ⊢ σ} →
    
    ------------------------
    `fun e ⇓ `fun e ↝ 1#

  ste-case-seq : {e e' : · ⊢ Nat} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a : Effect} →
      e ⇓ e' ↝ a
    ------------------------
    → `case e e₁ e₂ ⇓ `case e' e₁ e₂ ↝ a
  
  ste-case-val : {e v : · ⊢ Nat} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a : Effect} →
      e ⇓ v ↝ a 
    → v val
    ------------------------
    → `case e e₁ e₂ ⇓ `case v e₁ e₂ ↝ a

  ste-app-seq : {e₁ e₁' : · ⊢ τ ⇒ σ} {e₂ e₂' : · ⊢ τ} {a b : Effect} →
      e₁ ⇓ e₁' ↝ a
    → e₂ ⇓ e₂' ↝ b
    ------------------------
    → `app e₁ e₂ ⇓ `app e₁' e₂' ↝ a ∙ b

  ste-app-val₁ : {e₁ v₁ : · ⊢ τ ⇒ σ} {e₂ e₂' : · ⊢ τ} {a b : Effect} →
      e₁ ⇓ v₁ ↝ a
    → v₁ val
    → e₂ ⇓ e₂' ↝ b
    ------------------------
    → `app e₁ e₂ ⇓ `app v₁ e₂' ↝ a ∙ b

  ste-app-val₂ : {e₁ v₁ : · ⊢ τ ⇒ σ} {e₂ v₂ : · ⊢ τ} {a b : Effect} →
      e₁ ⇓ v₁ ↝ a  
    → v₁ val 
    → e₂ ⇓ v₂ ↝ b
    → v₂ val 
    ------------------------
    → `app e₁ e₂ ⇓ `app v₁ v₂ ↝ a ∙ b
  
  ste-eff-seq : {e e' : · ⊢ τ} {a b : Effect} →
      e ⇓ e' ↝ a
    ------------------------
    → `eff b e ⇓ `eff b e' ↝ a 
  
  ste-eff-val : {e v : · ⊢ τ} {a b : Effect} →
      e ⇓ v ↝ a
    → v val
    ------------------------
    → `eff b e ⇓ `eff b v ↝ a

  ste-case-z : {e : · ⊢ Nat} {e₁ e₁' : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a b : Effect} →
      e ⇓ `zero ↝ a 
    → e₁ ⇓ e₁' ↝ b
    ------------------------
    → `case e e₁ e₂ ⇓ e₁' ↝ a ∙ b

  ste-case-s : {e v : · ⊢ Nat} {e₁ e₂' : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a b : Effect} →
      e ⇓ `suc v ↝ a
    → v val 
    → e₂ [ v ] ⇓ e₂' ↝ b
    ------------------------
    → `case e e₁ e₂ ⇓ e₂' ↝ a ∙ b

  ste-app : {e₁ : · ⊢ τ ⇒ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ v₂ : · ⊢ τ} {e' : · ⊢ σ} {a b c : Effect} →
      e₁ ⇓ `fun e ↝ a
    → e₂ ⇓ v₂ ↝ b
    → v₂ val
    → e [ (`fun e) ][ v₂ ] ⇓ e' ↝ c
    ------------------------
    → `app e₁ e₂ ⇓ e' ↝ a ∙ b ∙ c  

  ste-eff : {e e' : · ⊢ τ} {a b : Effect} →
      e ⇓ e' ↝ a
    ------------------------
    → `eff b e ⇓ e' ↝ a ∙ b 

  ste-stop : {e : · ⊢ τ} →

    ------------------------
    e ⇓ e ↝ 1#
