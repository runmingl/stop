{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Level

module Substitution {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid 

private 
  variable 
    τ τ₁ τ₂ σ : Type
    Γ Δ Ξ : Ctx

Subst : Ctx → Ctx → Set ℓ
Subst Γ Δ = ∀ {τ} → Γ ∋ τ → Δ ⊢ τ

Rename : Ctx → Ctx → Set
Rename Γ Δ = ∀ {τ} → Γ ∋ τ → Δ ∋ τ

extend-var : Rename Γ Δ → Rename (Γ # τ) (Δ # τ)
extend-var ρ Z      =  Z
extend-var ρ (S x)  =  S (ρ x)

rename : Rename Γ Δ → Γ ⊢ τ → Δ ⊢ τ
rename ρ (` x)           = ` (ρ x)
rename ρ `zero           = `zero
rename ρ (`suc x)        = `suc (rename ρ x)
rename ρ (`case e e₁ e₂) = `case (rename ρ e) (rename ρ e₁) (rename (extend-var ρ) e₂)
rename ρ (`fun e)        = `fun (rename (extend-var (extend-var ρ)) e)
rename ρ (`app e₁ e₂)    = `app (rename ρ e₁) (rename ρ e₂)
rename ρ (`eff a e)      = `eff a (rename ρ e)

weaken : Subst Γ Δ → Subst (Γ # τ) (Δ # τ)
weaken γ Z     = ` Z
weaken γ (S x) = rename S (γ x)

subst : Subst Γ Δ → Γ ⊢ τ → Δ ⊢ τ
subst γ (` x)           = γ x
subst γ `zero           = `zero
subst γ (`suc x)        = `suc (subst γ x)
subst γ (`case e e₁ e₂) = `case (subst γ e) (subst γ e₁) (subst (weaken γ) e₂)
subst γ (`fun e)        = `fun (subst (weaken (weaken γ)) e)
subst γ (`app e₁ e₂)    = `app (subst γ e₁) (subst γ e₂)
subst γ (`eff a e)      = `eff a (subst γ e)

extend : Δ ⊢ τ → Subst Γ Δ → Subst (Γ # τ) Δ
extend v γ Z     = v
extend v γ (S x) = γ x

id-γ : Subst Γ Γ
id-γ = `_ 

_[_] : (Γ # τ) ⊢ σ → Γ ⊢ τ → Γ ⊢ σ
_[_] e e₁ = subst (extend e₁ id-γ) e

_[_][_] : (Γ # τ₁ # τ₂) ⊢ σ → Γ ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊢ σ
_[_][_] e e₁ e₂ = subst (extend e₂ (extend e₁ id-γ)) e

subst-eq : (γ : Subst Γ ·) (e₁ : Γ # τ ⊢ σ) (e₂ : · ⊢ τ) → 
  subst (extend e₂ γ) e₁ ≡ (subst (weaken γ) e₁ [ e₂ ])
subst-eq {Γ} {τ} {σ} γ e₁ e₂ = {!   !}

subst-eq₂ : (γ : Subst Γ ·) (e₁ : Γ # τ₁ # τ₂ ⊢ σ) (e₂ : · ⊢ τ₁) (e₃ : · ⊢ τ₂) → 
  subst (extend e₃ (extend e₂ γ)) e₁ ≡ subst (weaken (weaken γ)) e₁ [ e₂ ][ e₃ ]
subst-eq₂ {Γ} {τ₁} {τ₂} {σ} γ e₁ e₂ e₃ = {!   !}
