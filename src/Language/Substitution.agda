open import Prelude

open import Level

{-
  Substitution and Renaming adapted from PLFA https://plfa.github.io/Substitution

  We do not need to prove the substitution lemmas here, as operational semantics only concern closed terms. 
  Nevertheless substitution lemmas in PLFA are compatible in our setting.
-}
module Language.Substitution {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid 

private 
  variable 
    τ τ₁ τ₂ σ : Type
    Γ Δ : Ctx

Subst : Ctx → Ctx → Set ℓ
Subst Γ Δ = ∀ {τ} → Γ ∋ τ → Δ ⊢ τ

Rename : Ctx → Ctx → Set ℓ
Rename Γ Δ = ∀ {τ} → Γ ∋ τ → Δ ∋ τ

ext : ∀ {Γ Δ} → (∀ {τ} → Γ ∋ τ → Δ ∋ τ)
  → (∀ {τ σ} → (Γ # σ) ∋ τ → (Δ # σ) ∋ τ)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : Rename Γ Δ → Γ ⊢ τ → Δ ⊢ τ
rename ρ (` x)           = ` (ρ x)
rename ρ `zero           = `zero
rename ρ (`suc x)        = `suc (rename ρ x)
rename ρ (`case e e₁ e₂) = `case (rename ρ e) (rename ρ e₁) (rename (ext ρ) e₂)
rename ρ (`fun e)        = `fun (rename (ext (ext ρ)) e)
rename ρ (`app e₁ e₂)    = `app (rename ρ e₁) (rename ρ e₂)
rename ρ (`eff a e)      = `eff a (rename ρ e)

exts : ∀ {Γ Δ} → (∀ {τ} → Γ ∋ τ → Δ ⊢ τ)
  → (∀ {τ σ} → (Γ # σ) ∋ τ → (Δ # σ) ⊢ τ)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S (σ x)

subst : Subst Γ Δ → Γ ⊢ τ → Δ ⊢ τ
subst γ (` x)           = γ x
subst γ `zero           = `zero
subst γ (`suc x)        = `suc (subst γ x)
subst γ (`case e e₁ e₂) = `case (subst γ e) (subst γ e₁) (subst (exts γ) e₂)
subst γ (`fun e)        = `fun (subst (exts (exts γ)) e)
subst γ (`app e₁ e₂)    = `app (subst γ e₁) (subst γ e₂)
subst γ (`eff a e)      = `eff a (subst γ e)

subst-zero : ∀ {Γ σ} → Γ ⊢ σ → ∀ {τ} → (Γ # σ) ∋ τ → Γ ⊢ τ
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x

subst-zero-one : Γ ⊢ τ₁ →  Γ ⊢ τ₂ → (Γ # τ₁ # τ₂) ∋ τ → Γ ⊢ τ
subst-zero-one e₁ e₂ Z         =  e₂
subst-zero-one e₁ e₂ (S Z)     =  e₁
subst-zero-one e₁ e₂ (S (S x)) = ` x

_[_] : Γ # τ ⊢ σ → Γ ⊢ τ → Γ ⊢ σ
_[_] e e₁ = subst (subst-zero e₁) e

_[_][_] : Γ # τ₁ # τ₂ ⊢ σ → Γ ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊢ σ
_[_][_] e e₁ e₂ = subst (subst-zero-one e₁ e₂) e
