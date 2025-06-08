{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude 

open import Level 

module KMachine {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid
open import Substitution monoid

private
  variable
    τ σ : Type

infixl 5 _∘_
data Frame : Set ℓ where 
  ·   : Frame 
  _∘_ : Frame → · # τ ⊢ σ → Frame

private 
  variable
    K : Frame

infix 4 _÷_
infix 6 _⨾_
data _÷_ : Frame → Type → Set ℓ where
  ε  : · ÷ τ 
  _⨾_ : K ÷ σ → (e : · # τ ⊢ σ) → K ∘ e ÷ τ

infix 5 _▹_ _◃_
data State : Set ℓ where
  _◃_ : K ÷ τ → · ⊢ τ → State
  _▹_ : K ÷ τ → · ⊢ τ → State

infix 2 _↦_↝_
data _↦_↝_ : State → State → Effect → Set ℓ where
  ke-val : {k : K ÷ τ} {v : · ⊢ τ} →
      v val
    ------------------------
    → k ▹ v ↦ k ◃ v ↝ 1#
   
  ke-pop : {v : · ⊢ τ} {k : K ÷ σ} {e : · # τ ⊢ σ} →
      v val 
    ------------------------ 
    → k ⨾ e ◃ v ↦ k ▹ e [ v ] ↝ 1#
  
  ke-suc : {k : K ÷ Nat} {e : · ⊢ Nat} → 
    
    ------------------------ 
    k ▹ `suc e ↦ k ⨾ `suc (` Z) ▹ e ↝ 1#

  ke-case : {k : K ÷ τ} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {e : · ⊢ Nat} →

    ------------------------
    k ▹ `case e e₁ e₂ ↦ k ⨾ `case (` Z) (⇈ e₁) (⇈ e₂) ▹ e ↝ 1#

  ke-case-z : {k : K ÷ τ} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} →

    ------------------------
    k ▹ `case `zero e₁ e₂ ↦ k ▹ e₁ ↝ 1#

  ke-case-s : {k : K ÷ τ} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {v : · ⊢ Nat} →
      v val
    ------------------------
    → k ▹ `case (`suc v) e₁ e₂ ↦ k ▹ e₂ [ v ] ↝ 1#

  ke-app-f : {k : K ÷ σ} {e₁ : · ⊢ τ ⇒ σ} {e₂ : · ⊢ τ} →
      
    ------------------------
    k ▹ `app e₁ e₂ ↦ k ⨾ `app (` Z) (⇈ e₂) ▹ e₁ ↝ 1# 

  ke-app-a : {k : K ÷ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ : · ⊢ τ} →

    ------------------------
    k ▹ `app (`fun e) e₂ ↦ k ⨾ `app (⇈ (`fun e)) (` Z) ▹ e₂ ↝ 1#
  
  ke-app : {k : K ÷ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {v : · ⊢ τ} →
      v val
    ------------------------
    → k ▹ `app (`fun e) v ↦ k ▹ e [ (`fun e) ][ v ] ↝ 1#

  ke-eff : {k : K ÷ τ} {e : · ⊢ τ} {a : Effect} →

    ------------------------   
    k ▹ `eff a e ↦ k ▹ e ↝ a

infix 2 _↦*_↝_
data _↦*_↝_ : State → State → Effect → Set ℓ where
  ↦*-refl : {s : State} → 
    
    ------------------------
    s ↦* s ↝ 1#

  ↦*-step : {s s' s'' : State} {a b : Effect} → 
      s ↦ s' ↝ a 
    → s' ↦* s'' ↝ b 
    -------------
    → s ↦* s'' ↝ a ∙ b

↦*-trans : {s s' s'' : State} {a b : Effect} → 
    s ↦* s' ↝ a
  → s' ↦* s'' ↝ b
  ------------------------
  → s ↦* s'' ↝ a ∙ b
↦*-trans {b = b} ↦*-refl step rewrite identityˡ b = step
↦*-trans {b = c} (↦*-step {a = a} {b = b} step₁ step₂) step rewrite assoc a b c = 
    ↦*-step step₁ (↦*-trans step₂ step)

compatible : {p : State → State}
    → ({s s' : State} {a : Effect} → s ↦ s' ↝ a → p s ↦ p s' ↝ a)
    → {s s' : State} {a : Effect} → s ↦* s' ↝ a → p s ↦* p s' ↝ a 
compatible alift ↦*-refl       = ↦*-refl
compatible alift (↦*-step x s) = ↦*-step (alift x) (compatible alift s)
