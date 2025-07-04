open import Prelude 

open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Level 

module Language.StackMachine {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

private
  variable
    τ σ : Type

infix 4 _⇝_
data _⇝_ : Type → Type → Set ℓ where 
  suc⟨-⟩  : 
    
    ------------------------ 
    Nat ⇝ Nat

  case⟨-⟩ : 
      · ⊢ τ 
    → · # Nat ⊢ τ 
    ------------------------
    → Nat ⇝ τ

  app⟨-⟩  : 
      · ⊢ τ 
    ------------------------
    → τ ⇒ σ ⇝ σ

  app⟨fun_⟩⟨-⟩ : 
      · # τ ⇒ σ # τ ⊢ σ 
    ------------------------
    → τ ⇝ σ

infixl 5 _∘_
data Frame : Set ℓ where 
  ·   : Frame 
  _∘_ : Frame → τ ⇝ σ → Frame

private 
  variable
    K : Frame

infix 4 _÷_
infix 6 _⨾_
data _÷_ : Frame → Type → Set ℓ where
  ε  : · ÷ τ 
  _⨾_ : K ÷ σ → (F : τ ⇝ σ) → K ∘ F ÷ τ

infix 5 _▹_ _◃_
data State : Set ℓ where
  _◃_ : K ÷ τ → · ⊢ τ → State
  _▹_ : K ÷ τ → · ⊢ τ → State

infix 2 _↦_↝_
data _↦_↝_ : State → State → Effect → Set ℓ where
  ke-zero : {k : K ÷ Nat} →
      
    ------------------------
    k ▹ `zero ↦ k ◃ `zero ↝ 1#
   
  ke-suc₁ : {k : K ÷ Nat} {e : · ⊢ Nat} → 
      
    ------------------------
    k ▹ `suc e ↦ k ⨾ suc⟨-⟩ ▹ e ↝ 1#

  ke-suc₂ : {k : K ÷ Nat} {v : · ⊢ Nat} →
    
    ------------------------
    k ⨾ suc⟨-⟩ ◃ v ↦ k ◃ `suc v ↝ 1#

  ke-case : {k : K ÷ τ} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {e : · ⊢ Nat} →
    
    ------------------------
    k ▹ `case e e₁ e₂ ↦ k ⨾ case⟨-⟩ e₁ e₂ ▹ e ↝ 1#

  ke-case-z : {k : K ÷ τ} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} →
    
    ------------------------
    k ⨾ case⟨-⟩ e₁ e₂ ◃ `zero ↦ k ▹ e₁ ↝ 1#

  ke-case-s : {k : K ÷ τ} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {v : · ⊢ Nat} →
      
    ------------------------
    k ⨾ case⟨-⟩ e₁ e₂ ◃ `suc v ↦ k ▹ e₂ [ v ] ↝ 1#

  ke-fun : {k : K ÷ τ ⇒ σ} {e : · # τ ⇒ σ # τ ⊢ σ} →

    ------------------------
    k ▹ `fun e ↦ k ◃ `fun e ↝ 1#

  ke-app₁ : {k : K ÷ σ} {e₁ : · ⊢ τ ⇒ σ} {e₂ : · ⊢ τ} →
    
    ------------------------
    k ▹ `app e₁ e₂ ↦ k ⨾ app⟨-⟩ e₂ ▹ e₁ ↝ 1#

  ke-app₂ : {k : K ÷ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ : · ⊢ τ} →

    ------------------------
    k ⨾ app⟨-⟩ e₂ ◃ `fun e ↦ k ⨾ app⟨fun e ⟩⟨-⟩ ▹ e₂ ↝ 1#

  ke-app₃ : {k : K ÷ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {v : · ⊢ τ} →
      
    ------------------------
    k ⨾ app⟨fun e ⟩⟨-⟩ ◃ v ↦ k ▹ e [ (`fun e) ][ v ] ↝ 1#

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
    ------------------------
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

k▹v↦*k◃v : {k : K ÷ τ} {v : · ⊢ τ} →
    v val 
  ------------------------
  → k ▹ v ↦* k ◃ v ↝ 1#
k▹v↦*k◃v v-zero rewrite Eq.sym (identityʳ 1#) = ↦*-step ke-zero ↦*-refl 
k▹v↦*k◃v (v-suc v-val) rewrite Eq.trans (Eq.sym (identityˡ 1#)) (Eq.cong₂ _∙_ (Eq.sym (identityˡ 1#)) (Eq.sym (identityˡ 1#))) = 
  let step₁ = ↦*-step ke-suc₁ (k▹v↦*k◃v v-val) in 
  let step₂ = ↦*-step ke-suc₂ ↦*-refl in 
    ↦*-trans step₁ step₂
k▹v↦*k◃v v-fun rewrite Eq.sym (identityʳ 1#) = ↦*-step ke-fun ↦*-refl

return-type : K ÷ τ → Type 
return-type {τ = τ} ε = τ
return-type (K ⨾ F) = return-type K

infix 5 _●_
_●_ : (k : K ÷ τ) → · ⊢ τ → · ⊢ return-type k
_●_ ε e = e
(K ⨾ suc⟨-⟩) ● e = K ● `suc e
(K ⨾ case⟨-⟩ e₁ e₂) ● e = K ● `case e e₁ e₂
(K ⨾ app⟨-⟩ e₂) ● e = K ● `app e e₂
(K ⨾ app⟨fun e' ⟩⟨-⟩) ● e = K ● `app (`fun e') e

mutual 
  ▹-val : {K K' : Frame} {k : K ÷ τ} {e : · ⊢ τ} {k' : K' ÷ σ} {e' : · ⊢ σ} {a : Effect} →
      k ▹ e ↦* k' ◃ e' ↝ a 
    ------------------------
    → e' val
  ▹-val (↦*-step ke-zero s) = ◃-val s v-zero
  ▹-val (↦*-step ke-suc₁ s) = ▹-val s
  ▹-val (↦*-step ke-case s) = ▹-val s
  ▹-val (↦*-step ke-fun s)  = ◃-val s v-fun
  ▹-val (↦*-step ke-app₁ s) = ▹-val s
  ▹-val (↦*-step ke-eff s)  = ▹-val s

  ◃-val : {K K' : Frame} {k : K ÷ τ} {e : · ⊢ τ} {k' : K' ÷ σ} {e' : · ⊢ σ} {a : Effect} → 
      k ◃ e ↦* k' ◃ e' ↝ a 
    → e val
    ------------------------
    → e' val
  ◃-val  ↦*-refl v-val                      = v-val
  ◃-val (↦*-step ke-suc₂ s) v-val           = ◃-val s (v-suc v-val)
  ◃-val (↦*-step ke-case-z s) v-zero        = ▹-val s
  ◃-val (↦*-step ke-case-s s) (v-suc v-val) = ▹-val s
  ◃-val (↦*-step ke-app₂ s) v-fun           = ▹-val s
  ◃-val (↦*-step ke-app₃ s) v-val           = ▹-val s
