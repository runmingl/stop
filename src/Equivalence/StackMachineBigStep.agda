{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (cong; _≡_; module ≡-Reasoning)

module Equivalence.StackMachineBigStep {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid
open import Substitution monoid

open import StackMachine monoid
open import BigStep monoid 

private
  variable
    τ σ : Type

effect-arithimic₁ : (a b : Effect) → 1# ∙ a ∙ (1# ∙ b) ≡ a ∙ b
effect-arithimic₁ a b = 
  let open ≡-Reasoning in 
    1# ∙ a ∙ (1# ∙ b) 
  ≡⟨ cong (λ b → (1# ∙ a) ∙ b) (identityˡ b) ⟩ 
    1# ∙ a ∙ b
  ≡⟨ assoc 1# a b ⟩
    1# ∙ (a ∙ b) 
  ≡⟨ identityˡ (a ∙ b) ⟩ 
    a ∙ b
  ∎

effect-arithimic₂ : (a b c : Effect) → 1# ∙ a ∙ (1# ∙ b ∙ (1# ∙ c)) ≡ a ∙ b ∙ c
effect-arithimic₂ a b c = 
  let open ≡-Reasoning in 
    1# ∙ a ∙ (1# ∙ b ∙ (1# ∙ c)) 
  ≡⟨ cong (λ a → a ∙ _) (identityˡ a) ⟩ 
    a ∙ (1# ∙ b ∙ (1# ∙ c))
  ≡⟨ cong (λ b → a ∙ (b ∙ _)) (identityˡ b) ⟩ 
    a ∙ (b ∙ (1# ∙ c))
  ≡⟨ cong (λ c → a ∙ (b ∙ c)) (identityˡ c) ⟩ 
    a ∙ (b ∙ c)
  ≡⟨ assoc a b c ⟨ 
    a ∙ b ∙ c
  ∎

⇓→↦* : {e v : · ⊢ τ} {a : Effect} {K : Frame} → 
      e ⇓ v ↝ a 
    → (k : K ÷ τ) 
    ------------------------
    → k ▹ e ↦* k ◃ v ↝ a
⇓→↦* be-zero k = k▹v↦*k◃v v-zero 
⇓→↦* (be-suc {v = v} {a = a} e⇓v) k = 
  let step₁ = ↦*-step ke-suc₁ (⇓→↦* e⇓v (k ⨾ suc⟨-⟩)) in
  let step₂ = ↦*-step ke-suc₂ ↦*-refl in 
  let step = ↦*-trans step₁ step₂ in
  Eq.subst (λ a → k ▹ `suc _ ↦* k ◃ `suc v ↝ a) eq step
  where 
    eq : 1# ∙ a ∙ (1# ∙ 1#) ≡ a 
    eq = 
      let open ≡-Reasoning in 
        1# ∙ a ∙ (1# ∙ 1#)
      ≡⟨ cong (λ b → (1# ∙ a) ∙ b) (identityʳ 1#) ⟩ 
        1# ∙ a ∙ 1# 
      ≡⟨ identityʳ (1# ∙ a) ⟩  
        1# ∙ a 
      ≡⟨ identityˡ a ⟩ 
        a 
      ∎
⇓→↦* (be-case-z {a = a} {b = b} e⇓z e⇓v) k rewrite sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇓→↦* e⇓z (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-z (⇓→↦* e⇓v k) in
    ↦*-trans step₁ step₂
⇓→↦* (be-case-s {a = a} {b = b} e⇓s e⇓v) k rewrite sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇓→↦* e⇓s (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-s (⇓→↦* e⇓v k) in
    ↦*-trans step₁ step₂
⇓→↦* be-fun k = k▹v↦*k◃v v-fun
⇓→↦* (be-app {a = a} {b = b} {c = c} e⇓f e⇓v e⇓v₁) k rewrite sym (effect-arithimic₂ a b c) = 
  let step₁ = ↦*-step ke-app₁ (⇓→↦* e⇓f (k ⨾ _)) in 
  let step₂ = ↦*-step ke-app₂ (⇓→↦* e⇓v (k ⨾ _)) in
  let step₃ = ↦*-step ke-app₃ (⇓→↦* e⇓v₁ k) in
    ↦*-trans step₁ (↦*-trans step₂ step₃)
⇓→↦* (be-eff e⇓v) k = ↦*-step ke-eff (⇓→↦* e⇓v k)
  
infix 4 _⟪_ 
_⟪_ : · ⊢ τ → · ⊢ τ → Set ℓ 
_⟪_ {τ} e d = {v : · ⊢ τ} {a : Effect} → e ⇓ v ↝ a → d ⇓ v ↝ a

⟪-● : {K : Frame} {e d : · ⊢ τ} →
    (k : K ÷ τ) → 
    e ⟪ d 
  ------------------------
  → k ● e ⟪ k ● d 
⟪-● ε f H = f H
⟪-● (K ⨾ suc⟨-⟩) f        = ⟪-● K λ { (be-suc e⇓v) → be-suc (f e⇓v) }
⟪-● (K ⨾ case⟨-⟩ e₁ e₂) f = ⟪-● K λ { (be-case-z e⇓z e⇓v) → be-case-z (f e⇓z) e⇓v
                                    ; (be-case-s e⇓s e⇓v) → be-case-s (f e⇓s) e⇓v}
⟪-● (K ⨾ app⟨-⟩ e₂) f     = ⟪-● K λ { (be-app e⇓f e₂⇓v e⇓v) → be-app (f e⇓f) e₂⇓v e⇓v }
⟪-● (K ⨾ app e₁ ⟨-⟩) f    = ⟪-● K λ { (be-app e⇓f e₂⇓v e⇓v) → be-app e⇓f (f e₂⇓v) e⇓v}

goal : (s s' : State) → return s ≡ return s' → Set ℓ
goal (k ◃ e) (k' ◃ e') p = e val → k' ● e' ⟪ Eq.subst (λ τ → · ⊢ τ) p (k ● e) 
goal (k ▹ e) (k' ◃ e') p = k' ● e' ⟪ Eq.subst (λ τ → · ⊢ τ) p (k ● e)
goal (k ▹ e) (k' ▹ e') p = k' ● e' ⟪ Eq.subst (λ τ → · ⊢ τ) p (k ● e)
goal (k ◃ e) (k' ▹ e') p = e val → k' ● e' ⟪ Eq.subst (λ τ → · ⊢ τ) p (k ● e)

return-≡ : {s s' : State} {a : Effect} → s ↦ s' ↝ a → return s ≡ return s' 
return-≡ ke-zero = Eq.refl
return-≡ ke-suc₁ = Eq.refl
return-≡ ke-suc₂ = Eq.refl
return-≡ ke-case = Eq.refl
return-≡ ke-case-z = Eq.refl
return-≡ ke-case-s = Eq.refl
return-≡ ke-fun = Eq.refl
return-≡ ke-app₁ = Eq.refl
return-≡ ke-app₂ = Eq.refl
return-≡ ke-app₃ = Eq.refl
return-≡ ke-eff = Eq.refl 

s-⟪-● : {s s' : State} {a : Effect} → (transition : s ↦ s' ↝ a) → goal s s' (return-≡ transition)
s-⟪-● ke-zero d = d
s-⟪-● ke-suc₁ d = d
s-⟪-● ke-suc₂ v-val d = d
s-⟪-● ke-case d = d
s-⟪-● (ke-case-z {k = k}) v-zero d = ⟪-● k (λ e₁⇓v → 
  let step = be-case-z be-zero e₁⇓v in 
    Eq.subst (λ a → `case `zero _ _ ⇓ _ ↝ a) (identityˡ _) step) 
  d
s-⟪-● (ke-case-s {k = k}) (v-suc v-val) d = ⟪-● k (λ e₂⇓v → 
  let step = be-case-s (be-suc (v⇓v v-val)) e₂⇓v in 
    Eq.subst (λ a → `case (`suc _) _ _ ⇓ _ ↝ a) (identityˡ _) step) 
  d
s-⟪-● ke-fun d = d
s-⟪-● ke-app₁ = {!   !}
s-⟪-● ke-app₂ = {!   !}
s-⟪-● ke-app₃ = {!   !}
s-⟪-● (ke-eff {k = k}) d = {!   !}
  -- ⟪-● k (λ e⇓v → 
--   let step = be-eff e⇓v in 
--   {!   !}) 
--   d


-- thm : {s s' : State} {a : Effect} → (transition : s ↦ s' ↝ a) → goal s s' (return-≡ transition)
-- thm ke-zero (v , a , e⇓v) = v , a , e⇓v , e⇓v
-- thm ke-suc₁ (v , a , e⇓v) = v , a , e⇓v , e⇓v
-- thm ke-suc₂ v-val (v , a , e⇓v) = v , a , e⇓v , e⇓v
-- thm ke-case (v , a , e⇓v) = v , a , e⇓v , e⇓v 
-- thm (ke-case-z {k = k}) v-zero = ⟪-● k λ (v , a , e⇓v) → v , a , e⇓v , Eq.subst (λ a → _ ⇓ _ ↝ a) (identityˡ a) (be-case-z be-zero e⇓v)
-- thm (ke-case-s {k = k}) (v-suc v-val) = ⟪-● k (λ (v , a , e⇓v) → v , a , e⇓v , Eq.subst (λ a → _ ⇓ _ ↝ a) (identityˡ a) (be-case-s (v⇓v (v-suc v-val)) e⇓v))
-- thm ke-fun (v , a , e⇓v) = v , a , e⇓v , e⇓v
-- thm ke-app₁ (v , a , e⇓v) = v , a , e⇓v , e⇓v
-- thm ke-app₂ v-fun (v , a , e⇓v) = v , a , e⇓v , e⇓v
-- thm ke-app₃ v-val = {!   !}
-- thm (ke-eff {k = k}) = ⟪-● k λ (v , a , e⇓v) → v , a , e⇓v , Eq.subst (λ a → _ ⇓ _ ↝ a) (identityˡ a) {! be-eff  !} 
-- mutual
--   ▹-val : {K : Frame} {k : K ÷ τ} {e : · ⊢ τ} {k' : K ÷ σ} {e' : · ⊢ σ} {a : Effect}→
--       k ▹ e ↦* k' ◃ e' ↝ a 
--     ------------------------
--     → e' val
--   ▹-val (↦*-step {s' = x₁ ◃ x₂} x d) = ◃-val {! d  !} {!   !}
--   ▹-val (↦*-step {s' = x₁ ▹ x₂} x d) = ▹-val {! d  !}
--   ◃-val : {K : Frame} {k : K ÷ τ} {e : · ⊢ τ} {k' : K ÷ σ} {e' : · ⊢ σ} {a : Effect} → 
--       k ◃ e ↦* k' ◃ e' ↝ a 
--     → e val
--     ------------------------
--     → e' val
--   ◃-val ↦*-refl v-val = {!   !}
--   ◃-val (↦*-step x d) v-val = {!   !} 

