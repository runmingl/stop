{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (cong; _≡_; module ≡-Reasoning)

module Equivalence.StackMachineBigStop {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid
open import Substitution monoid

open import StackMachine monoid
open import BigStop monoid 

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
  → v val 
  → (k : K ÷ τ) 
  ------------------------
  → k ▹ e ↦* k ◃ v ↝ a
⇓→↦* ste-zero v-zero k = k▹v↦*k◃v v-zero
⇓→↦* (ste-suc {a = a} e⇓v) (v-suc v-val) k = 
  let step₁ = ↦*-step ke-suc₁ (⇓→↦* e⇓v v-val (k ⨾ suc⟨-⟩)) in
  let step₂ = ↦*-step ke-suc₂ ↦*-refl in 
  let step = ↦*-trans step₁ step₂ in
  Eq.subst (λ a → k ▹ `suc _ ↦* k ◃ `suc _ ↝ a) eq step
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
⇓→↦* ste-fun v-val k = k▹v↦*k◃v v-fun
⇓→↦* (ste-app {a = a} {b = b} {c = c} e⇓f e₂⇓v₂ v₂-val e⇓v₁) v-val k rewrite sym (effect-arithimic₂ a b c) = 
  let step₁ = ↦*-step ke-app₁ (⇓→↦* e⇓f v-fun (k ⨾ _)) in 
  let step₂ = ↦*-step ke-app₂ (⇓→↦* e₂⇓v₂ v₂-val (k ⨾ _)) in
  let step₃ = ↦*-step ke-app₃ (⇓→↦* e⇓v₁ v-val k) in
    ↦*-trans step₁ (↦*-trans step₂ step₃)
⇓→↦* (ste-case-z {a = a} {b = b} e⇓z e⇓v) v-val k rewrite sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇓→↦* e⇓z v-zero (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-z (⇓→↦* e⇓v v-val k) in
    ↦*-trans step₁ step₂
⇓→↦* (ste-case-s {a = a} {b = b} e⇓s v₁-val e⇓v) v-val k rewrite sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇓→↦* e⇓s (v-suc v₁-val) (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-s (⇓→↦* e⇓v v-val k) in
    ↦*-trans step₁ step₂
⇓→↦* (ste-eff e⇓v) v-val k = ↦*-step ke-eff (⇓→↦* e⇓v v-val k)
⇓→↦* ste-stop v-val k = k▹v↦*k◃v v-val

⇓→↦*s : {e e' : · ⊢ τ} {a : Effect} {K : Frame} → 
    e ⇓ e' ↝ a 
  → (k : K ÷ τ) 
  ------------------------
  → Σ[ s ∈ State ] (k ▹ e ↦* s ↝ a)
⇓→↦*s ste-zero k = k ▹ `zero , ↦*-refl
⇓→↦*s (ste-suc {a = a} e⇓e') k with ⇓→↦*s e⇓e' (k ⨾ suc⟨-⟩)   
... | s , k'▹e↦*s = s , Eq.subst (λ a → k ▹ `suc _ ↦* s ↝ a) (identityˡ a) (↦*-step ke-suc₁ k'▹e↦*s)
⇓→↦*s (ste-fun {e = e}) k = k ▹ `fun e , ↦*-refl
⇓→↦*s (ste-app-seq₁ {a = a} e⇓e') k with ⇓→↦*s e⇓e' (k ⨾ app⟨-⟩ _)
... | s , k'▹e↦*s = s , Eq.subst (λ a → k ▹ `app _ _ ↦* s ↝ a) (identityˡ a) (↦*-step ke-app₁ k'▹e↦*s)
⇓→↦*s (ste-app-seq₂ {a = a} {b = b} e⇓f e⇓e'') k with ⇓→↦*s e⇓e'' (k ⨾ app _ ⟨-⟩)
... | s , k'▹e↦*s rewrite sym (effect-arithimic₁ a b) =   
  let step₁ = ↦*-step ke-app₁ (⇓→↦* e⇓f v-fun (k ⨾ app⟨-⟩ _)) in 
  let step₂ = ↦*-step ke-app₂ k'▹e↦*s in 
    s , ↦*-trans step₁ step₂
⇓→↦*s (ste-app {a = a} {b = b} {c = c} e⇓f e₂⇓v₂ v₂-val e⇓v₁) k with ⇓→↦*s e⇓v₁ k 
... | s , k'▹e↦*s rewrite sym (effect-arithimic₂ a b c) = 
  let step₁ = ↦*-step ke-app₁ (⇓→↦* e⇓f v-fun (k ⨾ app⟨-⟩ _)) in 
  let step₂ = ↦*-step ke-app₂ (⇓→↦* e₂⇓v₂ v₂-val (k ⨾ app _ ⟨-⟩)) in
  let step₃ = ↦*-step ke-app₃ k'▹e↦*s in
    s , ↦*-trans step₁ (↦*-trans step₂ step₃)
⇓→↦*s (ste-case-seq {a = a} e⇓e') k with ⇓→↦*s e⇓e' (k ⨾ case⟨-⟩ _ _)
... | s , k'▹e↦*s = s , Eq.subst (λ a → k ▹ `case _ _ _ ↦* s ↝ a) (identityˡ a) (↦*-step ke-case k'▹e↦*s)
⇓→↦*s (ste-case-z {a = a} {b = b} e⇓z e⇓e') k with ⇓→↦*s e⇓e' k
... | s , k▹e↦*s rewrite sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇓→↦* e⇓z v-zero (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-z k▹e↦*s in
    s , ↦*-trans step₁ step₂
⇓→↦*s (ste-case-s {a = a} {b = b} e⇓s v₁-val e⇓e') k with ⇓→↦*s e⇓e' k
... | s , k▹e↦*s rewrite sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇓→↦* e⇓s (v-suc v₁-val) (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-s k▹e↦*s in
    s ,  ↦*-trans step₁ step₂
⇓→↦*s (ste-eff {e' = e'} e⇓e') k with ⇓→↦*s e⇓e' k 
... | s , k▹e↦*s = s , ↦*-step ke-eff k▹e↦*s
⇓→↦*s (ste-stop {e = e}) k = k ▹ e , ↦*-refl 
