{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (cong; _≡_; module ≡-Reasoning)

module Equivalence.KMachineBigStep {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid
open import Substitution monoid
  
open import KMachine monoid
open import BigStep monoid 

private
  variable
    τ σ : Type

effect-arithimic : (a b : Effect) → 1# ∙ a ∙ (1# ∙ 1#) ∙ (1# ∙ b) ≡ a ∙ b
effect-arithimic a b = 
  let open ≡-Reasoning in 
    1# ∙ a ∙ (1# ∙ 1#) ∙ (1# ∙ b)
  ≡⟨ cong (λ b → _ ∙ b) (identityˡ b) ⟩ 
    1# ∙ a ∙ (1# ∙ 1#) ∙ b
  ≡⟨ cong (λ c → 1# ∙ a ∙ c ∙ b) (identityʳ 1#) ⟩ 
    1# ∙ a ∙ 1# ∙ b
  ≡⟨ cong (λ a → a ∙ b) (identityʳ (1# ∙ a)) ⟩ 
    1# ∙ a ∙ b
  ≡⟨ assoc 1# a b ⟩
    1# ∙ (a ∙ b) 
  ≡⟨ identityˡ (a ∙ b) ⟩ 
    a ∙ b
  ∎

⇓→↦* : {e v : · ⊢ τ} {a : Effect} {K : Frame} → 
      e ⇓ v ↝ a 
    → (k : K ÷ τ) 
    ------------------------
    → k ▹ e ↦* k ◃ v ↝ a
⇓→↦* (be-zero) k rewrite sym (identityʳ 1#) = ↦*-step (ke-val v-zero) ↦*-refl
⇓→↦* (be-suc {v = v} {a = a} e⇓v) k = 
  let step₁ = ↦*-step ke-suc (⇓→↦* e⇓v (k ⨾ `suc (` Z))) in
  let v-val = ⇓-val e⇓v in
  let step₂ = ↦*-step (ke-pop v-val) (↦*-step (ke-val (v-suc v-val)) ↦*-refl) in 
  Eq.subst (λ a → k ▹ `suc _ ↦* k ◃ `suc v ↝ a) eq (↦*-trans step₁ step₂)
  where 
    eq : 1# ∙ a ∙ (1# ∙ (1# ∙ 1#)) ≡ a 
    eq = 
      let open ≡-Reasoning in 
        1# ∙ a ∙ (1# ∙ (1# ∙ 1#))
      ≡⟨ cong (λ b → (1# ∙ a) ∙ (1# ∙ b)) (identityʳ 1#) ⟩ 
        1# ∙ a ∙ (1# ∙ 1#)
      ≡⟨ cong (λ b → (1# ∙ a) ∙ b) (identityʳ 1#) ⟩ 
        1# ∙ a ∙ 1# 
      ≡⟨ identityʳ (1# ∙ a) ⟩  
        1# ∙ a 
      ≡⟨ identityˡ a ⟩ 
        a 
      ∎
⇓→↦* (be-case-z {e = e} {e₁ = e₁} {e₂ = e₂} {a = a} {b = b} e⇓z e⇓v) k = 
  let step₁ = ↦*-step (ke-case {e₁ = e₁} {e₂ = e₂}) (⇓→↦* e⇓z (k ⨾ `case (` Z) (⇈ e₁) (⟪ exts ↑ ⟫ e₂))) in 
  let step₂ = ↦*-step (ke-pop v-zero) ↦*-refl in
  let step₁₂ = ↦*-trans step₁ step₂ in
  let step₁₂' = Eq.subst (λ F → k ▹ `case e e₁ e₂ ↦* k ▹ F ↝ 1# ∙ a ∙ (1# ∙ 1#)) lem step₁₂ in
  let step₃ = ↦*-step ke-case-z (⇓→↦* e⇓v k) in 
  let step = ↦*-trans step₁₂' step₃ in
  Eq.subst (λ c → k ▹ `case e e₁ e₂ ↦* k ◃ _ ↝ c) (effect-arithimic a b) step
  where 
    lem : (`case (` Z) (⇈ e₁) (⟪ exts ↑ ⟫ e₂)) [ `zero ] ≡ `case `zero e₁ e₂
    lem rewrite shift-subst₁ `zero e₁ rewrite shift-subst₂ `zero e₂ = Eq.refl
⇓→↦* (be-case-s {e = e} {v = v} {e₁ = e₁} {v₁ = v₁} {e₂ = e₂} {a = a} {b = b} e⇓s e⇓v) k with ⇓-val e⇓s
... | v-suc v-val = 
  let step₁ = ↦*-step (ke-case {e₁ = e₁} {e₂ = e₂} {e = e}) (⇓→↦* e⇓s (k ⨾ `case (` Z) (⇈ e₁) (⟪ exts ↑ ⟫ e₂))) in 
  let step₂ = ↦*-step (ke-pop (⇓-val e⇓s)) ↦*-refl in 
  let step₁₂ =  ↦*-trans step₁ step₂ in 
  let step₁₂' = Eq.subst (λ F → k ▹ `case e e₁ e₂ ↦* k ▹ F ↝ 1# ∙ a ∙ (1# ∙ 1#)) lem step₁₂ in
  let step₃ = ↦*-step (ke-case-s v-val) (⇓→↦* e⇓v k) in
  let step = ↦*-trans step₁₂' step₃ in
  Eq.subst (λ c → k ▹ `case e e₁ e₂ ↦* k ◃ v₁ ↝ c) (effect-arithimic a b) step
  where 
    lem : (`case (` Z) (⇈ e₁) (⟪ exts ↑ ⟫ e₂)) [ `suc v ] ≡ `case (`suc v) e₁ e₂
    lem rewrite shift-subst₁ (`suc v) e₁ rewrite shift-subst₂ (`suc v) e₂ = Eq.refl
⇓→↦* (be-fun) k rewrite sym (identityʳ 1#) = ↦*-step (ke-val v-fun) ↦*-refl
⇓→↦* (be-app {e₁ = e₁} {e = e} {e₂ = e₂} {v = v} {v₁ = v₁} {a} {b} {c} e⇓f e⇓v e⇓v₁) k = 
  let step₁ = ↦*-step (ke-app-f {e₁ = e₁} {e₂ = e₂}) (⇓→↦* e⇓f (k ⨾ `app (` Z) (⇈ e₂))) in 
  let step₂ = ↦*-step (ke-pop {v = `fun e} {k = k} {e = `app (` Z) (⇈ e₂)} v-fun) ↦*-refl in 
  let step₁₂ = ↦*-trans step₁ step₂ in
  let step₁₂' = Eq.subst (λ F → k ▹ `app e₁ e₂ ↦* k ▹ F ↝ 1# ∙ a ∙ (1# ∙ 1#)) lem₁ step₁₂ in
  let step₃ = ↦*-step (ke-app-a {e = e} {e₂ = e₂}) (⇓→↦* e⇓v (k ⨾ `app (⇈ (`fun e)) (` Z))) in 
  let step₄ = ↦*-step (ke-pop {v = v} {k = k} {e = `app (⇈ (`fun e)) (` Z)} (⇓-val e⇓v)) ↦*-refl in 
  let step₄' = Eq.subst (λ F → k ⨾ `app (⇈ (`fun e)) (` Z) ◃ v ↦* k ▹ F ↝ 1# ∙ 1#) lem₂ step₄ in 
  let step₅ = ↦*-step (ke-app {e = e} {v = v} (⇓-val e⇓v)) (⇓→↦* e⇓v₁ k) in
  let step = ↦*-trans step₁₂' (↦*-trans step₃ (↦*-trans step₄' step₅)) in
  Eq.subst (λ c → k ▹ `app e₁ e₂ ↦* k ◃ v₁ ↝ c) effect-arithimic₁ step
  where
    lem₁ : `app (` Z) (⇈ e₂) [ `fun e ] ≡ `app (`fun e) e₂
    lem₁ rewrite shift-subst₁ (`fun e) e₂ = Eq.refl

    lem₂ : `app (⇈ (`fun e)) (` Z) [ v ] ≡ `app (`fun e) v
    lem₂ rewrite shift-subst₃ e v = Eq.refl
    
    effect-arithimic₁ : 1# ∙ a ∙ (1# ∙ 1#) ∙ (1# ∙ b ∙ (1# ∙ 1# ∙ (1# ∙ c))) ≡ a ∙ b ∙ c
    effect-arithimic₁ = 
      let open ≡-Reasoning in 
        1# ∙ a ∙ (1# ∙ 1#) ∙ (1# ∙ b ∙ (1# ∙ 1# ∙ (1# ∙ c)))
      ≡⟨ cong (λ d → 1# ∙ a ∙ d ∙ (1# ∙ b ∙ (1# ∙ 1# ∙ (1# ∙ c)))) (identityʳ 1#) ⟩ 
        1# ∙ a ∙ 1# ∙ (1# ∙ b ∙ (1# ∙ 1# ∙ (1# ∙ c)))
      ≡⟨ cong (λ d → d ∙ (1# ∙ b ∙ (1# ∙ 1# ∙ (1# ∙ c)))) (identityʳ (1# ∙ a)) ⟩ 
        1# ∙ a ∙ (1# ∙ b ∙ (1# ∙ 1# ∙ (1# ∙ c)))
      ≡⟨ cong (λ d → d ∙ (1# ∙ b ∙ (1# ∙ 1# ∙ (1# ∙ c)))) (identityˡ a) ⟩ 
        a ∙ (1# ∙ b ∙ (1# ∙ 1# ∙ (1# ∙ c)))
      ≡⟨ cong (λ d → a ∙ (d ∙ (1# ∙ 1# ∙ (1# ∙ c)))) (identityˡ b) ⟩ 
        a ∙ (b ∙ (1# ∙ 1# ∙ (1# ∙ c)))
      ≡⟨ cong (λ d → a ∙ (b ∙ (d ∙ (1# ∙ c)))) (identityʳ 1#) ⟩ 
        a ∙ (b ∙ (1# ∙ (1# ∙ c)))
      ≡⟨ cong (λ d → a ∙ (b ∙ d)) (identityˡ (1# ∙ c)) ⟩ 
        a ∙ (b ∙ (1# ∙ c))
      ≡⟨ cong (λ d → a ∙ (b ∙ d)) (identityˡ c) ⟩ 
        a ∙ (b ∙ c)
      ≡⟨ assoc a b c ⟨ 
        a ∙ b ∙ c
      ∎
⇓→↦* (be-eff e⇓v) k = ↦*-step ke-eff (⇓→↦* e⇓v k)
      