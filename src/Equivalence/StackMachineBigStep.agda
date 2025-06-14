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

⇓→↦*-ε : {e v : · ⊢ τ} {a : Effect} → 
      e ⇓ v ↝ a  
    ------------------------
    → ε ▹ e ↦* ε ◃ v ↝ a
⇓→↦*-ε e⇓v = ⇓→↦* e⇓v ε
  
infix 4 _⟪_∣_
_⟪_∣_ : · ⊢ τ → · ⊢ τ → Effect → Set ℓ 
_⟪_∣_ {τ} e d a = {v : · ⊢ τ} {b : Effect} → (c : Effect) →  
    c ≡ a ∙ b 
  → e ⇓ v ↝ b 
  ------------------------
  → d ⇓ v ↝ c

⟪-● : {K : Frame} {e d : · ⊢ τ} {a : Effect} →
    (k : K ÷ τ) 
  → e ⟪ d ∣ a
  ------------------------
  → k ● e ⟪ k ● d ∣ a
⟪-● ε f = f
⟪-● {a = b} (K ⨾ suc⟨-⟩) f
  = ⟪-● K (λ { c' c'≡a'∙b (be-suc e⇓v) → be-suc (f c' c'≡a'∙b e⇓v) }) 
⟪-● {e = e} {d = d} {a = b} (K ⨾ case⟨-⟩ e₁ e₂) f 
  = ⟪-● K (λ { c' c'≡a'∙b (be-case-z {a = a} {b = c} e⇓z e⇓v) → 
      let step = be-case-z (f (b ∙ a) Eq.refl e⇓z) e⇓v in 
        Eq.subst 
          (λ a → `case d _ _ ⇓ _ ↝ a) 
          (Eq.trans (assoc b a c) (sym c'≡a'∙b)) 
          step
      ; c' c'≡a'∙b (be-case-s {a = a} {b = c} e⇓s e⇓v) → 
      let step = be-case-s (f (b ∙ a) Eq.refl e⇓s) e⇓v in 
        Eq.subst 
          (λ a → `case d _ _ ⇓ _ ↝ a) 
          (Eq.trans (assoc b a c) (sym c'≡a'∙b)) 
          step }) 
⟪-● {e = e} {d = d} {a = b} (K ⨾ app⟨-⟩ e₂) f 
  = ⟪-● K (λ { c' c'≡a'∙b (be-app {a = a} e⇓f e₂⇓v e⇓v) → 
      let step = be-app (f (b ∙ a) Eq.refl e⇓f) e₂⇓v e⇓v in 
        Eq.subst 
          (λ a → `app d _ ⇓ _ ↝ a) 
          (Eq.trans (Eq.trans (assoc (b ∙ _) _ _) (Eq.trans (assoc _ _ _) (cong (λ a → b ∙ a) (sym (assoc _ _ _))))) (sym c'≡a'∙b)) 
          step })
⟪-● {e = e} {d = d} {a = b} (K ⨾ app⟨fun e₁ ⟩⟨-⟩) f 
  = ⟪-● K λ { c' c'≡a'∙b (be-app {a = a} {b = c} {c = g} be-fun e₂⇓v e⇓v) → 
      let step = be-app be-fun (f (b ∙ c) Eq.refl e₂⇓v) e⇓v in 
        Eq.subst 
          (λ a → `app (`fun _) d ⇓ _ ↝ a) 
          (Eq.trans (cong (λ a → a ∙ g) (identityˡ (b ∙ c))) (Eq.trans (assoc b c g) (Eq.trans (cong (λ a → b ∙ (a ∙ g)) (sym (identityˡ c))) (sym c'≡a'∙b)))) 
          step }

mutual 
  ▹-↦*→⇓ : {K : Frame} {k : K ÷ τ} {e : · ⊢ τ} {v : · ⊢ return-type k} {a : Effect} → 
      k ▹ e ↦* ε ◃ v ↝ a  
    ------------------------
    → k ● e ⇓ v ↝ a
  ▹-↦*→⇓ {k = ε} (↦*-step {b = b} ke-zero s) rewrite identityˡ b = ◃-↦*→⇓-ε s v-zero
  ▹-↦*→⇓ {k = k ⨾ F} (↦*-step {b = b} ke-zero s) rewrite identityˡ b = ◃-↦*→⇓ s v-zero 
  ▹-↦*→⇓ (↦*-step {b = b} ke-suc₁ s) rewrite identityˡ b = ▹-↦*→⇓ s
  ▹-↦*→⇓ (↦*-step {b = b} ke-case s) rewrite identityˡ b = ▹-↦*→⇓ s
  ▹-↦*→⇓ {k = ε} (↦*-step {b = b} ke-fun s) rewrite identityˡ b = ◃-↦*→⇓-ε s v-fun 
  ▹-↦*→⇓ {k = k ⨾ F} (↦*-step {b = b} ke-fun s) rewrite identityˡ b = ◃-↦*→⇓ s v-fun 
  ▹-↦*→⇓ (↦*-step {b = b} ke-app₁ s) rewrite identityˡ b = ▹-↦*→⇓ s
  ▹-↦*→⇓ {k = k} (↦*-step {a = a} {b = b} ke-eff s) 
    = ⟪-● k 
      (λ c' c'≡a∙b' e⇓v → 
        let step = be-eff e⇓v in 
          Eq.subst (λ a → `eff _ _ ⇓ _ ↝ a) (sym c'≡a∙b') step) 
      (a ∙ b) Eq.refl (▹-↦*→⇓ s)

  ◃-↦*→⇓-ε : {e : · ⊢ τ} {v : · ⊢ τ} {a : Effect} → 
      ε ◃ e ↦* ε ◃ v ↝ a
    → e val
    ------------------------
    → ε ● e ⇓ v ↝ a
  ◃-↦*→⇓-ε ↦*-refl e-val = v⇓v e-val

  ◃-↦*→⇓ : {K : Frame} {k : K ÷ σ} {F : τ ⇝ σ} {e : · ⊢ τ} {v : · ⊢ return-type k} {a : Effect} → 
      k ⨾ F ◃ e ↦* ε ◃ v ↝ a  
    → e val
    ------------------------
    → (k ⨾ F) ● e ⇓ v ↝ a
  ◃-↦*→⇓ {k = ε} (↦*-step {b = b} ke-suc₂ s) e-val rewrite identityˡ b = ◃-↦*→⇓-ε s (v-suc e-val)
  ◃-↦*→⇓ {k = k ⨾ F} (↦*-step {b = b} ke-suc₂ s) e-val rewrite identityˡ b = ◃-↦*→⇓ s (v-suc e-val)
  ◃-↦*→⇓ {k = k} (↦*-step {b = b} ke-case-z s) v-zero 
    = ⟪-● k 
      (λ b' b'≡b e₁⇓v → 
        let step = be-case-z be-zero e₁⇓v in 
          Eq.subst (λ a → `case `zero _ _ ⇓ _ ↝ a) (sym b'≡b) step) 
      (1# ∙ b) Eq.refl (▹-↦*→⇓ s)
  ◃-↦*→⇓ {k = k} (↦*-step {b = b} ke-case-s s) (v-suc v-val) 
    = ⟪-● k (λ b' b'≡b e₂⇓v → 
        let step = be-case-s (be-suc (v⇓v v-val)) e₂⇓v in 
          Eq.subst (λ a → `case (`suc _) _ _ ⇓ _ ↝ a) (sym b'≡b) step)
      (1# ∙ b) Eq.refl (▹-↦*→⇓ s)
  ◃-↦*→⇓ {k = k} (↦*-step {b = b} ke-app₂ s) v-fun rewrite identityˡ b = ▹-↦*→⇓ s
  ◃-↦*→⇓ {k = k} (↦*-step {b = b} ke-app₃ s) e-val 
    = ⟪-● k (λ c' c'≡a∙b' e⇓v → 
        let step = be-app be-fun (v⇓v e-val) e⇓v in 
          Eq.subst (λ a → `app (`fun _) _ ⇓ _ ↝ a) (Eq.trans (Eq.cong (λ a → a ∙ _) (identityʳ 1#)) (sym c'≡a∙b')) step) 
      (1# ∙ b) Eq.refl (▹-↦*→⇓ s)

↦*→⇓-ε : {e v : · ⊢ τ} {a : Effect} → 
      ε ▹ e ↦* ε ◃ v ↝ a
    ------------------------
    → e ⇓ v ↝ a  
↦*→⇓-ε e↦*v = ▹-↦*→⇓ e↦*v

↦*⇔⇓ : {e v : · ⊢ τ} {a : Effect} → 
      ε ▹ e ↦* ε ◃ v ↝ a
    ------------------------
    ⇔ 
    ------------------------
      e ⇓ v ↝ a 
↦*⇔⇓ = ↦*→⇓-ε , ⇓→↦*-ε
