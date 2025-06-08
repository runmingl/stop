{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (cong; _≡_; module ≡-Reasoning)

module Equivalence {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid
open import Substitution monoid

private
  variable
    τ σ : Type

module SmallStep⇔BigStep where 

  open import SmallStep monoid
  open import BigStep monoid 

  ↦*→⇓ : {e v : · ⊢ τ} {a : Effect} → 
      v val 
    → e ↦* v ↝ a 
    ------------------------
    → e ⇓ v ↝ a
  ↦*→⇓ {e = e} v-val ↦*-refl                  = be-val {e = e} {a = 1#} v-val
  ↦*→⇓ v-val (↦*-step {a = a} e↦e'↝a e'↦*v↝b) = ↦→⇓ e↦e'↝a (↦*→⇓ v-val e'↦*v↝b)
    where 
      ↦→⇓ : {e e' v : · ⊢ τ} {a b : Effect} → 
          e ↦ e' ↝ a 
        → e' ⇓ v ↝ b 
        ------------------------
        → e ⇓ v ↝ a ∙ b 
      ↦→⇓ (se-suc e↦e'↝a) (be-suc e'⇓v↝b)                 
          = be-suc (↦→⇓ e↦e'↝a e'⇓v↝b)
      ↦→⇓ (se-suc {e' = v} e↦e'↝a) (be-val (v-suc v-val)) 
          = be-suc (↦→⇓ e↦e'↝a (be-val {e = v} {a = 1#} v-val))
      ↦→⇓ {a = a} (se-case e↦e'↝a) (be-case-z {a = c} {b = d} e'⇓z↝c e'⇓v↝d) 
        rewrite sym (assoc a c d) 
          = be-case-z (↦→⇓ e↦e'↝a e'⇓z↝c) e'⇓v↝d
      ↦→⇓ {a = a} (se-case e↦e'↝a) (be-case-s {a = c} {b = d} e'⇓s↝c e'⇓v↝d) 
        rewrite sym (assoc a c d) 
          = be-case-s (↦→⇓ e↦e'↝a e'⇓s↝c) e'⇓v↝d
      ↦→⇓ se-case-z e'⇓v↝b 
          = be-case-z (be-val {e = `zero} {a = 1#} v-zero) e'⇓v↝b
      ↦→⇓ (se-case-s {v = v} v-val) e'⇓v↝b 
          = be-case-s (be-val {e = `suc v} {a = 1#} (v-suc v-val)) e'⇓v↝b
      ↦→⇓ {a = a} (se-app e↦e'↝a) (be-app {a = b} {b = c} {c = d} e'⇓v↝b e'⇓v↝c e'⇓v↝d) 
        rewrite trans (sym (assoc a (b ∙ c) d)) (cong (λ e → e ∙ d) (sym (assoc a b c))) 
          = be-app (↦→⇓ e↦e'↝a e'⇓v↝b) e'⇓v↝c e'⇓v↝d
      ↦→⇓ {a = a} (se-app₁ e↦e'↝a) (be-app {e = e} {a = b} {b = c} {c = d} (be-val v-fun) e'⇓v↝c e'⇓v↝d) 
        rewrite trans (cong (λ e → a ∙ (e ∙ d)) (identityˡ c)) 
                (trans (sym (assoc a c d)) (cong (λ e → e ∙ d) (sym (identityˡ (a ∙ c))))) 
          = be-app (be-val {e = `fun e} {a = 1#} v-fun) (↦→⇓ e↦e'↝a e'⇓v↝c) e'⇓v↝d 
      ↦→⇓ {b = b} (se-app₂ {e = e} {v = v} v-val) e'⇓v↝b 
        rewrite trans (cong (λ a → 1# ∙ a) (sym (identityˡ b))) (sym (assoc 1# 1# b)) 
          = be-app (be-val {e = `fun e} {a = 1#} v-fun) (be-val {e = v} {a = 1#} v-val) e'⇓v↝b
      ↦→⇓ se-eff e'⇓v↝b 
          = be-eff e'⇓v↝b
      
  ⇓→↦* : {e v : · ⊢ τ} {a : Effect} → 
      e ⇓ v ↝ a 
    ------------------------
    → e ↦* v ↝ a
  ⇓→↦* (be-suc e⇓v↝a) = compatible {p = `suc} se-suc (⇓→↦* e⇓v↝a)
  ⇓→↦* (be-case-z {e = e} {e₁ = e₁} {e₂ = e₂} {b = b} e⇓v↝a e⇓v↝b) = 
    let `case_e_e₁_e₂↦*`case_`zero_e₁_e₂↝a = compatible se-case (⇓→↦* e⇓v↝a) in 
    let `case_`zero_e₁_e₂↦*v↝1∙b = ↦*-step se-case-z (⇓→↦* e⇓v↝b) in 
    let `case_`zero_e₁_e₂↦*v↝b = Eq.subst (λ e → `case `zero _ _ ↦* _ ↝ e) (identityˡ b) `case_`zero_e₁_e₂↦*v↝1∙b in 
    ↦*-trans `case_e_e₁_e₂↦*`case_`zero_e₁_e₂↝a `case_`zero_e₁_e₂↦*v↝b
  ⇓→↦* (be-case-s e⇓v↝a e⇓v↝b) with ⇓-val e⇓v↝a  
  ... | v-suc v-val =
    let `case_e_e₁_e₂↦*`case_`sucv_e₁_e₂↝a = compatible se-case (⇓→↦* e⇓v↝a) in 
    let `case_`sucv_e₁_e₂↦*v↝1∙b = ↦*-step (se-case-s {a = 1#} v-val) (⇓→↦* e⇓v↝b) in 
    let `case_`sucv_e₁_e₂↦*v↝b = Eq.subst (λ c → `case (`suc _) _ _ ↦* _ ↝ c) (identityˡ _) `case_`sucv_e₁_e₂↦*v↝1∙b in
    ↦*-trans `case_e_e₁_e₂↦*`case_`sucv_e₁_e₂↝a `case_`sucv_e₁_e₂↦*v↝b
  ⇓→↦* (be-app {e = e} e⇓v↝a e⇓v↝b e⇓v↝c) = 
    let `app_e₁_e₂↦*`app_`fun_e_e₂↝a = compatible se-app (⇓→↦* e⇓v↝a) in 
    let `app_`fun_e_e₂↦*`app_`fun_e_v↝b = compatible se-app₁ (⇓→↦* e⇓v↝b) in 
    let `app_`fun_e_v↦*v₁↝1∙c = ↦*-step (se-app₂ {e = e} (⇓-val e⇓v↝b)) (⇓→↦* e⇓v↝c) in 
    let `app_`fun_e_v↦*v₁↝c = Eq.subst (λ c → `app (`fun e) _ ↦* _ ↝ c) (identityˡ _) `app_`fun_e_v↦*v₁↝1∙c in
    ↦*-trans 
      (↦*-trans `app_e₁_e₂↦*`app_`fun_e_e₂↝a `app_`fun_e_e₂↦*`app_`fun_e_v↝b) `app_`fun_e_v↦*v₁↝c
  ⇓→↦* (be-eff e⇓v↝a) = ↦*-step se-eff (⇓→↦* e⇓v↝a)
  ⇓→↦* (be-val _) = ↦*-refl
  
  ↦*⇔⇓ : {e v : · ⊢ τ} {a : Effect} → (v val) × (e ↦* v ↝ a) ⇔ e ⇓ v ↝ a
  ↦*⇔⇓ = (λ (v-val , e↦*v↝a) → ↦*→⇓ v-val e↦*v↝a) , λ e⇓v↝a → ⇓-val e⇓v↝a , ⇓→↦* e⇓v↝a 


module KMachine⇔BigStep where 

  open import KMachine monoid
  open import BigStep monoid 

  ⇓→↦* : {e v : · ⊢ τ} {a : Effect} {K : Frame} → 
        e ⇓ v ↝ a 
      → (k : K ÷ τ) 
      ------------------------
      → k ▹ e ↦* k ◃ v ↝ a
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
  ⇓→↦* (be-case-z {e₁ = e₁} {e₂ = e₂} e⇓z e⇓v) k = 
    let step₁ = ↦*-step (ke-case {e₁ = e₁} {e₂ = e₂}) (⇓→↦* e⇓z (k ⨾ `case (` Z) (⇈ e₁) (⇈ e₂))) in 
    let step₂ = (↦*-step (ke-pop v-zero) (↦*-step ke-case-z (⇓→↦* e⇓v k))) in 
    -- let step = ↦*-trans step₁ step₂ in
    {!   !}
    where 
      lem₁ : (⇈ e₁) [ `zero ] ≡ e₁ 
      lem₁ = 
        Eq.trans (subst-eq id-γ (⇈ e₁) `zero) 
        (Eq.trans (Eq.sym (combine-subst `_ (⇈ e₁) `zero)) {! subst (extend `zero `_) ∘ (weaken `_)  !})
      --subst (extend M' γ) M ≡ subst (extend M' `_) (subst (weaken γ) M)
      --subst (extend `zero `_) (subst (weaken `_) (subst (λ x → ` S x) e₁))

      lem₂ : (⇈ e₂) [ `zero ] ≡ e₂
      lem₂ = {!   !}

      lem : `case (` Z) (⇈ e₁) (⇈ e₂) [ `zero ] ≡ `case `zero e₁ e₂
      lem rewrite lem₁ rewrite lem₂ = {!   !}
  ⇓→↦* (be-case-s e⇓v e⇓v₁) k = {!   !}
  ⇓→↦* (be-app e⇓v e⇓v₁ e⇓v₂) k = {!   !}
  ⇓→↦* (be-eff e⇓v) k = ↦*-step ke-eff (⇓→↦* e⇓v k)
  ⇓→↦* (be-val v-val) k rewrite sym (identityʳ 1#) = ↦*-step (ke-val v-val) ↦*-refl
      