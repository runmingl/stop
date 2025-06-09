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
  ↦*→⇓ {e = e} v-val ↦*-refl                  = v⇓v v-val
  ↦*→⇓ v-val (↦*-step {a = a} e↦e'↝a e'↦*v↝b) = ↦→⇓ e↦e'↝a (↦*→⇓ v-val e'↦*v↝b)
    where 
      ↦→⇓ : {e e' v : · ⊢ τ} {a b : Effect} → 
          e ↦ e' ↝ a 
        → e' ⇓ v ↝ b 
        ------------------------
        → e ⇓ v ↝ a ∙ b 
      ↦→⇓ (se-suc e↦e'↝a) (be-suc e'⇓v↝b)                 
          = be-suc (↦→⇓ e↦e'↝a e'⇓v↝b)
      ↦→⇓ {a = a} (se-case e↦e'↝a) (be-case-z {a = c} {b = d} e'⇓z↝c e'⇓v↝d) 
        rewrite sym (assoc a c d) 
          = be-case-z (↦→⇓ e↦e'↝a e'⇓z↝c) e'⇓v↝d
      ↦→⇓ {a = a} (se-case e↦e'↝a) (be-case-s {a = c} {b = d} e'⇓s↝c e'⇓v↝d) 
        rewrite sym (assoc a c d) 
          = be-case-s (↦→⇓ e↦e'↝a e'⇓s↝c) e'⇓v↝d
      ↦→⇓ se-case-z e'⇓v↝b 
          = be-case-z (be-zero) e'⇓v↝b
      ↦→⇓ (se-case-s {v = v} v-val) e'⇓v↝b 
          = be-case-s (v⇓v (v-suc v-val)) e'⇓v↝b 
      ↦→⇓ {a = a} (se-app e↦e'↝a) (be-app {a = b} {b = c} {c = d} e'⇓v↝b e'⇓v↝c e'⇓v↝d) 
        rewrite trans (sym (assoc a (b ∙ c) d)) (cong (λ e → e ∙ d) (sym (assoc a b c))) 
          = be-app (↦→⇓ e↦e'↝a e'⇓v↝b) e'⇓v↝c e'⇓v↝d
      ↦→⇓ {a = a} (se-app₁ e↦e'↝a) (be-app {e = e} {a = b} {b = c} {c = d} (be-fun) e'⇓v↝c e'⇓v↝d) 
        rewrite trans (cong (λ e → a ∙ (e ∙ d)) (identityˡ c)) 
                (trans (sym (assoc a c d)) (cong (λ e → e ∙ d) (sym (identityˡ (a ∙ c))))) 
          = be-app be-fun (↦→⇓ e↦e'↝a e'⇓v↝c) e'⇓v↝d 
      ↦→⇓ {b = b} (se-app₂ {e = e} {v = v} v-val) e'⇓v↝b 
        rewrite trans (cong (λ a → 1# ∙ a) (sym (identityˡ b))) (sym (assoc 1# 1# b)) 
          = be-app be-fun (v⇓v v-val) e'⇓v↝b 
      ↦→⇓ se-eff e'⇓v↝b 
          = be-eff e'⇓v↝b
      
  ⇓→↦* : {e v : · ⊢ τ} {a : Effect} → 
      e ⇓ v ↝ a 
    ------------------------
    → e ↦* v ↝ a
  ⇓→↦* be-zero = ↦*-refl
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
  ⇓→↦* be-fun = ↦*-refl
  ⇓→↦* (be-app {e = e} e⇓v↝a e⇓v↝b e⇓v↝c) = 
    let `app_e₁_e₂↦*`app_`fun_e_e₂↝a = compatible se-app (⇓→↦* e⇓v↝a) in 
    let `app_`fun_e_e₂↦*`app_`fun_e_v↝b = compatible se-app₁ (⇓→↦* e⇓v↝b) in 
    let `app_`fun_e_v↦*v₁↝1∙c = ↦*-step (se-app₂ {e = e} (⇓-val e⇓v↝b)) (⇓→↦* e⇓v↝c) in 
    let `app_`fun_e_v↦*v₁↝c = Eq.subst (λ c → `app (`fun e) _ ↦* _ ↝ c) (identityˡ _) `app_`fun_e_v↦*v₁↝1∙c in
    ↦*-trans 
      (↦*-trans `app_e₁_e₂↦*`app_`fun_e_e₂↝a `app_`fun_e_e₂↦*`app_`fun_e_v↝b) `app_`fun_e_v↦*v₁↝c
  ⇓→↦* (be-eff e⇓v↝a) = ↦*-step se-eff (⇓→↦* e⇓v↝a)

  ↦*⇔⇓ : {e v : · ⊢ τ} {a : Effect} → (v val) × (e ↦* v ↝ a) ⇔ e ⇓ v ↝ a
  ↦*⇔⇓ = (λ (v-val , e↦*v↝a) → ↦*→⇓ v-val e↦*v↝a) , λ e⇓v↝a → ⇓-val e⇓v↝a , ⇓→↦* e⇓v↝a 


module KMachine⇔BigStep where 

  open import KMachine monoid
  open import BigStep monoid 

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
      