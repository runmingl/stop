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
    let step₁ = compatible se-case (⇓→↦* e⇓v↝a) in 
    let step₂ = ↦*-step se-case-z (⇓→↦* e⇓v↝b) in 
    let step₂' = Eq.subst (λ e → `case `zero _ _ ↦* _ ↝ e) (identityˡ b) step₂ in 
      ↦*-trans step₁ step₂'
  ⇓→↦* (be-case-s e⇓v↝a e⇓v↝b) with ⇓-val e⇓v↝a  
  ... | v-suc v-val =
    let step₁ = compatible se-case (⇓→↦* e⇓v↝a) in 
    let step₂ = ↦*-step (se-case-s {a = 1#} v-val) (⇓→↦* e⇓v↝b) in 
    let step₂' = Eq.subst (λ c → `case (`suc _) _ _ ↦* _ ↝ c) (identityˡ _) step₂ in
    ↦*-trans step₁ step₂'
  ⇓→↦* be-fun = ↦*-refl
  ⇓→↦* (be-app {e = e} e⇓v↝a e⇓v↝b e⇓v↝c) = 
    let step₁ = compatible se-app (⇓→↦* e⇓v↝a) in 
    let step₂ = compatible se-app₁ (⇓→↦* e⇓v↝b) in 
    let step₃ = ↦*-step (se-app₂ {e = e} (⇓-val e⇓v↝b)) (⇓→↦* e⇓v↝c) in 
    let step₃' = Eq.subst (λ c → `app (`fun e) _ ↦* _ ↝ c) (identityˡ _) step₃ in
    ↦*-trans 
      (↦*-trans step₁ step₂) step₃'
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
      
module StackMachine⇔BigStep where 

  open import StackMachine monoid
  open import BigStep monoid 

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
  ⇓→↦* (be-zero) k rewrite sym (identityʳ 1#) = ↦*-step ke-zero ↦*-refl
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
  ⇓→↦* (be-case-z {e = e} {e₁ = e₁} {e₂ = e₂} {a = a} {b = b} e⇓z e⇓v) k rewrite sym (effect-arithimic₁ a b) = 
    let step₁ = ↦*-step (ke-case {e₁ = e₁} {e₂ = e₂}) (⇓→↦* e⇓z (k ⨾ _)) in 
    let step₂ = ↦*-step ke-case-z (⇓→↦* e⇓v k) in
      ↦*-trans step₁ step₂
  ⇓→↦* (be-case-s {e = e} {v = v} {e₁ = e₁} {v₁ = v₁} {e₂ = e₂} {a = a} {b = b} e⇓s e⇓v) k rewrite sym (effect-arithimic₁ a b) = 
    let step₁ = ↦*-step (ke-case {e₁ = e₁} {e₂ = e₂} {e = e}) (⇓→↦* e⇓s (k ⨾ _)) in 
    let step₂ = ↦*-step ke-case-s (⇓→↦* e⇓v k) in
      ↦*-trans step₁ step₂
  ⇓→↦* (be-fun) k rewrite sym (identityʳ 1#) = ↦*-step ke-fun ↦*-refl
  ⇓→↦* (be-app {e₁ = e₁} {e = e} {e₂ = e₂} {v = v} {v₁ = v₁} {a} {b} {c} e⇓f e⇓v e⇓v₁) k rewrite sym (effect-arithimic₂ a b c) = 
    let step₁ = ↦*-step (ke-app₁ {e₁ = e₁} {e₂ = e₂}) (⇓→↦* e⇓f (k ⨾ _)) in 
    let step₂ = ↦*-step (ke-app₂ {k = k} {e = e} {e₂ = e₂}) (⇓→↦* e⇓v (k ⨾ _)) in
    let step₃ = ↦*-step (ke-app₃ {e = e}) (⇓→↦* e⇓v₁ k) in
      ↦*-trans step₁ (↦*-trans step₂ step₃)
  ⇓→↦* (be-eff e⇓v) k = ↦*-step ke-eff (⇓→↦* e⇓v k)
  
  infix 4 _⟪_ 
  _⟪_ : · ⊢ τ → · ⊢ τ → Set ℓ 
  _⟪_ {τ} e d = (Σ[ v ∈ · ⊢ τ ] Σ[ a ∈ Effect ] (e ⇓ v ↝ a)) → Σ[ v ∈ · ⊢ τ ] Σ[ a ∈ Effect ] (e ⇓ v ↝ a) × (d ⇓ v ↝ a)

  ⟪-● : {K : Frame} {e d : · ⊢ τ} →
      (k : K ÷ τ) → 
      e ⟪ d 
    ------------------------
    → k ● e ⟪ k ● d 
  ⟪-● ε f H = f H
  ⟪-● (K ⨾ suc⟨-⟩) f =
    ⟪-● K (λ { (`suc v , a , be-suc e⇓v) → let (v , a , e⇓v , d⇓v) = f (v , a , e⇓v) in `suc v , a , be-suc e⇓v , be-suc d⇓v })
  ⟪-● (K ⨾ case⟨-⟩ e₁ e₂) f = ⟪-● K λ { (v , _ , be-case-z {a = a} {b = b} p p₁) → 
      let t = f (`zero , a , p) in 
      let t₁ = f ({! v  !} , b , {!   !}) in {!   !} , {!   !} , be-case-z p p₁ , {!   !}
                                      ; (v , a , be-case-s p p₁) → {!   !}}
  ⟪-● (K ⨾ app⟨-⟩ e₂) f = ⟪-● K (λ { (v , a , p) → let t = {! f (v , a , p)  !} in {!   !} })
  ⟪-● (K ⨾ app e₁ ⟨-⟩) f = ⟪-● K λ { (v , a , be-app p p₁ p₂) → let t = f ({!  v !} , {!   !} , {!   !}) in {!   !} }

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
  
  thm : {s s' : State} {a : Effect} → (transition : s ↦ s' ↝ a) → goal s s' (return-≡ transition)
  thm ke-zero (v , a , e⇓v) = v , a , e⇓v , e⇓v
  thm ke-suc₁ (v , a , e⇓v) = v , a , e⇓v , e⇓v
  thm ke-suc₂ v-val (v , a , e⇓v) = v , a , e⇓v , e⇓v
  thm ke-case (v , a , e⇓v) = v , a , e⇓v , e⇓v 
  thm (ke-case-z {k = k}) v-zero = ⟪-● k λ (v , a , e⇓v) → v , a , e⇓v , Eq.subst (λ a → _ ⇓ _ ↝ a) (identityˡ a) (be-case-z be-zero e⇓v)
  thm (ke-case-s {k = k}) (v-suc v-val) = ⟪-● k (λ (v , a , e⇓v) → v , a , e⇓v , Eq.subst (λ a → _ ⇓ _ ↝ a) (identityˡ a) (be-case-s (v⇓v (v-suc v-val)) e⇓v))
  thm ke-fun (v , a , e⇓v) = v , a , e⇓v , e⇓v
  thm ke-app₁ (v , a , e⇓v) = v , a , e⇓v , e⇓v
  thm ke-app₂ v-fun (v , a , e⇓v) = v , a , e⇓v , e⇓v
  thm ke-app₃ v-val = {!   !}
  thm (ke-eff {k = k}) = ⟪-● k λ (v , a , e⇓v) → v , a , e⇓v , Eq.subst (λ a → _ ⇓ _ ↝ a) (identityˡ a) {! be-eff  !} 

  mutual
    ▹-val : {K : Frame} {k : K ÷ τ} {e : · ⊢ τ} {k' : K ÷ σ} {e' : · ⊢ σ} {a : Effect}→
        k ▹ e ↦* k' ◃ e' ↝ a 
      ------------------------
      → e' val
    ▹-val (↦*-step {s' = x₁ ◃ x₂} x d) = ◃-val {! d  !} {!   !}
    ▹-val (↦*-step {s' = x₁ ▹ x₂} x d) = ▹-val {! d  !}

    ◃-val : {K : Frame} {k : K ÷ τ} {e : · ⊢ τ} {k' : K ÷ σ} {e' : · ⊢ σ} {a : Effect} → 
        k ◃ e ↦* k' ◃ e' ↝ a 
      → e val
      ------------------------
      → e' val
    ◃-val ↦*-refl v-val = {!   !}
    ◃-val (↦*-step x d) v-val = {!   !} 