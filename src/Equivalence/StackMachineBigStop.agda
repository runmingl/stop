open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

module Equivalence.StackMachineBigStop {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

open import Language.StackMachine monoid
open import Language.BigStop monoid 

open import Equivalence.SmallStepBigStop monoid using (⇩-trans)

private
  variable
    τ : Type

effect-arithimic₁ : (a b : Effect) → 1# ∙ a ∙ (1# ∙ b) ≡ a ∙ b
effect-arithimic₁ a b = 
  let open ≡-Reasoning in 
    1# ∙ a ∙ (1# ∙ b) 
  ≡⟨ Eq.cong (λ b → (1# ∙ a) ∙ b) (identityˡ b) ⟩ 
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
  ≡⟨ Eq.cong (λ a → a ∙ _) (identityˡ a) ⟩ 
    a ∙ (1# ∙ b ∙ (1# ∙ c))
  ≡⟨ Eq.cong (λ b → a ∙ (b ∙ _)) (identityˡ b) ⟩ 
    a ∙ (b ∙ (1# ∙ c))
  ≡⟨ Eq.cong (λ c → a ∙ (b ∙ c)) (identityˡ c) ⟩ 
    a ∙ (b ∙ c)
  ≡⟨ assoc a b c ⟨ 
    a ∙ b ∙ c
  ∎

⇩→↦* : {e v : · ⊢ τ} {a : Effect} {K : Frame} → 
    e ⇩ v ↝ a 
  → v val 
  → (k : K ÷ τ) 
  ------------------------
  → k ▹ e ↦* k ◃ v ↝ a
⇩→↦* ste-zero v-zero k = k▹v↦*k◃v v-zero
⇩→↦* (ste-suc {a = a} e⇩v) (v-suc v-val) k = 
  let step₁ = ↦*-step ke-suc₁ (⇩→↦* e⇩v v-val (k ⨾ suc⟨-⟩)) in
  let step₂ = ↦*-step ke-suc₂ ↦*-refl in 
  let step = ↦*-trans step₁ step₂ in
  Eq.subst (λ a → k ▹ `suc _ ↦* k ◃ `suc _ ↝ a) eq step
    where 
    eq : 1# ∙ a ∙ (1# ∙ 1#) ≡ a 
    eq = 
      let open ≡-Reasoning in 
        1# ∙ a ∙ (1# ∙ 1#)
      ≡⟨ Eq.cong (λ b → (1# ∙ a) ∙ b) (identityʳ 1#) ⟩ 
        1# ∙ a ∙ 1# 
      ≡⟨ identityʳ (1# ∙ a) ⟩  
        1# ∙ a 
      ≡⟨ identityˡ a ⟩ 
        a 
      ∎ 
⇩→↦* ste-fun v-val k = k▹v↦*k◃v v-fun
⇩→↦* (ste-app {a = a} {b = b} {c = c} e⇩f e₂⇩v₂ v₂-val e⇩v₁) v-val k rewrite Eq.sym (effect-arithimic₂ a b c) = 
  let step₁ = ↦*-step ke-app₁ (⇩→↦* e⇩f v-fun (k ⨾ _)) in 
  let step₂ = ↦*-step ke-app₂ (⇩→↦* e₂⇩v₂ v₂-val (k ⨾ _)) in
  let step₃ = ↦*-step ke-app₃ (⇩→↦* e⇩v₁ v-val k) in
    ↦*-trans step₁ (↦*-trans step₂ step₃)
⇩→↦* (ste-case-z {a = a} {b = b} e⇩z e⇩v) v-val k rewrite Eq.sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇩→↦* e⇩z v-zero (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-z (⇩→↦* e⇩v v-val k) in
    ↦*-trans step₁ step₂
⇩→↦* (ste-case-s {a = a} {b = b} e⇩s v₁-val e⇩v) v-val k rewrite Eq.sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇩→↦* e⇩s (v-suc v₁-val) (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-s (⇩→↦* e⇩v v-val k) in
    ↦*-trans step₁ step₂
⇩→↦* (ste-eff e⇩v) v-val k = ↦*-step ke-eff (⇩→↦* e⇩v v-val k)
⇩→↦* ste-stop v-val k = k▹v↦*k◃v v-val

{-
  Convergent Completeness
-}
⇩→↦*-ε : {e v : · ⊢ τ} {a : Effect} → 
    e ⇩ v ↝ a 
  → v val 
  ------------------------
  → ε ▹ e ↦* ε ◃ v ↝ a
⇩→↦*-ε e⇩v v-val = ⇩→↦* e⇩v v-val ε

⇩→↦*s : {e e' : · ⊢ τ} {a : Effect} {K : Frame} → 
    e ⇩ e' ↝ a 
  → (k : K ÷ τ) 
  ------------------------
  → Σ[ s ∈ State ] (k ▹ e ↦* s ↝ a)
⇩→↦*s ste-zero k = k ▹ `zero , ↦*-refl
⇩→↦*s (ste-suc {a = a} e⇩e') k with ⇩→↦*s e⇩e' (k ⨾ suc⟨-⟩)   
... | s , k'▹e↦*s = s , Eq.subst (λ a → k ▹ `suc _ ↦* s ↝ a) (identityˡ a) (↦*-step ke-suc₁ k'▹e↦*s)
⇩→↦*s (ste-fun {e = e}) k = k ▹ `fun e , ↦*-refl
⇩→↦*s (ste-app-seq₁ {a = a} e⇩e') k with ⇩→↦*s e⇩e' (k ⨾ app⟨-⟩ _)
... | s , k'▹e↦*s = s , Eq.subst (λ a → k ▹ `app _ _ ↦* s ↝ a) (identityˡ a) (↦*-step ke-app₁ k'▹e↦*s)
⇩→↦*s (ste-app-seq₂ {a = a} {b = b} e⇩f e⇩e'') k with ⇩→↦*s e⇩e'' (k ⨾ _)
... | s , k'▹e↦*s rewrite Eq.sym (effect-arithimic₁ a b) =   
  let step₁ = ↦*-step ke-app₁ (⇩→↦* e⇩f v-fun (k ⨾ app⟨-⟩ _)) in 
  let step₂ = ↦*-step ke-app₂ k'▹e↦*s in 
    s , ↦*-trans step₁ step₂
⇩→↦*s (ste-app {a = a} {b = b} {c = c} e⇩f e₂⇩v₂ v₂-val e⇩v₁) k with ⇩→↦*s e⇩v₁ k 
... | s , k'▹e↦*s rewrite Eq.sym (effect-arithimic₂ a b c) = 
  let step₁ = ↦*-step ke-app₁ (⇩→↦* e⇩f v-fun (k ⨾ app⟨-⟩ _)) in 
  let step₂ = ↦*-step ke-app₂ (⇩→↦* e₂⇩v₂ v₂-val (k ⨾ _)) in
  let step₃ = ↦*-step ke-app₃ k'▹e↦*s in
    s , ↦*-trans step₁ (↦*-trans step₂ step₃)
⇩→↦*s (ste-case-seq {a = a} e⇩e') k with ⇩→↦*s e⇩e' (k ⨾ case⟨-⟩ _ _)
... | s , k'▹e↦*s = s , Eq.subst (λ a → k ▹ `case _ _ _ ↦* s ↝ a) (identityˡ a) (↦*-step ke-case k'▹e↦*s)
⇩→↦*s (ste-case-z {a = a} {b = b} e⇩z e⇩e') k with ⇩→↦*s e⇩e' k
... | s , k▹e↦*s rewrite Eq.sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇩→↦* e⇩z v-zero (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-z k▹e↦*s in
    s , ↦*-trans step₁ step₂
⇩→↦*s (ste-case-s {a = a} {b = b} e⇩s v₁-val e⇩e') k with ⇩→↦*s e⇩e' k
... | s , k▹e↦*s rewrite Eq.sym (effect-arithimic₁ a b) = 
  let step₁ = ↦*-step ke-case (⇩→↦* e⇩s (v-suc v₁-val) (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-s k▹e↦*s in
    s ,  ↦*-trans step₁ step₂
⇩→↦*s (ste-eff {e' = e'} e⇩e') k with ⇩→↦*s e⇩e' k 
... | s , k▹e↦*s = s , ↦*-step ke-eff k▹e↦*s
⇩→↦*s (ste-stop {e = e}) k = k ▹ e , ↦*-refl 

{-
  Divergent Completeness
-}
⇩→↦*s-ε : {e e' : · ⊢ τ} {a : Effect} {K : Frame} → 
    e ⇩ e' ↝ a 
  ------------------------
  → Σ[ s ∈ State ] (ε ▹ e ↦* s ↝ a)
⇩→↦*s-ε e⇩e' = ⇩→↦*s e⇩e' ε

infix 4 _⟪_∣_
_⟪_∣_ : · ⊢ τ → · ⊢ τ → Effect → Set ℓ 
_⟪_∣_ {τ} e d a = {e' : · ⊢ τ} {b : Effect} → (c : Effect) →  
    c ≡ a ∙ b 
  → e ⇩ e' ↝ b 
  ------------------------
  → d ⇩ e' ↝ c

⟪-● : {K : Frame} {e d : · ⊢ τ} {a : Effect} →
    (k : K ÷ τ) 
  → e ⟪ d ∣ a
  ------------------------
  → k ● e ⟪ k ● d ∣ a
⟪-● ε f = f
⟪-● {a = b} (K ⨾ suc⟨-⟩) f
  = ⟪-● K λ { c' c'≡a'∙b (ste-suc e⇩e') → ste-suc (f c' c'≡a'∙b e⇩e')
            ; c' c'≡a'∙b ste-stop → ste-suc (f c' c'≡a'∙b ste-stop) }
⟪-● {e = e} {d = d} {a = b} (K ⨾ case⟨-⟩ e₁ e₂) f 
  = ⟪-● K λ { c' c'≡a'∙b (ste-case-seq e⇩e') → ste-case-seq (f c' c'≡a'∙b e⇩e')
            ; c' c'≡a'∙b (ste-case-z {a = a} {b = c} e⇩z e⇩e') → 
          let step = ste-case-z (f (b ∙ a) Eq.refl e⇩z) e⇩e' in  
            Eq.subst 
              (λ a → `case d _ _ ⇩ _ ↝ a) 
              (Eq.trans (assoc b a c) (Eq.sym c'≡a'∙b)) 
              step
            ; c' c'≡a'∙b (ste-case-s {a = a} {b = c} e⇩s v-val e⇩e') → 
          let step = ste-case-s (f (b ∙ a) Eq.refl e⇩s) v-val e⇩e' in 
            Eq.subst 
              (λ a → `case d _ _ ⇩ _ ↝ a) 
              (Eq.trans (assoc b a c) (Eq.sym c'≡a'∙b)) 
              step
            ; c' c'≡a'∙b ste-stop → ste-case-seq (f c' c'≡a'∙b ste-stop) }
⟪-● {e = e} {d = d} {a = b} (K ⨾ app⟨-⟩ e₂) f 
  = ⟪-● K λ { c' c'≡a'∙b (ste-app-seq₁ e⇩e') → ste-app-seq₁ (f c' c'≡a'∙b e⇩e')
            ; c' c'≡a'∙b (ste-app-seq₂ {a = a} {b = c} e⇩f e⇩e') → 
          let step = ste-app-seq₂ (f (b ∙ a) Eq.refl e⇩f) e⇩e' in 
            Eq.subst 
              (λ a → `app d _ ⇩ `app (`fun _) _ ↝ a) 
              (Eq.trans (assoc b a c) (Eq.sym c'≡a'∙b)) 
              step
            ; c' c'≡a'∙b (ste-app {a = a} e⇩f e₂⇩v v-val e⇩e') → 
          let step = ste-app (f (b ∙ a) Eq.refl e⇩f) e₂⇩v v-val e⇩e' in 
            Eq.subst 
              (λ a → `app d _ ⇩ _ ↝ a) 
              (Eq.trans (Eq.trans (assoc (b ∙ _) _ _) (Eq.trans (assoc _ _ _) (Eq.cong (λ a → b ∙ a) (Eq.sym (assoc _ _ _))))) (Eq.sym c'≡a'∙b)) 
              step
            ; c' c'≡a'∙b ste-stop → ste-app-seq₁ (f c' c'≡a'∙b ste-stop) }
⟪-● {e = e} {d = d} {a = b} (K ⨾ app⟨fun e₁ ⟩⟨-⟩) f 
  = ⟪-● K λ { c' c'≡a'∙b (ste-app-seq₁ ste-fun) → 
          let step = ste-app-seq₂ ste-fun (f c' c'≡a'∙b ste-stop) in 
            Eq.subst 
              (λ a → `app (`fun _) d ⇩ `app (`fun _) e ↝ a) 
              (identityˡ c') 
              step
            ; c' c'≡a'∙b (ste-app-seq₁ ste-stop) → 
          let step = ste-app-seq₂ ste-fun (f c' c'≡a'∙b ste-stop) in 
            Eq.subst 
              (λ a → `app (`fun _) d ⇩ `app (`fun _) e ↝ a) 
              (identityˡ c') 
              step
            ; c' c'≡a'∙b (ste-app-seq₂ {a = a} {b = c} ste-fun e⇩e') → 
          let step = ste-app-seq₂ ste-fun (f c' (Eq.trans c'≡a'∙b (Eq.cong (λ a → b ∙ a) (identityˡ c))) e⇩e') in 
            Eq.subst 
              (λ a → `app (`fun _) d ⇩ `app (`fun _) _ ↝ a) 
              (identityˡ c') 
              step
            ; c' c'≡a'∙b (ste-app-seq₂ {a = a} {b = c} ste-stop e⇩e') → 
          let step = ste-app-seq₂ ste-fun (f c' (Eq.trans c'≡a'∙b (Eq.cong (λ a → b ∙ a) (identityˡ c))) e⇩e') in 
            Eq.subst 
              (λ a → `app (`fun _) d ⇩ `app (`fun _) _ ↝ a) 
              (identityˡ c') 
              step
            ; c' c'≡a'∙b (ste-app {a = a} {b = c} {c = g} ste-fun e₂⇩v v-val e⇩e') → 
          let step = ste-app ste-fun (f (b ∙ c) Eq.refl e₂⇩v) v-val e⇩e' in 
            Eq.subst 
              (λ a → `app (`fun _) d ⇩ _ ↝ a) 
              (Eq.trans (Eq.cong (λ a → a ∙ g) (identityˡ (b ∙ c))) (Eq.trans (assoc b c g) (Eq.trans (Eq.cong (λ a → b ∙ (a ∙ g)) (Eq.sym (identityˡ c))) (Eq.sym c'≡a'∙b)))) 
              step
            ; c' c'≡a'∙b (ste-app {a = a} {b = c} {c = g} ste-stop e₂⇩v v-val e⇩e') → 
          let step = ste-app ste-fun (f (b ∙ c) Eq.refl e₂⇩v) v-val e⇩e' in 
            Eq.subst 
              (λ a → `app (`fun _) d ⇩ _ ↝ a) 
              (Eq.trans (Eq.cong (λ a → a ∙ g) (identityˡ (b ∙ c))) (Eq.trans (assoc b c g) (Eq.trans (Eq.cong (λ a → b ∙ (a ∙ g)) (Eq.sym (identityˡ c))) (Eq.sym c'≡a'∙b)))) 
              step
            ; c' c'≡a'∙b ste-stop → 
          let step = ste-app-seq₂ ste-fun (f c' c'≡a'∙b ste-stop) in 
            Eq.subst 
              (λ a → `app (`fun _) d ⇩ `app (`fun _) e ↝ a) 
              (identityˡ c') 
              step }

mutual 
  ▹-↦*→⇩ : {K : Frame} {k : K ÷ τ} {e : · ⊢ τ} {v : · ⊢ return-type k} {a : Effect} → 
      k ▹ e ↦* ε ◃ v ↝ a  
    ------------------------
    → k ● e ⇩ v ↝ a
  ▹-↦*→⇩ (↦*-step {b = b} ke-zero s) rewrite identityˡ b = ◃-↦*→⇩ s v-zero 
  ▹-↦*→⇩ (↦*-step {b = b} ke-suc₁ s) rewrite identityˡ b = ▹-↦*→⇩ s
  ▹-↦*→⇩ (↦*-step {b = b} ke-case s) rewrite identityˡ b = ▹-↦*→⇩ s
  ▹-↦*→⇩ (↦*-step {b = b} ke-fun s)  rewrite identityˡ b = ◃-↦*→⇩ s v-fun 
  ▹-↦*→⇩ (↦*-step {b = b} ke-app₁ s) rewrite identityˡ b = ▹-↦*→⇩ s
  ▹-↦*→⇩ {k = k} (↦*-step {a = a} {b = b} ke-eff s) 
    = ⟪-● k 
      (λ c' c'≡a∙b' e⇩v → 
        let step = ste-eff e⇩v in 
          Eq.subst (λ a → `eff _ _ ⇩ _ ↝ a) (Eq.sym c'≡a∙b') step) 
      (a ∙ b) Eq.refl (▹-↦*→⇩ s)

  ◃-↦*→⇩ : {K : Frame} {k : K ÷ τ} {e : · ⊢ τ} {v : · ⊢ return-type k} {a : Effect} → 
      k ◃ e ↦* ε ◃ v ↝ a
    → e val
    ------------------------
    → k ● e ⇩ v ↝ a
  ◃-↦*→⇩ {k = ε} ↦*-refl e-val = ste-stop
  ◃-↦*→⇩ {k = k ⨾ F} (↦*-step {b = b} ke-suc₂ s) e-val rewrite identityˡ b = ◃-↦*→⇩ s (v-suc e-val)
  ◃-↦*→⇩ {k = k ⨾ F} (↦*-step {b = b} ke-case-z s) e-val 
    = ⟪-● k 
      (λ b' b'≡b e₁⇩e' → 
        let step = ste-case-z ste-zero e₁⇩e' in 
        Eq.subst (λ a → `case `zero _ _ ⇩ _ ↝ a) (Eq.sym b'≡b) step) 
      (1# ∙ b) Eq.refl (▹-↦*→⇩ s)
  ◃-↦*→⇩ {k = k ⨾ F} (↦*-step {b = b} ke-case-s s) (v-suc v-val)
    = ⟪-● k (λ b' b'≡b e₂⇩e' → 
        let step = ste-case-s (ste-suc ste-stop) v-val e₂⇩e' in 
          Eq.subst (λ a → `case (`suc _) _ _ ⇩ _ ↝ a) (Eq.sym b'≡b) step)
      (1# ∙ b) Eq.refl (▹-↦*→⇩ s)
  ◃-↦*→⇩ {k = k ⨾ F} (↦*-step {b = b} ke-app₂ s) v-fun rewrite identityˡ b = ▹-↦*→⇩ s
  ◃-↦*→⇩ {k = k ⨾ F} (↦*-step {b = b} ke-app₃ s) e-val 
    = ⟪-● k (λ c' c'≡a∙b' e⇩e' → 
        let step = ste-app ste-fun ste-stop e-val e⇩e' in 
          Eq.subst (λ a → `app (`fun _) _ ⇩ _ ↝ a) (Eq.trans (Eq.cong (λ a → a ∙ _) (identityʳ 1#)) (Eq.sym c'≡a∙b')) step) 
      (1# ∙ b) Eq.refl (▹-↦*→⇩ s)

{-
  Convergent Soundness
-}
↦*→⇩-ε : {e v : · ⊢ τ} {a : Effect} → 
    ε ▹ e ↦* ε ◃ v ↝ a
  ------------------------
  → e ⇩ v ↝ a  
↦*→⇩-ε e↦*v = ▹-↦*→⇩ e↦*v

return : (s : State) → Type 
return (k ◃ _) = return-type k
return (k ▹ _) = return-type k

↦-return-≡ : {s s' : State} {a : Effect} → 
    s ↦ s' ↝ a 
  ------------------------
  → return s ≡ return s' 
↦-return-≡ ke-zero   = Eq.refl
↦-return-≡ ke-suc₁   = Eq.refl
↦-return-≡ ke-suc₂   = Eq.refl
↦-return-≡ ke-case   = Eq.refl
↦-return-≡ ke-case-z = Eq.refl
↦-return-≡ ke-case-s = Eq.refl
↦-return-≡ ke-fun    = Eq.refl
↦-return-≡ ke-app₁   = Eq.refl
↦-return-≡ ke-app₂   = Eq.refl
↦-return-≡ ke-eff    = Eq.refl 
↦-return-≡ ke-app₃   = Eq.refl

↦*-return-≡ : {s s' : State} {a : Effect} → 
    s ↦* s' ↝ a 
  -------------------------
  → return s ≡ return s'
↦*-return-≡ ↦*-refl = Eq.refl
↦*-return-≡ (↦*-step step steps) = Eq.trans (↦-return-≡ step) (↦*-return-≡ steps)

k●e⇩k'●e' : (s s' : State) (a : Effect) → return s ≡ return s' → Set ℓ
k●e⇩k'●e' (k ◃ e) (k' ◃ e') a p = e val → k ● e ⇩ Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇩k'●e' (k ▹ e) (k' ◃ e') a p =         k ● e ⇩ Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇩k'●e' (k ▹ e) (k' ▹ e') a p =         k ● e ⇩ Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇩k'●e' (k ◃ e) (k' ▹ e') a p = e val → k ● e ⇩ Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a

↦-k●e⇩ : {s s' : State} {a : Effect} → 
    (transition : s ↦ s' ↝ a)
  ------------------------
  → k●e⇩k'●e' s s' a (↦-return-≡ transition)
↦-k●e⇩ {k ◃ e} {k' ◃ e'} ke-suc₂ e-val   = ste-stop 
↦-k●e⇩ {k ◃ e} {k' ▹ e'} ke-case-z e-val = ⟪-● k' (λ _ a≡b e₁⇩e' → 
  let step = ste-case-z ste-zero e₁⇩e' in 
    Eq.subst (λ a → `case `zero _ _ ⇩ _ ↝ a) (Eq.sym a≡b) step) 
    1# (Eq.sym (identityʳ 1#)) ste-stop
↦-k●e⇩ {k ◃ e} {k' ▹ e'} ke-case-s (v-suc e-val) = ⟪-● k' (λ _ a≡b e₂⇩e' → 
  let step = ste-case-s (ste-suc ste-stop) e-val e₂⇩e' in 
    Eq.subst (λ a → `case (`suc _) _ _ ⇩ _ ↝ a) (Eq.sym a≡b) step) 
    1# (Eq.sym (identityʳ 1#)) ste-stop
↦-k●e⇩ {k ◃ e} {k' ▹ e'} ke-app₂ e-val   = ste-stop
↦-k●e⇩ {k ◃ e} {k' ▹ e'} ke-app₃ e-val   = ⟪-● k' (λ _ c≡b e⇩e' → 
  let step = ste-app ste-fun ste-stop e-val e⇩e' in 
    Eq.subst (λ a → `app (`fun _) _ ⇩ _ ↝ a) (Eq.sym (Eq.trans c≡b (Eq.cong (λ a → a ∙ _) (Eq.sym (identityʳ 1#))))) step) 
    1# (Eq.sym (identityʳ 1#)) ste-stop 
↦-k●e⇩ {k ▹ e} {k' ◃ e'} ke-zero         = ste-stop
↦-k●e⇩ {k ▹ e} {k' ◃ e'} ke-fun          = ste-stop
↦-k●e⇩ {k ▹ e} {k' ▹ e'} ke-suc₁         = ste-stop
↦-k●e⇩ {k ▹ e} {k' ▹ e'} ke-case         = ste-stop
↦-k●e⇩ {k ▹ e} {k' ▹ e'} ke-app₁         = ste-stop
↦-k●e⇩ {k ▹ e} {k' ▹ e'} ke-eff          = ⟪-● k' (λ _ c'≡ab' e⇩e' →
  let step = ste-eff e⇩e' in 
    Eq.subst (λ a → `eff _ _ ⇩ _ ↝ a) (Eq.sym c'≡ab') step)
    _ (Eq.sym (identityʳ _)) ste-stop 

↦*-k●e⇩ : {s s' : State} {a : Effect} → 
    (transition : s ↦* s' ↝ a)
  ------------------------
  → k●e⇩k'●e' s s' a (↦*-return-≡ transition)
↦*-k●e⇩ {k ◃ e} {s'} ↦*-refl _ = ste-stop
↦*-k●e⇩ {k ▹ e} {s'} ↦*-refl   = ste-stop
↦*-k●e⇩ {k ◃ e} {k' ◃ e'} (↦*-step {s' = (k'' ◃ e'')} step steps) e-val with ↦-k●e⇩ step e-val | ↦*-k●e⇩ steps (◃-val (↦*-step step ↦*-refl) e-val)
↦*-k●e⇩ {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ◃ e''} ke-suc₂ steps) e-val   | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ◃ e'} (↦*-step {s' = (k'' ▹ e'')} step steps) e-val with ↦-k●e⇩ step e-val | ↦*-k●e⇩ steps 
↦*-k●e⇩ {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-case-z steps) e-val | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-case-s steps) e-val | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-app₂ steps) e-val   | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-app₃ steps) e-val   | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ▹ e'} (↦*-step {s' = (k'' ◃ e'')} step steps) e-val with ↦-k●e⇩ step e-val | ↦*-k●e⇩ steps (◃-val (↦*-step step ↦*-refl) e-val)
↦*-k●e⇩ {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ◃ e''} ke-suc₂ steps) e-val   | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ▹ e'} (↦*-step {s' = (k'' ▹ e'')} step steps) e-val with ↦-k●e⇩ step e-val | ↦*-k●e⇩ steps 
↦*-k●e⇩ {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-case-z steps) e-val | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-case-s steps) e-val | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-app₂ steps) e-val   | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-app₃ steps) e-val   | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ◃ e'} (↦*-step {s' = (k'' ◃ e'')} step steps) with ↦-k●e⇩ step | ↦*-k●e⇩ steps (▹-val (↦*-step step ↦*-refl))
↦*-k●e⇩ {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ◃ e''} ke-zero steps) | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ◃ e''} ke-fun steps)  | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ◃ e'} (↦*-step {s' = (k'' ▹ e'')} step steps) with ↦-k●e⇩ step | ↦*-k●e⇩ steps
↦*-k●e⇩ {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-suc₁ steps) | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-case steps) | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-app₁ steps) | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-eff steps)  | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ▹ e'} (↦*-step {s' = (k'' ◃ e'')} step steps) with ↦-k●e⇩ step | ↦*-k●e⇩ steps (▹-val (↦*-step step ↦*-refl))
↦*-k●e⇩ {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ◃ e''} ke-zero steps) | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ◃ e''} ke-fun steps)  | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ▹ e'} (↦*-step {s' = (k'' ▹ e'')} step steps) with ↦-k●e⇩ step | ↦*-k●e⇩ steps
↦*-k●e⇩ {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-suc₁ steps) | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-case steps) | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-app₁ steps) | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
↦*-k●e⇩ {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-eff steps)  | step⇩ | steps⇩ = ⇩-trans step⇩ steps⇩
 
{-
  Divergent Soundness
-}
↦*→⇩s-ε : {e : · ⊢ τ} {a : Effect} {s : State} →
    ε ▹ e ↦* s ↝ a
  ------------------------
  → Σ[ e' ∈ · ⊢ τ ] (e ⇩ e' ↝ a)
↦*→⇩s-ε {s = k' ◃ e'} d = _ , ↦*-k●e⇩ d
↦*→⇩s-ε {s = k' ▹ e'} d = _ , ↦*-k●e⇩ d
  
{-
  Convergent Equivalence
-}
↦*⇔⇩ : {e v : · ⊢ τ} {a : Effect} → 
    ε ▹ e ↦* ε ◃ v ↝ a
  ------------------------
  ⇔ 
  ------------------------
    (v val) × (e ⇩ v ↝ a)
↦*⇔⇩ = (λ e↦*v → ▹-val e↦*v , ↦*→⇩-ε e↦*v) , λ (v-val , e⇩v) → ⇩→↦*-ε e⇩v v-val
