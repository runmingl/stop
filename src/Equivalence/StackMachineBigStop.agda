open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

module Equivalence.StackMachineBigStop {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

open import Language.StackMachine monoid
open import Language.BigStop monoid 

open MonoidArithmetic monoid

open import Equivalence.SmallStepBigStop monoid using (⇩-trans)

private
  variable
    τ : Type

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
  Eq.subst (λ a → k ▹ `suc _ ↦* k ◃ `suc _ ↝ a) (arithmetic₉ a) step
⇩→↦* ste-fun v-val k = k▹v↦*k◃v v-fun
⇩→↦* (ste-app {a = a} {b = b} {c = c} e⇩f e₂⇩v₂ v₂-val e⇩v₁) v-val k rewrite arithmetic₈ a b c = 
  let step₁ = ↦*-step ke-app₁ (⇩→↦* e⇩f v-fun (k ⨾ _)) in 
  let step₂ = ↦*-step ke-app₂ (⇩→↦* e₂⇩v₂ v₂-val (k ⨾ _)) in
  let step₃ = ↦*-step ke-app₃ (⇩→↦* e⇩v₁ v-val k) in
    ↦*-trans step₁ (↦*-trans step₂ step₃)
⇩→↦* (ste-case-z {a = a} {b = b} e⇩z e⇩v) v-val k rewrite arithmetic₇ a b =
  let step₁ = ↦*-step ke-case (⇩→↦* e⇩z v-zero (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-z (⇩→↦* e⇩v v-val k) in
    ↦*-trans step₁ step₂
⇩→↦* (ste-case-s {a = a} {b = b} e⇩s v₁-val e⇩v) v-val k rewrite arithmetic₇ a b = 
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
... | s , k'▹e↦*s rewrite arithmetic₇ a b =   
  let step₁ = ↦*-step ke-app₁ (⇩→↦* e⇩f v-fun (k ⨾ app⟨-⟩ _)) in 
  let step₂ = ↦*-step ke-app₂ k'▹e↦*s in 
    s , ↦*-trans step₁ step₂
⇩→↦*s (ste-app {a = a} {b = b} {c = c} e⇩f e₂⇩v₂ v₂-val e⇩v₁) k with ⇩→↦*s e⇩v₁ k 
... | s , k'▹e↦*s rewrite arithmetic₈ a b c = 
  let step₁ = ↦*-step ke-app₁ (⇩→↦* e⇩f v-fun (k ⨾ app⟨-⟩ _)) in 
  let step₂ = ↦*-step ke-app₂ (⇩→↦* e₂⇩v₂ v₂-val (k ⨾ _)) in
  let step₃ = ↦*-step ke-app₃ k'▹e↦*s in
    s , ↦*-trans step₁ (↦*-trans step₂ step₃)
⇩→↦*s (ste-case-seq {a = a} e⇩e') k with ⇩→↦*s e⇩e' (k ⨾ case⟨-⟩ _ _)
... | s , k'▹e↦*s = s , Eq.subst (λ a → k ▹ `case _ _ _ ↦* s ↝ a) (identityˡ a) (↦*-step ke-case k'▹e↦*s)
⇩→↦*s (ste-case-z {a = a} {b = b} e⇩z e⇩e') k with ⇩→↦*s e⇩e' k
... | s , k▹e↦*s rewrite arithmetic₇ a b = 
  let step₁ = ↦*-step ke-case (⇩→↦* e⇩z v-zero (k ⨾ _)) in 
  let step₂ = ↦*-step ke-case-z k▹e↦*s in
    s , ↦*-trans step₁ step₂
⇩→↦*s (ste-case-s {a = a} {b = b} e⇩s v₁-val e⇩e') k with ⇩→↦*s e⇩e' k
... | s , k▹e↦*s rewrite arithmetic₇ a b = 
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

k●e⇩k'●e' : (s s' : State) (a : Effect) → return s ≡ return s' → Set ℓ
k●e⇩k'●e' (k ◃ e) (k' ◃ e') a p = e val → k ● e ⇩ Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇩k'●e' (k ▹ e) (k' ◃ e') a p =         k ● e ⇩ Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇩k'●e' (k ▹ e) (k' ▹ e') a p =         k ● e ⇩ Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇩k'●e' (k ◃ e) (k' ▹ e') a p = e val → k ● e ⇩ Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a

congruence :  {K : Frame} → (k : K ÷ τ) → {a : Effect} {e e' : · ⊢ τ} → 
    e ⇩ e' ↝ a
  ------------------------
  → (k ● e ⇩ k ● e' ↝ a)
congruence ε e⇩e' = e⇩e'
congruence (k ⨾ suc⟨-⟩) e⇩e'         = congruence k (ste-suc e⇩e')
congruence (k ⨾ case⟨-⟩ _ _) e⇩e'    = congruence k (ste-case-seq e⇩e')
congruence (k ⨾ app⟨-⟩ _) e⇩e'       = congruence k (ste-app-seq₁ e⇩e')
congruence (k ⨾ app⟨fun _ ⟩⟨-⟩) e⇩e' = Eq.subst (λ a → k ● `app (`fun _) _ ⇩ k ● `app (`fun _) _ ↝ a) (identityˡ _) (congruence k (ste-app-seq₂ ste-fun e⇩e'))

↦-k●e⇩ : {s s' : State} {a : Effect} → 
    (transition : s ↦ s' ↝ a)
  ------------------------
  → k●e⇩k'●e' s s' a (↦-return-≡ transition)
↦-k●e⇩ {k ◃ e} {k' ◃ e'} ke-suc₂ _ = ste-stop 
↦-k●e⇩ {k ◃ e} {k' ▹ e'} ke-case-z e-val rewrite arithmetic₁₄ 
  = congruence k' (ste-case-z ste-zero ste-stop)
↦-k●e⇩ {k ◃ e} {k' ▹ e'} ke-case-s (v-suc e-val) rewrite arithmetic₁₄ 
  = congruence k' (ste-case-s ste-stop e-val ste-stop)
↦-k●e⇩ {k ◃ e} {k' ▹ e'} ke-app₂ _ = ste-stop
↦-k●e⇩ {k ◃ e} {k' ▹ e'} ke-app₃ e-val rewrite arithmetic₁₅ 
  = congruence k' (ste-app ste-fun ste-stop e-val ste-stop)
↦-k●e⇩ {k ▹ e} {k' ◃ e'} ke-zero   = ste-stop
↦-k●e⇩ {k ▹ e} {k' ◃ e'} ke-fun    = ste-stop
↦-k●e⇩ {k ▹ e} {k' ▹ e'} ke-suc₁   = ste-stop
↦-k●e⇩ {k ▹ e} {k' ▹ e'} ke-case   = ste-stop
↦-k●e⇩ {k ▹ e} {k' ▹ e'} ke-app₁   = ste-stop
↦-k●e⇩ {k ▹ e} {k' ▹ e'} ke-eff 
  = Eq.subst (λ a → k ● `eff _ e' ⇩ k ● e' ↝ a) (identityʳ _) 
    (congruence k (ste-eff ste-stop))

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
  Convergent Soundness
-}
↦*→⇩-ε : {e v : · ⊢ τ} {a : Effect} → 
    ε ▹ e ↦* ε ◃ v ↝ a
  ------------------------
  → e ⇩ v ↝ a  
↦*→⇩-ε {τ} {e} {v} {a} d = term 
  where 
    -- a hack to get rid of the annoying transport
    eq : v ≡ Eq.subst (_⊢_ ·) (Eq.sym (↦*-return-≡ d)) v
    eq rewrite uip (Eq.sym (↦*-return-≡ d)) Eq.refl = Eq.refl

    term : e ⇩ v ↝ a  
    term rewrite eq = ↦*-k●e⇩ d

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
