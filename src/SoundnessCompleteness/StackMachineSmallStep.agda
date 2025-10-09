open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

module SoundnessCompleteness.StackMachineSmallStep {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

open import Language.StackMachine monoid
open import Language.SmallStep monoid renaming(_↦*_↝_ to _⇒*_↝_; _↦_↝_ to _⇒_↝_; ↦*-trans to ⇒*-trans; compatible to sscompatible)

open MonoidArithmetic monoid

private
  variable
    τ τ' : Type

congruence :  {K : Frame} → (k : K ÷ τ) → {a : Effect} {e e' : · ⊢ τ} → 
    e ⇒ e' ↝ a
  ------------------------
  → (k ● e ⇒ k ● e' ↝ a)
congruence ε step = step
congruence (k ⨾ suc⟨-⟩) step = congruence k (se-suc step)
congruence (k ⨾ case⟨-⟩ _ _) step = congruence k (se-case step)
congruence (k ⨾ app⟨-⟩ _) step = congruence k (se-app step)
congruence (k ⨾ app⟨fun _ ⟩⟨-⟩) step = congruence k (se-app₁ step)

congruence* :  {K : Frame} → (k : K ÷ τ) → {a : Effect} {e e' : · ⊢ τ} → 
    e ⇒* e' ↝ a
  ------------------------
  → (k ● e ⇒* k ● e' ↝ a)
congruence* k ↦*-refl = ↦*-refl
congruence* k (↦*-step e⇒e' e'⇒*e'') = ↦*-step (congruence k e⇒e') (congruence* k e'⇒*e'')

k●e⇒*k'●e' : (s s' : State) (a : Effect) → return s ≡ return s' → Set ℓ
k●e⇒*k'●e' (k ◃ e) (k' ◃ e') a p = e val → k ● e ⇒* Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇒*k'●e' (k ▹ e) (k' ◃ e') a p =         k ● e ⇒* Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇒*k'●e' (k ▹ e) (k' ▹ e') a p =         k ● e ⇒* Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a 
k●e⇒*k'●e' (k ◃ e) (k' ▹ e') a p = e val → k ● e ⇒* Eq.subst (· ⊢_) (Eq.sym p) (k' ● e') ↝ a

↦-k●e⇒* : {s s' : State} {a : Effect} → 
    (transition : s ↦ s' ↝ a)
  ------------------------
  → k●e⇒*k'●e' s s' a (↦-return-≡ transition)
↦-k●e⇒* {s} {s'} ke-zero   = ↦*-refl
↦-k●e⇒* {s} {s'} ke-suc₁   = ↦*-refl
↦-k●e⇒* {s} {s'} ke-suc₂ _ = ↦*-refl
↦-k●e⇒* {s} {s'} ke-case   = ↦*-refl
↦-k●e⇒* {s} {s'} (ke-case-z {k = k}) _
  = congruence* k 
      (Eq.subst (λ a → `case `zero _ _ ⇒* _ ↝ a) (identityˡ 1#) 
      (↦*-step se-case-z ↦*-refl))
↦-k●e⇒* {s} {s'} (ke-case-s {k = k} {e₁ = e₁} {e₂ = e₂} {v = v}) (v-suc v-val) 
  = congruence* k 
      (Eq.subst (λ a → `case (`suc v) e₁ e₂ ⇒* e₂ [ v ] ↝ a) (identityʳ 1#) 
      (↦*-step (se-case-s v-val) ↦*-refl))
↦-k●e⇒* {s} {s'} ke-fun    = ↦*-refl
↦-k●e⇒* {s} {s'} ke-app₁   = ↦*-refl
↦-k●e⇒* {s} {s'} ke-app₂ _ = ↦*-refl
↦-k●e⇒* {s} {s'} (ke-app₃ {k = k} {e = e} {v = v}) v-val 
  = congruence* k 
    (Eq.subst (λ a → `app (`fun e) v ⇒* e [ `fun e ][ v ] ↝ a) (identityʳ 1#) 
    (↦*-step (se-app₂ v-val) ↦*-refl))
↦-k●e⇒* {s} {s'} (ke-eff {k = k}) 
  = congruence* k 
    (Eq.subst (λ a → `eff _ _ ⇒* _ ↝ a) (identityʳ _) 
    (↦*-step se-eff ↦*-refl))

↦*-k●e⇒* : {s s' : State} {a : Effect} → 
    (transition : s ↦* s' ↝ a)
  ------------------------
  → k●e⇒*k'●e' s s' a (↦*-return-≡ transition)
↦*-k●e⇒* {k ◃ e} {s'} ↦*-refl _ = ↦*-refl
↦*-k●e⇒* {k ▹ e} {s'} ↦*-refl   = ↦*-refl
↦*-k●e⇒* {k ◃ e} {k' ◃ e'} (↦*-step {s' = (k'' ◃ e'')} step steps) e-val with ↦-k●e⇒* step e-val | ↦*-k●e⇒* steps (◃-val (↦*-step step ↦*-refl) e-val)
↦*-k●e⇒* {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ◃ e''} ke-suc₂ steps) e-val   | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ◃ e'} (↦*-step {s' = (k'' ▹ e'')} step steps) e-val with ↦-k●e⇒* step e-val | ↦*-k●e⇒* steps 
↦*-k●e⇒* {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-case-z steps) e-val | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-case-s steps) e-val | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-app₂ steps) e-val   | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-app₃ steps) e-val   | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ▹ e'} (↦*-step {s' = (k'' ◃ e'')} step steps) e-val with ↦-k●e⇒* step e-val | ↦*-k●e⇒* steps (◃-val (↦*-step step ↦*-refl) e-val)
↦*-k●e⇒* {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ◃ e''} ke-suc₂ steps) e-val   | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ▹ e'} (↦*-step {s' = (k'' ▹ e'')} step steps) e-val with ↦-k●e⇒* step e-val | ↦*-k●e⇒* steps 
↦*-k●e⇒* {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-case-z steps) e-val | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-case-s steps) e-val | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-app₂ steps) e-val   | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ◃ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-app₃ steps) e-val   | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ◃ e'} (↦*-step {s' = (k'' ◃ e'')} step steps) with ↦-k●e⇒* step | ↦*-k●e⇒* steps (▹-val (↦*-step step ↦*-refl))
↦*-k●e⇒* {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ◃ e''} ke-zero steps) | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ◃ e''} ke-fun steps)  | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ◃ e'} (↦*-step {s' = (k'' ▹ e'')} step steps) with ↦-k●e⇒* step | ↦*-k●e⇒* steps
↦*-k●e⇒* {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-suc₁ steps) | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-case steps) | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-app₁ steps) | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ◃ e'} (↦*-step {_} {k'' ▹ e''} ke-eff steps)  | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ▹ e'} (↦*-step {s' = (k'' ◃ e'')} step steps) with ↦-k●e⇒* step | ↦*-k●e⇒* steps (▹-val (↦*-step step ↦*-refl))
↦*-k●e⇒* {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ◃ e''} ke-zero steps) | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ◃ e''} ke-fun steps)  | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ▹ e'} (↦*-step {s' = (k'' ▹ e'')} step steps) with ↦-k●e⇒* step | ↦*-k●e⇒* steps
↦*-k●e⇒* {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-suc₁ steps) | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-case steps) | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-app₁ steps) | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
↦*-k●e⇒* {k ▹ e} {k' ▹ e'} (↦*-step {_} {k'' ▹ e''} ke-eff steps)  | step⇒* | steps⇒* = ⇒*-trans step⇒* steps⇒*
 
{-
  Convergent Soundness
-}
↦*→⇒*-ε : {e v : · ⊢ τ} {a : Effect} → 
    ε ▹ e ↦* ε ◃ v ↝ a
  ------------------------
  → e ⇒* v ↝ a  
↦*→⇒*-ε {τ} {e} {v} {a} d = term
  where 
    -- a hack to get rid of the annoying transport
    eq : v ≡ Eq.subst (_⊢_ ·) (Eq.sym (↦*-return-≡ d)) v
    eq rewrite uip (Eq.sym (↦*-return-≡ d)) Eq.refl = Eq.refl
 
    term : e ⇒* v ↝ a  
    term rewrite eq = ↦*-k●e⇒* d

{-
  Divergent Soundness
-}
↦*→⇒*s-ε : {e : · ⊢ τ} {a : Effect} {s : State} →
    ε ▹ e ↦* s ↝ a
  ------------------------
  → Σ[ e' ∈ · ⊢ τ ] (e ⇒* e' ↝ a)
↦*→⇒*s-ε {s = k' ◃ e'} d = _ , ↦*-k●e⇒* d
↦*→⇒*s-ε {s = k' ▹ e'} d = _ , ↦*-k●e⇒* d


open import SoundnessCompleteness.SmallStepBigStep monoid 
open import SoundnessCompleteness.StackMachineBigStep monoid

{-
  Convergent Completeness
-}

⇒*→↦*-ε : {e v : · ⊢ τ} {a : Effect} → 
    v val 
  → e ⇒* v ↝ a
  ------------------------
  → ε ▹ e ↦* ε ◃ v ↝ a
⇒*→↦*-ε v-val e⇒*v = ⇓→↦*-ε (↦*→⇓ v-val e⇒*v)

