open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module SoundnessCompleteness.SmallStepBigStep {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

open import Language.SmallStep monoid
open import Language.BigStep monoid 

open MonoidArithmetic monoid

private
  variable
    τ : Type

↦*→⇓ : {e v : · ⊢ τ} {a : Effect} → 
    v val 
  → e ↦* v ↝ a 
  ------------------------
  → e ⇓ v ↝ a
↦*→⇓ v-val ↦*-refl                  = v⇓v v-val
↦*→⇓ v-val (↦*-step e↦e'↝a e'↦*v↝b) = ↦→⇓ e↦e'↝a (↦*→⇓ v-val e'↦*v↝b)
  where 
    ↦→⇓ : {e e' v : · ⊢ τ} {a b : Effect} → 
        e ↦ e' ↝ a 
      → e' ⇓ v ↝ b 
      ------------------------
      → e ⇓ v ↝ a ∙ b 
    ↦→⇓ (se-suc e↦e'↝a) (be-suc e'⇓v↝b)                 
      = be-suc (↦→⇓ e↦e'↝a e'⇓v↝b)
    ↦→⇓ {a = a} (se-case e↦e'↝a) (be-case-z {a = c} {b = d} e'⇓z↝c e'⇓v↝d) 
      rewrite arithmetic₁ a c d 
      = be-case-z (↦→⇓ e↦e'↝a e'⇓z↝c) e'⇓v↝d 
    ↦→⇓ {a = a} (se-case e↦e'↝a) (be-case-s {a = c} {b = d} e'⇓s↝c e'⇓v↝d) 
      rewrite arithmetic₁ a c d 
      = be-case-s (↦→⇓ e↦e'↝a e'⇓s↝c) e'⇓v↝d
    ↦→⇓ se-case-z e'⇓v↝b 
      = be-case-z (be-zero) e'⇓v↝b
    ↦→⇓ (se-case-s {v = v} v-val) e'⇓v↝b 
      = be-case-s (v⇓v (v-suc v-val)) e'⇓v↝b 
    ↦→⇓ {a = a} (se-app e↦e'↝a) (be-app {a = b} {b = c} {c = d} e'⇓v↝b e'⇓v↝c e'⇓v↝d) 
      rewrite arithmetic₂ a b c d 
      = be-app (↦→⇓ e↦e'↝a e'⇓v↝b) e'⇓v↝c e'⇓v↝d 
    ↦→⇓ {a = a} (se-app₁ e↦e'↝a) (be-app {b = c} {c = d} (be-fun) e'⇓v↝c e'⇓v↝d) 
      rewrite arithmetic₃ a c d
      = be-app be-fun (↦→⇓ e↦e'↝a e'⇓v↝c) e'⇓v↝d 
    ↦→⇓ {b = b} (se-app₂ v-val) e'⇓v↝b 
      rewrite arithmetic₄ b 
      = be-app be-fun (v⇓v v-val) e'⇓v↝b
    ↦→⇓ se-eff e'⇓v↝b 
      = be-eff e'⇓v↝b
      
⇓→↦* : {e v : · ⊢ τ} {a : Effect} → 
    e ⇓ v ↝ a 
  ------------------------
  → e ↦* v ↝ a
⇓→↦* be-zero = ↦*-refl
⇓→↦* (be-suc e⇓v↝a) = compatible {p = `suc} se-suc (⇓→↦* e⇓v↝a)
⇓→↦* (be-case-z e⇓v↝a e⇓v↝b) = 
  let step₁ = compatible se-case (⇓→↦* e⇓v↝a) in 
  let step₂ = ↦*-step se-case-z (⇓→↦* e⇓v↝b) in 
  let step₂' = Eq.subst (λ e → `case `zero _ _ ↦* _ ↝ e) (identityˡ _) step₂ in 
    ↦*-trans step₁ step₂'
⇓→↦* (be-case-s e⇓v↝a e⇓v↝b) with ⇓-val e⇓v↝a  
... | v-suc v-val =
  let step₁ = compatible se-case (⇓→↦* e⇓v↝a) in 
  let step₂ = ↦*-step (se-case-s v-val) (⇓→↦* e⇓v↝b) in 
  let step₂' = Eq.subst (λ c → `case (`suc _) _ _ ↦* _ ↝ c) (identityˡ _) step₂ in
  ↦*-trans step₁ step₂'
⇓→↦* be-fun = ↦*-refl
⇓→↦* (be-app e⇓v↝a e⇓v↝b e⇓v↝c) = 
  let step₁ = compatible se-app (⇓→↦* e⇓v↝a) in 
  let step₂ = compatible se-app₁ (⇓→↦* e⇓v↝b) in 
  let step₃ = ↦*-step (se-app₂ (⇓-val e⇓v↝b)) (⇓→↦* e⇓v↝c) in 
  let step₃' = Eq.subst (λ c → `app (`fun _) _ ↦* _ ↝ c) (identityˡ _) step₃ in
  ↦*-trans 
    (↦*-trans step₁ step₂) step₃'
⇓→↦* (be-eff e⇓v↝a) = ↦*-step se-eff (⇓→↦* e⇓v↝a)

↦*⇔⇓ : {e v : · ⊢ τ} {a : Effect} → 
    (v val) × (e ↦* v ↝ a) 
  ------------------------
  ⇔ 
  ------------------------
    e ⇓ v ↝ a
↦*⇔⇓ = (λ (v-val , e↦*v↝a) → ↦*→⇓ v-val e↦*v↝a) , λ e⇓v↝a → ⇓-val e⇓v↝a , ⇓→↦* e⇓v↝a 
