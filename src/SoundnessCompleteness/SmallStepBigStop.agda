open import Prelude 

open import Level 
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module SoundnessCompleteness.SmallStepBigStop {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

open import Language.SmallStep monoid
open import Language.BigStop monoid 

open MonoidArithmetic monoid

private
  variable
    τ : Type

↦*→⇩ : {e e' : · ⊢ τ} {a : Effect} → 
    e ↦* e' ↝ a 
  ------------------------
  → e ⇩ e' ↝ a
↦*→⇩ ↦*-refl                     = ste-stop 
↦*→⇩ (↦*-step e↦e''↝a e''↦*e'↝b) = ↦→⇩ e↦e''↝a (↦*→⇩ e''↦*e'↝b)
  where
    ↦→⇩ : {e e' e'' : · ⊢ τ} {a b : Effect} → 
        e ↦ e' ↝ a 
      → e' ⇩ e'' ↝ b 
      ------------------------
      → e ⇩ e'' ↝ a ∙ b 
    ↦→⇩ (se-suc e↦e') (ste-suc e'⇩e'') 
      = ste-suc (↦→⇩ e↦e' e'⇩e'')
    ↦→⇩ (se-suc e↦e') ste-stop         
      = ste-suc (↦→⇩ e↦e' ste-stop)
    ↦→⇩ (se-case e↦e') (ste-case-seq e'⇩e'') 
      = ste-case-seq (↦→⇩ e↦e' e'⇩e'')
    ↦→⇩ (se-case {a = a} e↦e') (ste-case-z {a = b} {b = c} e'⇩z e₁⇩e'') rewrite arithmetic₁ a b c 
      = ste-case-z (↦→⇩ e↦e' e'⇩z) e₁⇩e''
    ↦→⇩ (se-case {a = a} e↦e') (ste-case-s {a = b} {b = c} e'⇩s v-val e₂⇩e'') rewrite arithmetic₁ a b c
      = ste-case-s (↦→⇩ e↦e' e'⇩s) v-val e₂⇩e''
    ↦→⇩ (se-case e↦e') ste-stop 
      = ste-case-seq (↦→⇩ e↦e' ste-stop)
    ↦→⇩ se-case-z e'⇩e'' 
      = ste-case-z ste-zero e'⇩e''
    ↦→⇩ (se-case-s v-val) e'⇩e'' 
      = ste-case-s (ste-suc ste-stop) v-val e'⇩e''
    ↦→⇩ (se-app e↦e') (ste-app-seq₁ e'⇩e'') 
      = ste-app-seq₁ (↦→⇩ e↦e' e'⇩e'')
    ↦→⇩ {a = a} (se-app e↦e') (ste-app-seq₂ {a = b} {b = c} e'⇩e'' e'⇩e''') rewrite arithmetic₁ a b c 
      = ste-app-seq₂ (↦→⇩ e↦e' e'⇩e'') e'⇩e'''
    ↦→⇩ {a = a} (se-app e↦e') (ste-app {a = b} {b = c} {c = d} e'⇩e'' e'⇩e''' v-val e'⇩e'''') rewrite arithmetic₂ a b c d 
      = ste-app (↦→⇩ e↦e' e'⇩e'') e'⇩e''' v-val e'⇩e''''
    ↦→⇩ (se-app e↦e') ste-stop 
      = ste-app-seq₁ (↦→⇩ e↦e' ste-stop)
    ↦→⇩ {a = a} (se-app₁ e↦e') (ste-app-seq₁ ste-fun) rewrite arithmetic₅ a 
      = ste-app-seq₂ ste-fun (↦→⇩ e↦e' ste-stop) 
    ↦→⇩ {a = a} (se-app₁ e↦e') (ste-app-seq₁ ste-stop) rewrite arithmetic₅ a 
      = ste-app-seq₂ ste-fun (↦→⇩ e↦e' ste-stop)
    ↦→⇩ {a = a} (se-app₁ e↦e') (ste-app-seq₂ {b = b} ste-fun e'⇩e'') rewrite arithmetic₆ a b
      = ste-app-seq₂ ste-fun (↦→⇩ e↦e' e'⇩e'') 
    ↦→⇩ {a = a} (se-app₁ e↦e') (ste-app-seq₂ {b = b} ste-stop e'⇩e'') rewrite arithmetic₆ a b 
      = ste-app-seq₂ ste-fun (↦→⇩ e↦e' e'⇩e'') 
    ↦→⇩ {a = a} (se-app₁ e↦e') (ste-app {b = c} {c = d} ste-fun e'⇩e''' v-val e'⇩e'''') rewrite arithmetic₃ a c d 
      = ste-app ste-fun (↦→⇩ e↦e' e'⇩e''') v-val e'⇩e''''
    ↦→⇩ {a = a} (se-app₁ e↦e') (ste-app {b = c} {c = d} ste-stop e'⇩e''' v-val e'⇩e'''') rewrite arithmetic₃ a c d 
      = ste-app ste-fun (↦→⇩ e↦e' e'⇩e''') v-val e'⇩e''''
    ↦→⇩ {a = a} (se-app₁ e↦e') ste-stop rewrite arithmetic₅ a 
      = ste-app-seq₂ ste-fun (↦→⇩ e↦e' ste-stop)
    ↦→⇩ {b = b} (se-app₂ v-val) e'⇩e'' rewrite arithmetic₄ b 
      = ste-app ste-fun ste-stop v-val e'⇩e''
    ↦→⇩ se-eff e'⇩e'' 
      = ste-eff e'⇩e''

⇩→↦* : {e e' : · ⊢ τ} {a : Effect} → 
    e ⇩ e' ↝ a 
  ------------------------
  → e ↦* e' ↝ a
⇩→↦* ste-zero = ↦*-refl
⇩→↦* (ste-suc e⇩e') = compatible se-suc (⇩→↦* e⇩e')
⇩→↦* ste-fun = ↦*-refl
⇩→↦* (ste-app-seq₁ e⇩e') = compatible se-app (⇩→↦* e⇩e')
⇩→↦* (ste-app-seq₂ e⇩f e⇩e') = 
  let step₁ = compatible se-app (⇩→↦* e⇩f) in 
  let step₂ = compatible se-app₁ (⇩→↦* e⇩e') in 
    ↦*-trans step₁ step₂
⇩→↦* (ste-app e⇩f e⇩v v-val e'⇩e'') = 
  let step₁ = compatible se-app (⇩→↦* e⇩f) in 
  let step₂ = compatible se-app₁ (⇩→↦* e⇩v) in 
  let step₃ = ↦*-step (se-app₂ v-val) (⇩→↦* e'⇩e'') in 
  let step₃' = Eq.subst (λ c → `app (`fun _) _ ↦* _ ↝ c) (identityˡ _) step₃ in
    ↦*-trans 
      (↦*-trans step₁ step₂) step₃'
⇩→↦* (ste-case-seq e⇩e') = compatible se-case (⇩→↦* e⇩e')
⇩→↦* (ste-case-z e⇩z e'⇩e'') = 
  let step₁ = compatible se-case (⇩→↦* e⇩z) in  
  let step₂ = ↦*-step se-case-z (⇩→↦* e'⇩e'') in 
  let step₂' = Eq.subst (λ e → `case `zero _ _ ↦* _ ↝ e) (identityˡ _) step₂ in 
  ↦*-trans step₁ step₂'
⇩→↦* (ste-case-s e⇩s v-val e'⇩e'') = 
  let step₁ = compatible se-case (⇩→↦* e⇩s) in 
  let step₂ = ↦*-step (se-case-s v-val) (⇩→↦* e'⇩e'') in 
  let step₂' = Eq.subst (λ c → `case (`suc _) _ _ ↦* _ ↝ c) (identityˡ _) step₂ in
  ↦*-trans step₁ step₂'
⇩→↦* (ste-eff e⇩e') = ↦*-step se-eff (⇩→↦* e⇩e')
⇩→↦* ste-stop = ↦*-refl

↦*⇔⇩ : {e e' : · ⊢ τ} {a : Effect} → 
    e ↦* e' ↝ a
  ------------------------
  ⇔ 
  ------------------------
    e ⇩ e' ↝ a
↦*⇔⇩ = ↦*→⇩ , ⇩→↦*
