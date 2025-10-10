open import Prelude 

open import Level 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

{-
  Big-Stop Semantics
-}
module Language.BigStop {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

open MonoidArithmetic monoid

private
  variable
    τ σ : Type

infix 2 _⇩_↝_
data _⇩_↝_ : · ⊢ τ → · ⊢ τ → Effect → Set ℓ where
  ste-zero : 

    ------------------------
    `zero ⇩ `zero ↝ 1# 

  ste-suc : {e e' : · ⊢ Nat} {a : Effect} →
      e ⇩ e' ↝ a 
    ------------------------
    → `suc e ⇩ `suc e' ↝ a

  ste-fun : {e : · # τ ⇒ σ # τ ⊢ σ} →
    
    ------------------------
    `fun e ⇩ `fun e ↝ 1#

  ste-app-seq₁ : {e₁ e₁' : · ⊢ τ ⇒ σ} {e₂ : · ⊢ τ} {a : Effect} →
      e₁ ⇩ e₁' ↝ a
    ------------------------
    → `app e₁ e₂ ⇩ `app e₁' e₂ ↝ a 

  ste-app-seq₂ : {e₁ : · ⊢ τ ⇒ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ e₂' : · ⊢ τ} {a b : Effect} →
      e₁ ⇩ `fun e ↝ a
    → e₂ ⇩ e₂' ↝ b
    ------------------------
    → `app e₁ e₂ ⇩ `app (`fun e) e₂' ↝ a ∙ b

  ste-app : {e₁ : · ⊢ τ ⇒ σ} {e : · # τ ⇒ σ # τ ⊢ σ} {e₂ v₂ : · ⊢ τ} {e' : · ⊢ σ} {a b c : Effect} →
      e₁ ⇩ `fun e ↝ a
    → e₂ ⇩ v₂ ↝ b
    → v₂ val
    → e [ (`fun e) ][ v₂ ] ⇩ e' ↝ c
    ------------------------
    → `app e₁ e₂ ⇩ e' ↝ a ∙ b ∙ c  

  ste-case-seq : {e e' : · ⊢ Nat} {e₁ : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a : Effect} →
      e ⇩ e' ↝ a
    ------------------------
    → `case e e₁ e₂ ⇩ `case e' e₁ e₂ ↝ a

  ste-case-z : {e : · ⊢ Nat} {e₁ e₁' : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a b : Effect} →
      e ⇩ `zero ↝ a 
    → e₁ ⇩ e₁' ↝ b
    ------------------------
    → `case e e₁ e₂ ⇩ e₁' ↝ a ∙ b

  ste-case-s : {e v : · ⊢ Nat} {e₁ e₂' : · ⊢ τ} {e₂ : · # Nat ⊢ τ} {a b : Effect} →
      e ⇩ `suc v ↝ a
    → v val 
    → e₂ [ v ] ⇩ e₂' ↝ b
    ------------------------
    → `case e e₁ e₂ ⇩ e₂' ↝ a ∙ b

  ste-eff : {e e' : · ⊢ τ} {a b : Effect} →
      e ⇩ e' ↝ b
    ------------------------
    → `eff a e ⇩ e' ↝ a ∙ b 

  ste-stop : {e : · ⊢ τ} →

    ------------------------
    e ⇩ e ↝ 1#

{-
  Transitivity of big-stop semantics can be easily proved by considering the equivalence between 
  small-step and big-stop semantics. Nevertheless we give a direct proof here, which is not any more difficult. 
-}
⇩-trans : {e e' e'' : · ⊢ τ} {a b : Effect} → 
    e ⇩ e' ↝ a
  → e' ⇩ e'' ↝ b
  ------------------------
  → e ⇩ e'' ↝ a ∙ b
⇩-trans ste-zero ste-zero rewrite identityˡ 1# = ste-stop
⇩-trans ste-zero ste-stop rewrite identityˡ 1# = ste-stop
⇩-trans (ste-suc d₁) (ste-suc d₂) = ste-suc (⇩-trans d₁ d₂)
⇩-trans {a = a} (ste-suc d₁) ste-stop rewrite identityʳ a = ste-suc d₁
⇩-trans ste-fun ste-fun rewrite identityˡ 1# = ste-stop
⇩-trans ste-fun ste-stop rewrite identityˡ 1# = ste-stop
⇩-trans (ste-app-seq₁ d₁) (ste-app-seq₁ d₂) = ste-app-seq₁ (⇩-trans d₁ d₂)
⇩-trans {a = a} (ste-app-seq₁ d₁) (ste-app-seq₂ {a = b} {b = c} d₂ d₃) rewrite arithmetic₁ a b c = ste-app-seq₂ (⇩-trans d₁ d₂) d₃
⇩-trans {a = a} (ste-app-seq₁ d₁) (ste-app {a = b} {b = c} {c = d} d₂ d₃ v-val d₄) rewrite arithmetic₂ a b c d = ste-app (⇩-trans d₁ d₂) d₃ v-val d₄
⇩-trans {a = a} (ste-app-seq₁ d₁) ste-stop rewrite identityʳ a = ste-app-seq₁ d₁
⇩-trans (ste-app-seq₂ {a = a} {b = b} d₁ d₃) (ste-app-seq₁ ste-fun) rewrite arithmetic₁₇ a b = ste-app-seq₂ d₁ d₃
⇩-trans (ste-app-seq₂ {a = a} {b = b} d₁ d₃) (ste-app-seq₁ ste-stop) rewrite arithmetic₁₇ a b = ste-app-seq₂ d₁ d₃
⇩-trans (ste-app-seq₂ {a = a} {b = b} d₁ d₃) (ste-app-seq₂ {b = c} ste-fun d₄) rewrite arithmetic₁₈ a b c = ste-app-seq₂ d₁ (⇩-trans d₃ d₄)
⇩-trans (ste-app-seq₂ {a = a} {b = b} d₁ d₃) (ste-app-seq₂ {b = c} ste-stop d₄) rewrite arithmetic₁₈ a b c = ste-app-seq₂ d₁ (⇩-trans d₃ d₄)
⇩-trans (ste-app-seq₂ {a = a} {b = b} d₁ d₃) (ste-app {b = c} {c = d} ste-fun d₄ v-val d₅) rewrite arithmetic₁₉ a b c d = ste-app d₁ (⇩-trans d₃ d₄) v-val d₅
⇩-trans (ste-app-seq₂ {a = a} {b = b} d₁ d₃) (ste-app {b = c} {c = d} ste-stop d₄ v-val d₅) rewrite arithmetic₁₉ a b c d = ste-app d₁ (⇩-trans d₃ d₄) v-val d₅
⇩-trans (ste-app-seq₂ {a = a} {b = b} d₁ d₃) ste-stop rewrite arithmetic₁₇ a b = ste-app-seq₂ d₁ d₃
⇩-trans {b = d} (ste-app {a = a} {b = b} {c = c} d₁ d₃ v-val d₄) d₂ rewrite arithmetic₁₆ a b c d = ste-app d₁ d₃ v-val (⇩-trans d₄ d₂)
⇩-trans (ste-case-seq d₁) (ste-case-seq d₂) = ste-case-seq (⇩-trans d₁ d₂)
⇩-trans (ste-case-seq {a = a} d₁) (ste-case-z {a = b} {b = c} d₂ d₃) rewrite arithmetic₁ a b c = ste-case-z (⇩-trans d₁ d₂) d₃
⇩-trans (ste-case-seq {a = a} d₁) (ste-case-s {a = b} {b = c} d₂ v-val d₃) rewrite arithmetic₁ a b c = ste-case-s (⇩-trans d₁ d₂) v-val d₃
⇩-trans (ste-case-seq {a = a} d₁) ste-stop rewrite identityʳ a = ste-case-seq d₁
⇩-trans {b = c} (ste-case-z {a = a} {b = b} d₁ d₃) d₂ rewrite Eq.sym (arithmetic₁ a b c) = ste-case-z d₁ (⇩-trans d₃ d₂)
⇩-trans {b = c} (ste-case-s {a = a} {b = b} d₁ v-val d₃) d₂ rewrite Eq.sym (arithmetic₁ a b c) = ste-case-s d₁ v-val (⇩-trans d₃ d₂)
⇩-trans {b = c} (ste-eff {a = a} {b = b} d₁) d₂ rewrite Eq.sym (arithmetic₁ a b c) = ste-eff (⇩-trans d₁ d₂)
⇩-trans {b = b} ste-stop d₂ rewrite identityˡ b = d₂
