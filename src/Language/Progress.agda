open import Prelude 

open import Level 
open import Data.Unit 
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

{-
  Progress Theorem using Big-Stop Semantics
-}
module Language.Progress {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

open import Language.BigStop monoid 
open import Language.SmallStep monoid

open MonoidArithmetic monoid

open import SoundnessCompleteness.SmallStepBigStop monoid

private
  variable
    τ : Type

{-
  The notion of a "progressing" big-stop derivation is that it is not always stopping.
-}
progressing : {e e' : · ⊢ τ} {a : Effect} → e ⇩ e' ↝ a → Set
progressing ste-zero             = ⊥
progressing (ste-suc d)          = progressing d
progressing ste-fun              = ⊥
progressing (ste-app-seq₁ d)     = progressing d
progressing (ste-app-seq₂ d₁ d₂) = progressing d₁ ⊎ progressing d₂
progressing (ste-app _ _ _ _)    = ⊤
progressing (ste-case-seq d)     = progressing d
progressing (ste-case-z _ _)     = ⊤
progressing (ste-case-s _ _ _)   = ⊤
progressing (ste-eff _)          = ⊤
progressing ste-stop             = ⊥

infix 2 _↧_↝_
_↧_↝_ : (e e' : · ⊢ τ) (a : Effect) → Set ℓ
_↧_↝_ e e' a = Σ[ d ∈ e ⇩ e' ↝ a ] progressing d

{-
  Progress Theorem: A well-typed closed term is either a value or can take step(s).
-}
progress : 
    (e : · ⊢ τ)
  ------------------------
  → e val ⊎ ∃[ e' ] ∃[ a ] (e ↧ e' ↝ a)
progress `zero = inj₁ v-zero
progress (`suc e) with progress e 
... | inj₁ e-val            = inj₁ (v-suc e-val)
... | inj₂ (e' , a , d , p) = inj₂ (`suc e' , a , ste-suc d , p)
progress (`case e e₁ e₂) with progress e 
... | inj₁ v-zero           = inj₂ (e₁ , 1# ∙ 1# , ste-case-z ste-zero ste-stop , tt)
... | inj₁ (v-suc e-val)    = inj₂ ((e₂ [ _ ]) , 1# ∙ 1# , ste-case-s ste-stop e-val ste-stop , tt)
... | inj₂ (e' , a , d , p) = inj₂ (`case e' e₁ e₂ , a , ste-case-seq d , p)
progress (`fun e) = inj₁ v-fun
progress (`app e₁ e₂) with progress e₁ 
... | inj₁ (v-fun {e = e}) with progress e₂ 
... | inj₁ e₂-val              = inj₂ ((e [ `fun e ][ e₂ ]) , 1# ∙ 1# ∙ 1# , ste-app ste-fun ste-stop e₂-val ste-stop , tt)
... | inj₂ (e₂' , a , d , p)   = inj₂ (`app (`fun e) e₂' , 1# ∙ a , ste-app-seq₂ ste-stop d , inj₂ p)
progress (`app e₁ e₂) | inj₂ (e₁' , a , d , p) = inj₂ (`app e₁' e₂ , a , ste-app-seq₁ d , p)
progress (`eff a e) = inj₂ (e , a ∙ 1# , ste-eff ste-stop , tt)

{-
  Progressing big-stop derivation is a right notion for proving progress theorem because 
  it can always take at least one step in small-step semantics. 
-}
progressing-progress : {e₁ e₂ : · ⊢ τ} {a : Effect} → 
    e₁ ↧ e₂ ↝ a
  ------------------------
  → ∃[ e₃ ] ∃[ b ] ∃[ c ] (e₁ ↦ e₃ ↝ b) × (e₃ ↦* e₂ ↝ c) × (a ≡ b ∙ c)
progressing-progress ((ste-suc d) , p) with progressing-progress (d , p)
... | e₃ , b , c , step₁ , step₂ , p    = `suc e₃ , b , c , se-suc step₁ , compatible se-suc step₂ , p
progressing-progress ((ste-app-seq₁ d) , p) with progressing-progress (d , p)
... | e₃ , b , c , step₁ , step₂ , p    = `app e₃ _ , b , c , se-app step₁ , compatible se-app step₂ , p
progressing-progress ((ste-app-seq₂ d d₁) , (inj₁ p)) with progressing-progress (d , p)
... | e₃ , b , c , step₁ , step₂ , p    = 
    `app e₃ _ , _ , _ , 
      se-app step₁ , 
      ↦*-trans (compatible se-app step₂) (compatible se-app₁ (⇩→↦* d₁)) , 
        Eq.trans (Eq.cong (λ a → a ∙ _) p) (assoc _ _ _)
progressing-progress ((ste-app-seq₂ d d₁) , (inj₂ p)) with progressing-progress (d₁ , p) with ⇩→↦* d
... | e₃ , b , c , step₁ , step₂ , p | ↦*-refl            = 
    `app (`fun _) _ , _ , _ , 
      se-app₁ step₁ , 
      compatible se-app₁ step₂ , 
        Eq.trans (identityˡ _) p
... | e₃ , b , c , step₁ , step₂ , p | ↦*-step step steps = 
    `app _ _ , _ , _ , 
      se-app step , 
      ↦*-trans (compatible se-app steps) (compatible se-app₁ (⇩→↦* d₁)) , 
        assoc _ _ _
progressing-progress ((ste-app d d₁ v-val d₂) , tt) with ⇩→↦* d | ⇩→↦* d₁ 
... | ↦*-refl            | ↦*-refl             = _ , _ , _ , se-app₂ v-val , ⇩→↦* d₂ , Eq.sym (arithmetic₄ _)
... | ↦*-refl            | ↦*-step step steps  =                
    `app (`fun _) _ , _ , _ , 
      se-app₁ step , 
      ↦*-trans (compatible se-app₁ steps) (↦*-step (se-app₂ v-val) (⇩→↦* d₂)) , 
        arithmetic₁₀ _ _ _ 
... | ↦*-step step steps | _                   = 
    `app _ _ , _ , _ , 
      se-app step , 
      ↦*-trans (compatible se-app steps) (↦*-trans (compatible se-app₁ (⇩→↦* d₁)) (↦*-step (se-app₂ v-val) (⇩→↦* d₂))) , arithmetic₁₁ _ _ _ _
progressing-progress ((ste-case-seq d) , p) with progressing-progress (d , p)
... | e₃ , b , c , step₁ , step₂ , p    = `case _ _ _ , _ , _ , se-case step₁ , compatible se-case step₂ , p
progressing-progress ((ste-case-z {e₁ = e₁} d d₁) , tt) with ⇩→↦* d  
... | ↦*-refl            = e₁ , _ , _ , se-case-z , ⇩→↦* d₁ , Eq.refl
... | ↦*-step step steps = 
    `case _ _ _ , _ , _ , 
      se-case step , 
      ↦*-trans (compatible se-case steps) (↦*-step se-case-z (⇩→↦* d₁)) , arithmetic₁₂ _ _ _
progressing-progress ((ste-case-s {e₂ = e₂} d v-val d₁) , tt) with ⇩→↦* d 
... | ↦*-refl            = e₂ [ _ ] , _ , _ , se-case-s v-val , ⇩→↦* d₁ , Eq.refl
... | ↦*-step step steps = 
    `case _ _ _ , _ , _ , 
      se-case step , 
      ↦*-trans (compatible se-case steps) (↦*-step (se-case-s v-val) (⇩→↦* d₁)) , arithmetic₁₂ _ _ _
progressing-progress ((ste-eff {e = e} d) , tt) = e , _ , _ , se-eff , ⇩→↦* d , Eq.refl
