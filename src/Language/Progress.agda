open import Prelude 

open import Level 
open import Data.Unit 
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module Language.Progress {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid
open import Language.Substitution monoid

open import Language.BigStop monoid 
open import Language.SmallStep monoid
open import Equivalence.SmallStepBigStop monoid

private
  variable
    τ : Type

progressing : {e e' : · ⊢ τ} {a : Effect} → e ↧ e' ↝ a → Set
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

progress : 
    (e : · ⊢ τ)
  ------------------------
  → e val ⊎ Σ[ e' ∈ · ⊢ τ ] Σ[ a ∈ Effect ] Σ[ d ∈ e ↧ e' ↝ a ] progressing d
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

progressing-progress : {e₁ e₂ : · ⊢ τ} {a : Effect} → 
    (d : e₁ ↧ e₂ ↝ a)
  → progressing d 
  ------------------------
  → Σ[ e₃ ∈ · ⊢ τ ] Σ[ b ∈ Effect ] Σ[ c ∈ Effect ] ((e₁ ↦ e₃ ↝ b) × (e₃ ↦* e₂ ↝ c) × (a ≡ b ∙ c))
progressing-progress (ste-suc {e' = e'} {a = a} d) p with progressing-progress d p
... | e₃ , b , c , step₁ , step₂ , p    = `suc e₃ , b , c , se-suc step₁ , compatible se-suc step₂ , p
progressing-progress (ste-app-seq₁ d) p with progressing-progress d p
... | e₃ , b , c , step₁ , step₂ , p    = `app e₃ _ , b , c , se-app step₁ , compatible se-app step₂ , p
progressing-progress (ste-app-seq₂ d d₁) (inj₁ p) with progressing-progress d p
... | e₃ , b , c , step₁ , step₂ , p    = 
    `app e₃ _ , _ , _ , 
      se-app step₁ , 
      ↦*-trans (compatible se-app step₂) (compatible se-app₁ (↧→↦* d₁)) , 
        Eq.trans (Eq.cong (λ a → a ∙ _) p) (assoc _ _ _)
progressing-progress (ste-app-seq₂ d d₁) (inj₂ p) with progressing-progress d₁ p with ↧→↦* d
... | e₃ , b , c , step₁ , step₂ , p | ↦*-refl            = 
    `app (`fun _) _ , _ , _ , 
      se-app₁ step₁ , 
      compatible se-app₁ step₂ , 
        Eq.trans (identityˡ _) p
... | e₃ , b , c , step₁ , step₂ , p | ↦*-step step steps = 
    `app _ _ , _ , _ , 
      se-app step , 
      ↦*-trans (compatible se-app steps) (compatible se-app₁ (↧→↦* d₁)) , 
        assoc _ _ _
progressing-progress (ste-app d d₁ v-val d₂) tt with ↧→↦* d | ↧→↦* d₁ 
... | ↦*-refl            | ↦*-refl             = _ , _ , _ , se-app₂ v-val , ↧→↦* d₂ , Eq.trans (assoc _ _ _) (identityˡ _)
... | ↦*-refl            | ↦*-step step steps  =                
    `app (`fun _) _ , _ , _ , 
      se-app₁ step , 
      ↦*-trans (compatible se-app₁ steps) (↦*-step (se-app₂ v-val) (↧→↦* d₂)) , 
        Eq.trans (Eq.cong (λ a → a ∙ _) (identityˡ _)) (Eq.trans (assoc _ _ _) (Eq.cong (λ a → _ ∙ (_ ∙ a)) (Eq.sym ((identityˡ _)))))
... | ↦*-step step steps | _                   = 
    `app _ _ , _ , _ , 
      se-app step , 
      ↦*-trans (compatible se-app steps) (↦*-trans (compatible se-app₁ (↧→↦* d₁)) (↦*-step (se-app₂ v-val) (↧→↦* d₂))) , 
        Eq.trans (assoc _ _ _) (Eq.trans (assoc _ _ _) (Eq.cong (λ a → _ ∙ (_ ∙ (_ ∙ a))) (Eq.sym (identityˡ _)))) 
progressing-progress (ste-case-seq d) p with progressing-progress d p 
... | e₃ , b , c , step₁ , step₂ , p    = `case _ _ _ , _ , _ , se-case step₁ , compatible se-case step₂ , p
progressing-progress (ste-case-z {e₁ = e₁} d d₁) tt with ↧→↦* d  
... | ↦*-refl            = e₁ , _ , _ , se-case-z , ↧→↦* d₁ , Eq.refl
... | ↦*-step step steps = 
    `case _ _ _ , _ , _ , 
      se-case step , 
      ↦*-trans (compatible se-case steps) (↦*-step se-case-z (↧→↦* d₁)) , 
        Eq.trans (assoc _ _ _) (Eq.cong (λ d → _ ∙ (_ ∙ d)) (Eq.sym (identityˡ _))) 
progressing-progress (ste-case-s {e₂ = e₂} d v-val d₁) tt with ↧→↦* d 
... | ↦*-refl            = e₂ [ _ ] , _ , _ , se-case-s v-val , ↧→↦* d₁ , Eq.refl
... | ↦*-step step steps = 
    `case _ _ _ , _ , _ , 
      se-case step , 
      ↦*-trans (compatible se-case steps) (↦*-step (se-case-s v-val) (↧→↦* d₁)) , 
        Eq.trans (assoc _ _ _) (Eq.cong (λ d → _ ∙ (_ ∙ d)) (Eq.sym (identityˡ _)))
progressing-progress (ste-eff {e = e} d) tt = e , _ , _ , se-eff , ↧→↦* d , Eq.refl
