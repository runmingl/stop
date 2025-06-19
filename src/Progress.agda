
{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude 

open import Level 
open import Data.Unit 
open import Data.Empty
open import Data.Sum
open import Relation.Binary.PropositionalEquality as Eq using (cong; _≡_; module ≡-Reasoning)

module Progress {ℓ : Level} (monoid : MonoidWithLeftZero ℓ) where

open import PCF monoid
open import Substitution monoid

open import BigStop monoid 

private
  variable
    τ σ : Type

progressing : {e e' : · ⊢ τ} {a : Effect} → e ⇓ e' ↝ a → Set
progressing ste-zero             = ⊥
progressing (ste-suc _)          = ⊤
progressing ste-fun              = ⊥
progressing (ste-app-seq₁ d)     = progressing d
progressing (ste-app-seq₂ d₁ d₂) = progressing d₁ ⊎ progressing d₂
progressing (ste-app _ _ _ _)    = ⊤
progressing (ste-case-seq d)     = progressing d
progressing (ste-case-z _ _)     = ⊤
progressing (ste-case-s _ _ _)   = ⊤
progressing (ste-eff _)          = ⊤
progressing ste-stop             = ⊥