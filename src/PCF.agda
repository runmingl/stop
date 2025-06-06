open import Prelude

open import Level

module PCF {c ℓ : Level} (monoid : MonoidWithLeftZero c ℓ) where
    
open MonoidWithLeftZero monoid public renaming (Carrier to Effect)

infixr 7 _⇒_
data Type : Set where
  Nat : Type
  _⇒_ : Type → Type → Type 
  
infixl 5 _#_
data Ctx : Set where
  ·   : Ctx
  _#_ : Ctx → Type → Ctx

private
  variable
    τ σ : Type
    Γ : Ctx

data _∋_ : Ctx → Type → Set where
  Z : (Γ # τ) ∋ τ
  S : Γ ∋ τ → (Γ # σ) ∋ τ

infix 4 _⊢_
data _⊢_ : Ctx → Type → Set c where
  `_    : 
      Γ ∋ τ 
    ------------------------
    → Γ ⊢ τ

  `zero : 
    
    ------------------------
    Γ ⊢ Nat

  `suc  : 
      Γ ⊢ Nat 
    ------------------------
    → Γ ⊢ Nat

  `case :
      Γ ⊢ Nat
    → Γ ⊢ τ
    → Γ # Nat ⊢ τ
    ------------------------
    → Γ ⊢ τ

  `fun  : 
      Γ # τ ⇒ σ # τ ⊢ σ 
    ------------------------
    → Γ ⊢ τ ⇒ σ 

  `app  : 
      Γ ⊢ τ ⇒ σ
    → Γ ⊢ τ
    ------------------------
    → Γ ⊢ σ

  `eff  : 
      Effect 
    → Γ ⊢ τ
    ------------------------
    → Γ ⊢ τ

data _val : · ⊢ τ → Set c where 
  v-zero :

    ------------------------
    `zero val

  v-suc  : {v : · ⊢ Nat} → 
      v val
    ------------------------
    → (`suc v) val 

  v-fun  : {e : · # τ ⇒ σ # τ ⊢ σ} 

    ------------------------
    → (`fun e) val
