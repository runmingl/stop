open import Prelude

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)
open import Level
open import Function.Base using (_∘_)

-- Adapted from PLFA https://plfa.github.io/Substitution

module Language.Substitution {ℓ : Level} (monoid : Monoid ℓ) where

open import Language.PCF monoid 

private 
  variable 
    A A₁ A₂ B : Type
    Γ Δ Ξ : Ctx

Subst : Ctx → Ctx → Set ℓ
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

Rename : Ctx → Ctx → Set ℓ
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A B} → (Γ # B) ∋ A → (Δ # B) ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : Rename Γ Δ → Γ ⊢ A → Δ ⊢ A
rename ρ (` x)           = ` (ρ x)
rename ρ `zero           = `zero
rename ρ (`suc x)        = `suc (rename ρ x)
rename ρ (`case e e₁ e₂) = `case (rename ρ e) (rename ρ e₁) (rename (ext ρ) e₂)
rename ρ (`fun e)        = `fun (rename (ext (ext ρ)) e)
rename ρ (`app e₁ e₂)    = `app (rename ρ e₁) (rename ρ e₂)
rename ρ (`eff a e)      = `eff a (rename ρ e)

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A B} → (Γ # B) ∋ A → (Δ # B) ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S (σ x)

subst : Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
subst γ (` x)           = γ x
subst γ `zero           = `zero
subst γ (`suc x)        = `suc (subst γ x)
subst γ (`case e e₁ e₂) = `case (subst γ e) (subst γ e₁) (subst (exts γ) e₂)
subst γ (`fun e)        = `fun (subst (exts (exts γ)) e)
subst γ (`app e₁ e₂)    = `app (subst γ e₁) (subst γ e₂)
subst γ (`eff a e)      = `eff a (subst γ e)

⟪_⟫ : Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
⟪ σ ⟫ = λ e → subst σ e

extend : Δ ⊢ A → Subst Γ Δ → Subst (Γ # A) Δ
extend v γ Z     = v
extend v γ (S x) = γ x

ids : Subst Γ Γ
ids = `_ 

subst-zero : ∀ {Γ B} → Γ ⊢ B → ∀ {A} → (Γ # B) ∋ A → Γ ⊢ A
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x

subst-zero-one : Γ ⊢ A₁ →  Γ ⊢ A₂ → (Γ # A₁ # A₂) ∋ A → Γ ⊢ A
subst-zero-one e₁ e₂ Z         =  e₂
subst-zero-one e₁ e₂ (S Z)     =  e₁
subst-zero-one e₁ e₂ (S (S x)) = ` x

↑ : Subst Γ (Γ # A)
↑ x = ` (S x)

⇈ : Γ ⊢ A → Γ # B ⊢ A
⇈ = subst ↑

_[_] : Γ # A ⊢ B → Γ ⊢ A → Γ ⊢ B
_[_] e e₁ = subst (subst-zero e₁) e

_[_][_] : Γ # A₁ # A₂ ⊢ B → Γ ⊢ A₁ → Γ ⊢ A₂ → Γ ⊢ B
_[_][_] e e₁ e₂ = subst (subst-zero-one e₁ e₂) e

infixr 6 _•'_
_•'_ : ∀ {Γ Δ A} → Δ ⊢ A → Subst Γ Δ → Subst (Γ # A) Δ
(M •' σ) Z     = M
(M •' σ) (S x) = σ x

infixr 5 _⨟_
_⨟_ : ∀ {Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ ⨟ τ = ⟪ τ ⟫ ∘ σ

ren : ∀ {Γ Δ} → Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ

sub-head : ∀ {Γ Δ} {A} {M : Δ ⊢ A} {σ : Subst Γ Δ} → ⟪ M •' σ ⟫ (` Z) ≡ M
sub-head = Eq.refl

sub-tail : ∀ {Γ Δ} {A B} {M : Δ ⊢ A} {σ : Subst Γ Δ} → (↑ ⨟ M •' σ) {A = B} ≡ σ
sub-tail = funext λ x → Eq.refl

sub-η : ∀ {Γ Δ} {A B} {σ : Subst (Γ # A) Δ}
      → (⟪ σ ⟫ (` Z) •' (↑ ⨟ σ)) {A = B} ≡ σ
sub-η {Γ} {Δ} {A} {B} {σ} = funext lemma
   where
   lemma : (x : (Γ # A) ∋ B) → ((⟪ σ ⟫ (` Z)) •' (↑ ⨟ σ)) x ≡ σ x
   lemma Z = Eq.refl
   lemma (S x) = Eq.refl

Z-shift : ∀ {Γ} {A B}
        → ((` Z) •' ↑) ≡ ids {Γ # A} {B}
Z-shift {Γ} {A} {B} = funext lemma
   where
   lemma : (x : (Γ # A) ∋ B) → ((` Z) •' ↑) x ≡ ids x
   lemma Z = Eq.refl
   lemma (S y) = Eq.refl

sub-idL : ∀ {Γ Δ} {σ : Subst Γ Δ} {A}
       → ids ⨟ σ ≡ σ {A}
sub-idL = funext λ x → Eq.refl

sub-dist :  ∀ {Γ Δ Σ : Ctx} {A B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
              {M : Δ ⊢ A}
         → ((M •' σ) ⨟ τ) ≡ ((subst τ M) •' (σ ⨟ τ)) {B}
sub-dist {Γ} {Δ} {Σ} {A} {B} {σ} {τ} {M} = funext lemma
  where
  lemma : (x : (Γ # A) ∋ B) → ((M •' σ) ⨟ τ) x ≡ ((subst τ M) •' (σ ⨟ τ)) x
  lemma Z = Eq.refl
  lemma (S x) = Eq.refl

sub-zero : ∀ {σ : Subst Γ Δ} → ⟪ σ ⟫ (`zero) ≡ `zero
sub-zero = Eq.refl

sub-suc : ∀ {σ : Subst Γ Δ} {e : Γ ⊢ Nat} → ⟪ σ ⟫ (`suc e) ≡ `suc (⟪ σ ⟫ e)
sub-suc = Eq.refl

sub-case : ∀ {σ : Subst Γ Δ} {e : Γ ⊢ Nat} {e₁ : Γ ⊢ A} {e₂ : Γ # Nat ⊢ A} → 
  ⟪ σ ⟫ (`case e e₁ e₂) ≡ `case (⟪ σ ⟫ e) (⟪ σ ⟫ e₁) (subst (exts σ) e₂)
sub-case = Eq.refl

sub-fun : ∀ {σ : Subst Γ Δ} {e : Γ # A₁ ⇒ A₂ # A₁ ⊢ A₂} → 
  ⟪ σ ⟫ (`fun e) ≡ `fun (subst (exts (exts σ)) e)
sub-fun = Eq.refl

sub-app : ∀ {σ : Subst Γ Δ} {e₁ : Γ ⊢ A₁ ⇒ A₂} {e₂ : Γ ⊢ A₁} → 
  ⟪ σ ⟫ (`app e₁ e₂) ≡ `app (⟪ σ ⟫ e₁) (⟪ σ ⟫ e₂)
sub-app = Eq.refl

sub-eff : ∀ {σ : Subst Γ Δ} {a : Effect} {e : Γ ⊢ A} → ⟪ σ ⟫ (`eff a e) ≡ `eff a (⟪ σ ⟫ e)
sub-eff = Eq.refl

cong-ext : ∀ {Γ Δ} {ρ ρ′ : Rename Γ Δ}{B}
   → (∀ {A} → ρ ≡ ρ′ {A})
   → ∀ {A} → ext ρ {B = B} ≡ ext ρ′ 
cong-ext {Γ} {Δ} {ρ} {ρ′} {B} rr {A} = funext lemma
  where
  lemma : (x : (Γ # B) ∋ A) → ext ρ x ≡ ext ρ′ x
  lemma Z = Eq.refl
  lemma (S y) = Eq.cong S (Eq.cong-app rr y)

cong-rename : ∀ {Γ Δ} {ρ ρ′ : Rename Γ Δ} {B} {M : Γ ⊢ B}
  → (∀ {A} → ρ ≡ ρ′ {A})
  → rename ρ M ≡ rename ρ′ M
cong-rename {M = ` x}           rr = Eq.cong `_ (Eq.cong-app rr x)
cong-rename {M = `zero}         rr = Eq.refl
cong-rename {M = `suc M}        rr = Eq.cong `suc (cong-rename rr)
cong-rename {M = `case M M₁ M₂} rr = cong₃ `case (cong-rename rr) (cong-rename rr) (cong-rename (cong-ext rr))
cong-rename {M = `fun M}        rr = Eq.cong `fun (cong-rename (cong-ext (cong-ext rr)))
cong-rename {M = `app M M₁}     rr = Eq.cong₂ `app (cong-rename rr) (cong-rename rr)
cong-rename {M = `eff a M}      rr = Eq.cong (λ M → `eff a M) (cong-rename rr)

cong-exts : ∀ {Γ Δ} {σ σ′ : Subst Γ Δ} {B}
   → (∀ {A} → σ ≡ σ′ {A}) 
   → ∀{A} → exts σ {B = B} ≡ exts σ′ {A}
cong-exts {Γ} {Δ} {σ} {σ′} {B} ss {A} = funext lemma
   where
   lemma : (x : (Γ # B) ∋ A) → exts σ x ≡ exts σ′ x
   lemma Z = Eq.refl
   lemma (S x) = Eq.cong (rename S) (Eq.cong-app (ss {A}) x)

cong-sub : ∀ {Γ Δ} {σ σ′ : Subst Γ Δ} {A} {M M′ : Γ ⊢ A}
  → (∀ {A} → σ ≡ σ′ {A})  
  →  M ≡ M′
  → subst σ M ≡ subst σ′ M′
cong-sub {M = ` x} ss Eq.refl     = Eq.cong-app ss x
cong-sub {M = `zero} ss Eq.refl   = Eq.refl
cong-sub {M = `suc M} ss Eq.refl  = Eq.cong `suc (cong-sub {M = M} ss Eq.refl)
cong-sub {M = `case M M₁ M₂} ss Eq.refl = 
  cong₃ `case (cong-sub {M = M} ss Eq.refl) (cong-sub {M = M₁} ss Eq.refl) (cong-sub {M = M₂} (cong-exts ss) Eq.refl)
cong-sub {M = `fun M} ss Eq.refl = 
  Eq.cong `fun (cong-sub {M = M} (cong-exts (cong-exts ss)) Eq.refl)
cong-sub {M = `app M M₁} ss Eq.refl = 
  Eq.cong₂ `app (cong-sub {M = M} ss Eq.refl) (cong-sub {M = M₁} ss Eq.refl)
cong-sub {M = `eff a M} ss Eq.refl = Eq.cong (λ M → `eff a M) (cong-sub {M = M} ss Eq.refl)

cong-sub-zero : ∀ {Γ} {B : Type} {M M′ : Γ ⊢ B}
  → M ≡ M′
  → ∀ {A} → subst-zero M ≡ (subst-zero M′) {A}
cong-sub-zero {Γ} {B} {M} {M′} mm' {A} =
   funext λ x → Eq.cong (λ z → subst-zero z x) mm'

cong-cons : ∀ {Γ Δ} {A} {M N : Δ ⊢ A} {σ τ : Subst Γ Δ}
  → M ≡ N  
  → (∀ {A} → σ {A} ≡ τ {A})
  → ∀ {A} → (M •' σ) {A} ≡ (N •' τ) {A}
cong-cons {Γ} {Δ} {A} {M} {N} {σ} {τ} Eq.refl st {A′} = funext lemma
  where
  lemma : (x : (Γ # A) ∋ A′) → (M •' σ) x ≡ (M •' τ) x
  lemma Z = Eq.refl
  lemma (S x) = Eq.cong-app st x

cong-seq : ∀ {Γ Δ Σ} {σ σ′ : Subst Γ Δ} {τ τ′ : Subst Δ Σ}
  → (∀ {A} → σ {A} ≡ σ′ {A}) 
  → (∀ {A} → τ {A} ≡ τ′ {A})
  → ∀ {A} → (σ ⨟ τ) {A} ≡ (σ′ ⨟ τ′) {A}
cong-seq {Γ} {Δ} {Σ} {σ} {σ′} {τ} {τ′} ss' tt' {A} = funext lemma
  where
  lemma : (x : Γ ∋ A) → (σ ⨟ τ) x ≡ (σ′ ⨟ τ′) x
  lemma x =
     let open ≡-Reasoning in
     begin
       (σ ⨟ τ) x
     ≡⟨⟩
       subst τ (σ x)
     ≡⟨ Eq.cong (subst τ) (Eq.cong-app ss' x) ⟩
       subst τ (σ′ x)
     ≡⟨ cong-sub{M = σ′ x} tt' Eq.refl ⟩
       subst τ′ (σ′ x)
     ≡⟨⟩
       (σ′ ⨟ τ′) x
     ∎

ren-ext : ∀ {Γ Δ} {B C : Type} {ρ : Rename Γ Δ}
  → ren (ext ρ {B = B}) ≡ exts (ren ρ) {C}
ren-ext {Γ} {Δ} {B} {C} {ρ} = funext lemma
  where
  lemma : (x : (Γ # B) ∋ C) → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma Z  = Eq.refl
  lemma (S x) = Eq.refl

rename-subst-ren : ∀ {Γ Δ}{A} {ρ : Rename Γ Δ}{M : Γ ⊢ A}
                 → rename ρ M ≡ ⟪ ren ρ ⟫ M
rename-subst-ren {ρ = ρ} {M = ` x} = Eq.refl
rename-subst-ren {ρ = ρ} {M = `zero} = Eq.refl
rename-subst-ren {ρ = ρ} {M = `suc M} = Eq.cong `suc rename-subst-ren
rename-subst-ren {ρ = ρ} {M = `case M M₁ M₂} = 
  let open ≡-Reasoning in
  begin 
    rename ρ (`case M M₁ M₂)
  ≡⟨⟩
    `case (rename ρ M) (rename ρ M₁) (rename (ext ρ) M₂)
  ≡⟨ cong₃ `case rename-subst-ren rename-subst-ren (rename-subst-ren {ρ = ext ρ}) ⟩ 
    `case (⟪ ren ρ ⟫ M) (⟪ ren ρ ⟫ M₁) (⟪ ren (ext ρ) ⟫ M₂)
  ≡⟨ Eq.cong (λ M → `case _ _ M) (cong-sub {M = M₂} ren-ext Eq.refl) ⟩
    `case (⟪ ren ρ ⟫ M) (⟪ ren ρ ⟫ M₁) (⟪ exts (ren ρ) ⟫ M₂)
  ≡⟨⟩
    ⟪ ren ρ ⟫ (`case M M₁ M₂)
  ∎
rename-subst-ren {Γ = Γ} {Δ = Δ} {ρ = ρ} {M = `fun {τ = τ} {σ = σ} M} = 
  let open ≡-Reasoning in
  begin
    rename ρ (`fun M)
  ≡⟨⟩
    `fun (rename (ext (ext ρ)) M)
  ≡⟨ Eq.cong `fun rename-subst-ren ⟩
    `fun (⟪ ren (ext (ext ρ)) ⟫ M)
  ≡⟨ Eq.cong `fun (cong-sub {M = M} ren-ext Eq.refl) ⟩
    `fun (⟪ exts (ren (ext ρ)) ⟫ M)
  ≡⟨ Eq.cong `fun (cong-sub {M = M} (cong-exts ren-ext) Eq.refl) ⟩
    `fun (⟪ exts (exts (ren ρ)) ⟫ M)
  ≡⟨⟩
    ⟪ ren ρ ⟫ (`fun M)
  ∎
rename-subst-ren {ρ = ρ} {M = `app M M₁} = Eq.cong₂ `app rename-subst-ren rename-subst-ren
rename-subst-ren {ρ = ρ} {M = `eff a M} = Eq.cong (λ M → `eff a M) rename-subst-ren

ren-shift : ∀ {Γ} {A} {B}
  → ren S ≡ ↑ {A = B} {A}
ren-shift {Γ} {A} {B} = funext lemma
  where
  lemma : (x : Γ ∋ A) → ren S x ≡ ↑ {A = B} x
  lemma Z     = Eq.refl
  lemma (S x) = Eq.refl

rename-shift : ∀ {Γ} {A} {B} {M : Γ ⊢ A}
             → rename (S {σ = B}) M ≡ ⟪ ↑ ⟫ M
rename-shift {Γ} {A} {B} {M} =
  let open ≡-Reasoning in
  begin
    rename S M
  ≡⟨ rename-subst-ren ⟩
    ⟪ ren S ⟫ M
  ≡⟨ cong-sub {M = M} ren-shift Eq.refl ⟩
    ⟪ ↑ ⟫ M
  ∎

exts-cons-shift : ∀ {Γ Δ} {A B} {σ : Subst Γ Δ}
                → exts σ {A} {B} ≡ (` Z •' (σ ⨟ ↑))
exts-cons-shift = funext lemma
  where
  lemma : ∀ {Γ Δ} {A B} {σ : Subst Γ Δ} (x : (Γ # B) ∋ A) → exts σ x ≡ (` Z •' (σ ⨟ ↑)) x
  lemma Z = Eq.refl
  lemma (S y) = rename-subst-ren

ext-cons-Z-shift : ∀ {Γ Δ} {ρ : Rename Γ Δ} {A} {B}
                 → ren (ext ρ {B = B}) ≡ (` Z •' (ren ρ ⨟ ↑)) {A}
ext-cons-Z-shift {Γ} {Δ} {ρ} {A} {B} =
  let open ≡-Reasoning in 
  begin
    ren (ext ρ)
  ≡⟨ ren-ext ⟩
    exts (ren ρ)
  ≡⟨ exts-cons-shift{σ = ren ρ} ⟩
   ((` Z) •' (ren ρ ⨟ ↑))
  ∎

subst-Z-cons-ids : ∀ {Γ} {A B : Type} {M : Γ ⊢ B}
  → subst-zero M ≡ (M •' ids) {A}
subst-Z-cons-ids = funext lemma
  where
  lemma : ∀ {Γ} {A B : Type} {M : Γ ⊢ B} (x : (Γ # B) ∋ A) → subst-zero M x ≡ (M •' ids) x
  lemma Z = Eq.refl 
  lemma (S y) = Eq.refl

exts-ids : ∀ {Γ} {A B} → exts ids ≡ ids {Γ # B} {A}
exts-ids {Γ} {A} {B} = funext lemma
  where 
  lemma : (x : (Γ # B) ∋ A) → exts ids x ≡ ids x
  lemma Z = Eq.refl
  lemma (S x) = Eq.refl

sub-id : ∀ {Γ} {A} {M : Γ ⊢ A} → ⟪ ids ⟫ M ≡ M
sub-id {M = ` x} = Eq.refl
sub-id {M = `zero} = Eq.refl
sub-id {M = `suc M} = Eq.cong `suc sub-id
sub-id {M = `case M M₁ M₂} = 
  let open ≡-Reasoning in
  begin 
    ⟪ ids ⟫ (`case M M₁ M₂)
  ≡⟨⟩
    `case (⟪ ids ⟫ M) (⟪ ids ⟫ M₁) (⟪ exts ids ⟫ M₂)
  ≡⟨ cong₃ `case sub-id sub-id (Eq.trans (cong-sub {M = M₂} exts-ids Eq.refl) sub-id) ⟩
    `case M M₁ M₂
  ∎
sub-id {Γ = Γ} {M = `fun {τ = τ} {σ = σ} M} = 
  let open ≡-Reasoning in
  begin
    ⟪ ids ⟫ (`fun M)
  ≡⟨⟩
    `fun (⟪ exts (exts ids) ⟫ M)
  ≡⟨ Eq.cong `fun (cong-sub {M = M} (cong-exts exts-ids) Eq.refl) ⟩ 
    `fun (⟪ exts ids ⟫ M)
  ≡⟨ Eq.cong `fun (cong-sub {M = M} exts-ids Eq.refl) ⟩
    `fun (⟪ ids ⟫ M)
  ≡⟨ Eq.cong `fun sub-id ⟩
    `fun M
  ∎
sub-id {M = `app M M₁} = Eq.cong₂ `app sub-id sub-id
sub-id {M = `eff a M} = Eq.cong (λ M → `eff a M) sub-id

rename-id : ∀ {Γ} {A} {M : Γ ⊢ A} → rename (λ {A} x → x) M ≡ M
rename-id {M = M} =
  let open ≡-Reasoning in
  begin
    rename (λ {A} x → x) M
  ≡⟨ rename-subst-ren  ⟩
    ⟪ ren (λ {A} x → x) ⟫ M
  ≡⟨⟩
    ⟪ ids ⟫ M
  ≡⟨ sub-id  ⟩
    M
  ∎

sub-idR : ∀ {Γ Δ} {σ : Subst Γ Δ} {A} → (σ ⨟ ids) ≡ σ {A}
sub-idR {Γ} {σ = σ} {A} =
  let open ≡-Reasoning in
  begin
    σ ⨟ ids
  ≡⟨⟩
    ⟪ ids ⟫ ∘ σ
  ≡⟨ funext (λ x → sub-id) ⟩
    σ
  ∎

compose-ext : ∀ {Γ Δ Σ} {ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B}
  → ((ext ρ) ∘ (ext ρ′)) ≡ ext (ρ ∘ ρ′) {B} {A}
compose-ext = funext lemma
  where
  lemma : ∀ {Γ Δ Σ} {ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B} (x : (Γ # B) ∋ A)
              → ((ext ρ) ∘ (ext ρ′)) x ≡ ext (ρ ∘ ρ′) x
  lemma Z  = Eq.refl
  lemma (S x) = Eq.refl

compose-rename : ∀ {Γ Δ Σ} {A} {M : Γ ⊢ A} {ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ}
  → rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M
compose-rename {M = ` x} = Eq.refl
compose-rename {M = `zero} = Eq.refl
compose-rename {M = `suc M} = Eq.cong `suc compose-rename
compose-rename {Γ} {Δ} {Σ} {A} {M = `case M M₁ M₂} {ρ} {ρ′} = 
  let open ≡-Reasoning in
  begin 
    `case (rename ρ (rename ρ′ M)) (rename ρ (rename ρ′ M₁)) (rename (ext ρ) (rename (ext ρ′) M₂))
  ≡⟨ cong₃ `case compose-rename compose-rename (Eq.trans (compose-rename {ρ = ext ρ} {ρ′ = ext ρ′}) (cong-rename compose-ext)) ⟩
    `case (rename (ρ ∘ ρ′) M) (rename (ρ ∘ ρ′) M₁) (rename (ext (ρ ∘ ρ′)) M₂)
  ∎
compose-rename {Γ} {Δ} {Σ} {A} {M = `fun {τ = τ} {σ = σ} M} {ρ} {ρ′} = 
  let open ≡-Reasoning in
  begin
    `fun (rename (ext (ext ρ)) (rename (ext (ext ρ′)) M))
  ≡⟨ Eq.cong `fun (compose-rename {ρ = ext (ext ρ)}) ⟩
    `fun (rename (ext (ext ρ) ∘ (ext (ext ρ′))) M)
  ≡⟨ Eq.cong `fun (cong-rename compose-ext) ⟩ 
    `fun (rename (ext (ext ρ ∘ (ext ρ′))) M)
  ≡⟨ Eq.cong `fun (cong-rename (cong-ext compose-ext)) ⟩ 
    `fun (rename (ext (ext (ρ ∘ ρ′))) M)
  ∎
compose-rename {M = `app M M₁} = Eq.cong₂ `app compose-rename compose-rename
compose-rename {M = `eff a M} = Eq.cong (λ M → `eff a M) compose-rename

-- https://github.com/plfa/plfa.github.io/issues/858
commute-subst-rename : ∀ {Γ Δ Δ' Ξ} {A} {M : Γ ⊢ A}
                        {ρ  : Rename Γ Δ } {σ  : Subst  Δ  Ξ}
                        {σ' : Subst  Γ Δ'} {ρ' : Rename Δ' Ξ}
     → (∀ {A} {x : Γ ∋ A} → σ (ρ x) ≡ rename ρ' (σ' x))
     → subst σ (rename ρ M) ≡ rename ρ' (subst σ' M)
commute-subst-rename {M = ` x} H = H
commute-subst-rename {M = `zero} H = Eq.refl
commute-subst-rename {M = `suc M} H = Eq.cong `suc (commute-subst-rename {M = M} H)
commute-subst-rename {Γ = Γ} {A = A} {M = `case M M₁ M₂} {ρ} {σ} {σ'} {ρ'} H = 
  cong₃ `case (commute-subst-rename {M = M} H) (commute-subst-rename {M = M₁} H) (commute-subst-rename {M = M₂} {ρ = ext ρ} {σ = exts σ} (λ {A} {x : (Γ # Nat) ∋ A} → H' {x = x}))
  where
    H' : {x : (Γ # Nat) ∋ B} → exts σ (ext ρ x) ≡ rename (ext ρ') (exts σ' x)
    H' {x = Z} = Eq.refl
    H' {x = S y} = 
      let open ≡-Reasoning in
      begin
         exts σ (ext ρ (S y))
       ≡⟨⟩
         rename S (σ (ρ y))
       ≡⟨ Eq.cong (rename S) H ⟩
         rename S (rename ρ' (σ' y))
       ≡⟨ compose-rename ⟩
         rename (S ∘ ρ') (σ' y)
       ≡⟨ cong-rename Eq.refl ⟩
         rename ((ext ρ') ∘ S) (σ' y)
       ≡⟨ compose-rename ⟨
         rename (ext ρ') (rename S (σ' y))
       ≡⟨⟩
         rename (ext ρ') (exts σ' (S y))
       ∎
commute-subst-rename {Γ = Γ} {A = A} {M = `fun {τ = τ} {σ = σ₁} M} {ρ} {σ} {σ'} {ρ'} H = 
  Eq.cong `fun (commute-subst-rename {M = M} {ρ = ext (ext ρ)} {σ = exts (exts σ)} (λ {A} {x : (Γ # τ ⇒ σ₁ # τ) ∋ A} → H'' {x = x}))
   where 
      H' : {x : (Γ # τ ⇒ σ₁) ∋ B} → exts σ (ext ρ x) ≡ rename (ext ρ') (exts σ' x)
      H' {x = Z} = Eq.refl
      H' {x = S y} = 
        let open ≡-Reasoning in
        begin
           exts σ (ext ρ (S y))
         ≡⟨⟩
           rename S (σ (ρ y))
         ≡⟨ Eq.cong (rename S) H ⟩
           rename S (rename ρ' (σ' y))
         ≡⟨ compose-rename ⟩
           rename (S ∘ ρ') (σ' y)
         ≡⟨ cong-rename Eq.refl ⟩
           rename ((ext ρ') ∘ S) (σ' y)
         ≡⟨ compose-rename ⟨
           rename (ext ρ') (rename S (σ' y))
         ≡⟨⟩
           rename (ext ρ') (exts σ' (S y))
         ∎

      H'' : {x : (Γ # τ ⇒ σ₁ # τ) ∋ B} → exts (exts σ) (ext (ext ρ) x) ≡ rename (ext (ext ρ')) (exts (exts σ') x)
      H'' {x = Z}   = Eq.refl
      H'' {x = S x} = 
        let open ≡-Reasoning in
        begin 
          rename S (exts σ (ext ρ x))
        ≡⟨ Eq.cong (rename S) (H' {x = x}) ⟩
          rename S (rename (ext ρ') (exts σ' x))
        ≡⟨ compose-rename ⟩
          rename (S ∘ (ext ρ')) (exts σ' x)
        ≡⟨ compose-rename ⟨ 
          rename (ext (ext ρ')) (rename S (exts σ' x))
        ∎
commute-subst-rename {M = `app M M₁} H = 
  Eq.cong₂ `app (commute-subst-rename {M = M} H) (commute-subst-rename {M = M₁} H) 
commute-subst-rename {M = `eff a M} H = 
  Eq.cong (λ M → `eff a M) (commute-subst-rename {M = M} H)

exts-seq : ∀{Γ Δ Δ′} {σ₁ : Subst Γ Δ} {σ₂ : Subst Δ Δ′}
         → ∀ {A B} → ((exts σ₁ {B = B}) ⨟ exts σ₂) {A} ≡ exts (σ₁ ⨟ σ₂)
exts-seq {Γ = Γ} {σ₁ = σ₁} {σ₂ = σ₂} {A} {B} = funext lemma
  where 
    lemma : (x : (Γ # B) ∋ A) → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
    lemma Z = Eq.refl
    lemma (S x) = 
      let open ≡-Reasoning in
      begin
        (exts σ₁ ⨟ exts σ₂) (S x)
      ≡⟨⟩
        subst (exts σ₂) (rename S (σ₁ x)) 
      ≡⟨ commute-subst-rename {M = σ₁ x} Eq.refl ⟩ 
        rename S (subst σ₂ (σ₁ x))  
      ≡⟨⟩ 
        rename S ((σ₁ ⨟ σ₂) x) 
      ∎

sub-sub : ∀ {Γ Δ Σ} {A} {M : Γ ⊢ A} {σ₁ : Subst Γ Δ} {σ₂ : Subst Δ Σ}
            → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub {M = ` x}   = Eq.refl
sub-sub {M = `zero} = Eq.refl
sub-sub {M = `suc M} = Eq.cong `suc (sub-sub {M = M})
sub-sub {M = `case M M₁ M₂} {σ₁} {σ₂} = cong₃ `case (sub-sub {M = M}) (sub-sub {M = M₁}) eq
  where 
    eq : subst (exts σ₂) (subst (exts σ₁) M₂) ≡ subst (exts (σ₁ ⨟ σ₂)) M₂
    eq = 
      let open ≡-Reasoning in
      begin
        subst (exts σ₂) (subst (exts σ₁) M₂)
      ≡⟨ sub-sub {M = M₂} {σ₁ = exts σ₁} ⟩
        ⟪ exts σ₁ ⨟ exts σ₂ ⟫ M₂
      ≡⟨ cong-sub {M = M₂} (λ {A} → exts-seq) Eq.refl ⟩
        subst (exts (σ₁ ⨟ σ₂)) M₂
      ∎
sub-sub {Γ = Γ} {Σ = Σ} {M = `fun {τ = τ} {σ = σ} M} {σ₁} {σ₂} = Eq.cong `fun eq
  where
    eq : subst (exts (exts σ₂)) (subst (exts (exts σ₁)) M) ≡ subst (exts (exts (σ₁ ⨟ σ₂))) M
    eq = 
      let open ≡-Reasoning in
      begin
        subst (exts (exts σ₂)) (subst (exts (exts σ₁)) M)
      ≡⟨ sub-sub {M = M} {σ₁ = exts (exts σ₁)} ⟩
        ⟪ exts (exts σ₁) ⨟ exts (exts σ₂) ⟫ M
      ≡⟨ cong-sub {M = M} (λ {A} → exts-seq) Eq.refl ⟩
        ⟪ exts (exts σ₁ ⨟ exts σ₂) ⟫ M
      ≡⟨ cong-sub {M = M} (cong-exts exts-seq) Eq.refl ⟩ 
        subst (exts (exts (σ₁ ⨟ σ₂))) M
      ∎
sub-sub {M = `app M M₁} = 
  Eq.cong₂ `app (sub-sub {M = M}) (sub-sub {M = M₁})
sub-sub {M = `eff a M} = 
  Eq.cong (λ M → `eff a M) (sub-sub {M = M})

rename-subst : ∀ {Γ Δ Δ′} {A} {M : Γ ⊢ A} {ρ : Rename Γ Δ} {σ : Subst Δ Δ′}
             → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ σ ∘ ρ ⟫ M
rename-subst {Γ} {Δ} {Δ′} {A} {M} {ρ} {σ} =
  let open ≡-Reasoning in
  begin
    ⟪ σ ⟫ (rename ρ M)
  ≡⟨ Eq.cong ⟪ σ ⟫ (rename-subst-ren {M = M}) ⟩
    ⟪ σ ⟫ (⟪ ren ρ ⟫ M)
  ≡⟨ sub-sub{M = M} ⟩
    ⟪ ren ρ ⨟ σ ⟫ M
  ≡⟨⟩
    ⟪ σ ∘ ρ ⟫ M
  ∎

sub-assoc : ∀ {Γ Δ Σ Ψ : Ctx} {σ : Subst Γ Δ} {τ : Subst Δ Σ} {θ : Subst Σ Ψ}
  → ∀ {A} → (σ ⨟ τ) ⨟ θ ≡ (σ ⨟ τ ⨟ θ) {A}
sub-assoc {Γ}{Δ}{Σ}{Ψ}{σ}{τ}{θ}{A} = funext lemma
  where
  lemma : (x : Γ ∋ A) → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ τ ⨟ θ) x
  lemma x =
    let open ≡-Reasoning in
      begin
        ((σ ⨟ τ) ⨟ θ) x
      ≡⟨⟩
        ⟪ θ ⟫ (⟪ τ ⟫ (σ x))
      ≡⟨ sub-sub{M = σ x} ⟩
        ⟪ τ ⨟ θ ⟫ (σ x)
      ≡⟨⟩
        (σ ⨟ τ ⨟ θ) x
      ∎

subst-zero-exts-cons : ∀ {Γ Δ} {σ : Subst Γ Δ} {B} {M : Δ ⊢ B} {A}
  → exts σ ⨟ subst-zero M ≡ (M •' σ) {A}
subst-zero-exts-cons {Γ}{Δ}{σ}{B}{M}{A} =
  let open ≡-Reasoning in
  begin
    exts σ ⨟ subst-zero M
  ≡⟨ cong-seq exts-cons-shift subst-Z-cons-ids ⟩
    (` Z •' (σ ⨟ ↑)) ⨟ (M •' ids)
  ≡⟨ sub-dist ⟩
    (⟪ M •' ids ⟫ (` Z)) •' ((σ ⨟ ↑) ⨟ (M •' ids))
  ≡⟨ cong-cons (sub-head{σ = ids}) Eq.refl ⟩
    M •' ((σ ⨟ ↑) ⨟ (M •' ids))
  ≡⟨ cong-cons Eq.refl (sub-assoc {σ = σ}) ⟩
    M •' (σ ⨟ (↑ ⨟ (M •' ids)))
  ≡⟨ cong-cons Eq.refl (cong-seq {σ = σ} Eq.refl (sub-tail {M = M} {σ = ids})) ⟩
    M •' (σ ⨟ ids)
  ≡⟨ cong-cons Eq.refl (sub-idR {σ = σ}) ⟩
    M •' σ
  ∎

subst-commute : ∀ {Γ Δ} {A B} {N : Γ # A ⊢ B} {M : Γ ⊢ A} {σ : Subst Γ Δ}
    → ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {Γ}{Δ} {A} {B} {N} {M} {σ} =
     let open ≡-Reasoning in
     begin
       ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ]
     ≡⟨⟩
       ⟪ subst-zero (⟪ σ ⟫ M) ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ cong-sub {M = ⟪ exts σ ⟫ N} subst-Z-cons-ids Eq.refl ⟩
       ⟪ ⟪ σ ⟫ M •' ids ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ sub-sub {M = N} ⟩
       ⟪ (exts σ) ⨟ ((⟪ σ ⟫ M) •' ids) ⟫ N
     ≡⟨ cong-sub {M = N} (cong-seq exts-cons-shift Eq.refl) Eq.refl ⟩
       ⟪ (` Z •' (σ ⨟ ↑)) ⨟ (⟪ σ ⟫ M •' ids) ⟫ N
     ≡⟨ cong-sub {M = N} (sub-dist {M = ` Z}) Eq.refl ⟩
       ⟪ ⟪ ⟪ σ ⟫ M •' ids ⟫ (` Z) •' ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M •' ids)) ⟫ N
     ≡⟨⟩
       ⟪ ⟪ σ ⟫ M •' ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M •' ids)) ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons Eq.refl (sub-assoc{σ = σ})) Eq.refl ⟩
       ⟪ ⟪ σ ⟫ M •' (σ ⨟ ↑ ⨟ ⟪ σ ⟫ M •' ids) ⟫ N
     ≡⟨ cong-sub{M = N} Eq.refl Eq.refl ⟩
       ⟪ ⟪ σ ⟫ M •' (σ ⨟ ids) ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons Eq.refl (sub-idR{σ = σ})) Eq.refl ⟩
       ⟪ ⟪ σ ⟫ M •' σ ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons Eq.refl (sub-idL{σ = σ})) Eq.refl ⟩
       ⟪ ⟪ σ ⟫ M •' (ids ⨟ σ) ⟫ N
     ≡⟨ cong-sub{M = N} (Eq.sym sub-dist) Eq.refl ⟩
       ⟪ M •' ids ⨟ σ ⟫ N
     ≡⟨ (sub-sub{M = N}) ⟨
       ⟪ σ ⟫ (⟪ M •' ids ⟫ N)
     ≡⟨ Eq.cong ⟪ σ ⟫ (Eq.sym (cong-sub{M = N} subst-Z-cons-ids Eq.refl)) ⟩
       ⟪ σ ⟫ (N [ M ])
     ∎

rename-subst-commute : ∀ {Γ Δ} {A B} {N : Γ # A ⊢ B}{M : Γ ⊢ A} {ρ : Rename Γ Δ}
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ} {Δ} {A} {B} {N} {M} {ρ} =
  let open ≡-Reasoning in
   begin
     (rename (ext ρ) N) [ rename ρ M ]
   ≡⟨ cong-sub (cong-sub-zero (rename-subst-ren{M = M}))
               (rename-subst-ren{M = N}) ⟩
     (⟪ ren (ext ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
   ≡⟨ cong-sub Eq.refl (cong-sub{M = N} ren-ext Eq.refl) ⟩
     (⟪ exts (ren ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
   ≡⟨ subst-commute{N = N} ⟩
     subst (ren ρ) (N [ M ])
   ≡⟨ rename-subst-ren ⟨ 
     rename ρ (N [ M ])
   ∎

_〔_〕 : ∀ {Γ A B C}
        → Γ # B # C ⊢ A
        → Γ ⊢ B
          ---------
        → Γ # C ⊢ A
_〔_〕 {Γ} {A} {B} {C} N M =
   subst {Γ # B # C} {Γ # C} (exts (subst-zero M)) N
  
substitution : ∀ {Γ} {A B C} {M : Γ # B # C ⊢ A} {N : Γ # B ⊢ C} {L : Γ ⊢ B}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution{M = M}{N = N}{L = L} =
   Eq.sym (subst-commute {N = M} {M = N} {σ = subst-zero L})

shift-subst₁ : ∀ {Γ} {A B} → (e : Γ ⊢ A) (e₁ : Γ ⊢ B) → (⇈ e₁) [ e ] ≡ e₁
shift-subst₁ e e₁ = 
  let open ≡-Reasoning in 
  begin
    ⇈ e₁ [ e ]
  ≡⟨⟩
    ⟪ subst-zero e ⟫ (⟪ ↑ ⟫ e₁) 
  ≡⟨ sub-sub {M = e₁} ⟩ 
    ⟪ ↑ ⨟ subst-zero e ⟫ e₁ 
  ≡⟨ cong-sub {M = e₁} (cong-seq {σ = ↑} Eq.refl (subst-Z-cons-ids {M = e})) Eq.refl ⟩ 
    ⟪ ↑ ⨟ (e •' ids ) ⟫ e₁ 
  ≡⟨⟩ 
    ⟪ ids ⟫ e₁ 
  ≡⟨ sub-id ⟩ 
    e₁ 
  ∎ 

shift-subst₂ : ∀ {Γ} {A B} → (e : Γ ⊢ A) (e₂ : Γ # A ⊢ B) → ⟪ exts (subst-zero e) ⟫ (⟪ exts ↑ ⟫ e₂) ≡ e₂ 
shift-subst₂ e e₂ = 
  let open ≡-Reasoning in
  begin 
    ⟪ exts (subst-zero e) ⟫ (⟪ exts ↑ ⟫ e₂)
  ≡⟨ sub-sub {M = e₂} ⟩ 
    ⟪ exts ↑ ⨟ exts (subst-zero e) ⟫ e₂ 
  ≡⟨ cong-sub {M = e₂} exts-seq Eq.refl ⟩ 
    ⟪ exts (↑ ⨟ (subst-zero e)) ⟫ e₂ 
  ≡⟨ cong-sub {M = e₂} (cong-exts (cong-seq {σ = ↑} Eq.refl (subst-Z-cons-ids {M = e}))) Eq.refl ⟩ 
    ⟪ exts (↑ ⨟ (e •' ids )) ⟫ e₂ 
  ≡⟨⟩ 
    ⟪ exts ids ⟫ e₂
  ≡⟨ cong-sub {M = e₂} exts-ids Eq.refl ⟩ 
    ⟪ ids ⟫ e₂
  ≡⟨ sub-id ⟩ 
    e₂ 
  ∎ 

shift-subst₃ : ∀ {Γ} {A B C D} → (e : Γ # A # B ⊢ C) (v : Γ ⊢ D) → ⟪ exts (exts (subst-zero v)) ⟫ (⟪ exts (exts ↑) ⟫ e) ≡ e
shift-subst₃ e v = 
  let open ≡-Reasoning in
  begin 
    ⟪ exts (exts (subst-zero v)) ⟫ (⟪ exts (exts ↑) ⟫ e)
  ≡⟨ sub-sub {M = e} ⟩ 
    ⟪ exts (exts ↑) ⨟ exts (exts (subst-zero v)) ⟫ e
  ≡⟨ cong-sub {M = e} exts-seq Eq.refl ⟩
    ⟪ exts ((exts ↑) ⨟ (exts (subst-zero v))) ⟫ e
  ≡⟨ cong-sub {M = e} (cong-exts exts-seq) Eq.refl ⟩ 
    ⟪ exts (exts (↑ ⨟ (subst-zero v))) ⟫ e
  ≡⟨ cong-sub {M = e} (cong-exts (cong-exts (cong-seq {σ = ↑} Eq.refl (subst-Z-cons-ids {M = v})))) Eq.refl ⟩ 
    ⟪ exts (exts (↑ ⨟ (v •' ids ))) ⟫ e
  ≡⟨⟩ 
    ⟪ exts (exts ids) ⟫ e
  ≡⟨ cong-sub {M = e} (cong-exts exts-ids) Eq.refl ⟩ 
    ⟪ exts ids ⟫ e 
  ≡⟨ cong-sub {M = e} exts-ids Eq.refl ⟩ 
    ⟪ ids ⟫ e
  ≡⟨ sub-id ⟩ 
    e
  ∎