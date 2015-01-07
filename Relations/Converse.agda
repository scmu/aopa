{-# OPTIONS --universe-polymorphism #-}

module Relations.Converse where

open import Level
open import Data.Product  using (Σ; _×_; _,_)

open import Sets
open import Relations 
open import AlgebraicReasoning.Implications

-- ˘-universal : X ⊑ R ˘  ⇔  X ˘ ⊑ R

˘-universal-⇒  : ∀ {i j} {A : Set i} {B : Set j} {X : A ← B} {R : B ← A} → 
                 X ⊑ R ˘ → X ˘ ⊑ R
˘-universal-⇒ X⊑R˘ a b aXb = X⊑R˘ b a aXb

˘-universal-⇐ : ∀ {i j} {A : Set i} {B : Set j} {X : A ← B} {R : B ← A} → 
                  X ˘ ⊑ R → X ⊑ R ˘
˘-universal-⇐ X˘⊑R b a bXa = X˘⊑R a b bXa 

-- id ≑ id˘

id⊑id˘ : {A : Set} → idR {A} ⊑ (idR {A})˘
id⊑id˘ a a' = sym 

id˘⊑id : {A : Set} → (idR {A})˘ ⊑ idR {A}
id˘⊑id a a' = sym 

-- C ≑ C˘ if C ⊑ id

C⊑C˘ : {A : Set}{C : A ← A} → C ⊑ idR → C ⊑ C ˘
C⊑C˘ C⊑id a a' aCa' with C⊑id a a' aCa' 
C⊑C˘ C⊑id a .a aCa' | refl = aCa' 

C˘⊑C : {A : Set}{C : A ← A} → C ⊑ idR → C ˘ ⊑ C
C˘⊑C C⊑id a a' a'Ca with C⊑id a' a a'Ca 
C˘⊑C C⊑id a .a a'Ca | refl = a'Ca 

-- ˘-idempotent : R˘˘ ≑ R

˘-idempotent-⊑ : ∀ {i j} {A : Set i} {B : Set j} → {R : A ← B} → (R ˘) ˘ ⊑ R
˘-idempotent-⊑ = ˘-universal-⇒ ⊑-refl

˘-idempotent-⊒ : ∀ {i j} {A : Set i} {B : Set j} → {R : A ← B} → R ⊑ (R ˘) ˘
˘-idempotent-⊒ = ˘-universal-⇐ ⊑-refl

-- monotonicity: R ˘ ⊑ S ˘ ⇔ R ⊑ S

 -- Why can they not be level polymorphic?

˘-monotonic-⇒ : {A B : Set} {R S : B ← A} →
                 R ˘ ⊑ S ˘ → R ⊑ S 
˘-monotonic-⇒ {_}{_}{R}{S} =
    ⇐-begin
         R ⊑ S
    ⇐⟨ ⊑-trans ˘-idempotent-⊒ ⟩
         (R ˘) ˘ ⊑ S
    ⇐⟨ ˘-universal-⇒ ⟩
         R ˘ ⊑ S ˘ 
    ⇐∎

˘-monotonic-⇐ : {A B : Set} {R S : B ← A} →
                 R ⊑ S → R ˘ ⊑ S ˘ 
˘-monotonic-⇐ {_}{_}{R}{S} =
    ⇐-begin
       R ˘ ⊑ S ˘ 
    ⇐⟨ ˘-universal-⇐ ⟩
       (R ˘) ˘ ⊑ S
    ⇐⟨ ⊑-trans ˘-idempotent-⊑ ⟩
       R ⊑ S
    ⇐∎
     
-- distributivity rules

˘-○-distr-⊒ : ∀ {i j} {A : Set i} {B : Set} {C : Set j} → (R : A ← B) → (S : B ← C) →
        (R ○ S)˘ ⊒ S ˘ ○ R ˘
˘-○-distr-⊒ R S a c  (b , bRa , cSb) = (b , cSb , bRa) 

˘-○-distr-⊑ : ∀ {i j} {A : Set i} {B : Set} {C : Set j} → (R : A ← B) → (S : B ← C) →
        (R ○ S)˘ ⊑ S ˘ ○ R ˘
˘-○-distr-⊑ R S a c (b , cSb , bRa) = (b , bRa , cSb)

˘-○-distr3-⊒ : ∀ {i j} {A : Set i} {B C : Set} {D : Set j} → 
     (R : A ← B) → (S : B ← C) → (T : C ← D) →
        (R ○ S ○ T)˘ ⊒ T ˘ ○ S ˘ ○ R ˘
˘-○-distr3-⊒ R S T a d (c , (b , bRa , bSc) , cTd) = 
     (b , (c , cTd , bSc) , bRa)  

˘-○-distr3-⊑ : ∀ {i j} {A : Set i} {B C : Set} {D : Set j} → 
     {R : A ← B} → {S : B ← C} → {T : C ← D} →
        (R ○ S ○ T)˘ ⊑ T ˘ ○ S ˘ ○ R ˘ 
˘-○-distr3-⊑ {R} {S} {T} a d (b , (c , cTd , bSc) , bRa) = 
     (c , (b , bRa , bSc) , cTd)

˘-⨉-distr-⊑ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l} →
  {R : B ← A} → {S : D ← C} → (R ⨉ S)˘ ⊑ (R ˘ ⨉ S ˘)
˘-⨉-distr-⊑ (b , d) (a , c) (bRa , dSc) = bRa , dSc

˘-⨉-distr-⊒ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l} →
  {R : B ← A} → {S : D ← C} → (R ⨉ S)˘ ⊒ (R ˘ ⨉ S ˘)
˘-⨉-distr-⊒ (b , d) (a , c) (bRa , dSc) = bRa , dSc

