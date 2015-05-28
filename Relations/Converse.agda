{-# OPTIONS --universe-polymorphism #-}

module Relations.Converse where

open import Level
open import Data.Product  using (Σ; _×_; _,_)

open import Sets
open import Relations 
open import AlgebraicReasoning.Implications

-- ˘-universal : X ⊑ R ˘  ⇔  X ˘ ⊑ R

˘-universal-⇒  : ∀ {i j k} {A : Set i} {B : Set j} {X : A ← B ⊣ k} {R : B ← A} → 
                 X ⊑ R ˘ → X ˘ ⊑ R
˘-universal-⇒ X⊑R˘ a b aXb = X⊑R˘ b a aXb

˘-universal-⇐ : ∀ {i j k} {A : Set i} {B : Set j} {X : A ← B ⊣ k} {R : B ← A} → 
                  X ˘ ⊑ R → X ⊑ R ˘
˘-universal-⇐ X˘⊑R b a bXa = X˘⊑R a b bXa 

-- id ≑ id˘

id⊑id˘ : {A : Set} → idR {A = A} ⊑ (idR)˘
id⊑id˘ a a' = sym 

id˘⊑id : {A : Set} → (idR {A = A})˘ ⊑ idR
id˘⊑id a a' = sym

id˘≑id : {A : Set} → (idR {A = A})˘ ≑ idR
id˘≑id = id˘⊑id , id⊑id˘


-- C ≑ C˘ if C ⊑ id

C⊑C˘ : {A : Set}{C : A ← A} → C ⊑ idR → C ⊑ C ˘
C⊑C˘ C⊑id a a' aCa' with C⊑id a a' aCa' 
C⊑C˘ C⊑id a .a aCa' | refl = aCa' 

C˘⊑C : {A : Set}{C : A ← A} → C ⊑ idR → C ˘ ⊑ C
C˘⊑C C⊑id a a' a'Ca with C⊑id a' a a'Ca 
C˘⊑C C⊑id a .a a'Ca | refl = a'Ca 

C˘≑C : {A : Set}{C : A ← A} → C ⊑ idR → C ˘ ≑ C
C˘≑C C⊑id = C˘⊑C C⊑id , C⊑C˘ C⊑id

-- ˘-idempotent : R˘˘ ≑ R

˘-idempotent-⊑ : ∀ {i j k} {A : Set i} {B : Set j} → {R : A ← B ⊣ k} → (R ˘) ˘ ⊑ R
˘-idempotent-⊑ = ˘-universal-⇒ ⊑-refl

˘-idempotent-⊒ : ∀ {i j k} {A : Set i} {B : Set j} → {R : A ← B ⊣ k} → R ⊑ (R ˘) ˘
˘-idempotent-⊒ = ˘-universal-⇐ ⊑-refl

˘-idempotent : ∀ {i j k} {A : Set i} {B : Set j} → {R : A ← B ⊣ k} → (R ˘) ˘ ≑ R
˘-idempotent = ˘-idempotent-⊑ , ˘-idempotent-⊒

-- monotonicity: R ˘ ⊑ S ˘ ⇔ R ⊑ S

˘-monotonic-⇒ : ∀ {i j k} {A : Set i} {B : Set j} {R S : B ← A ⊣ k} →
                 R ˘ ⊑ S ˘ → R ⊑ S 
˘-monotonic-⇒ {R = R}{S} =
    ⇐-begin
         R ⊑ S
    ⇐⟨ ⊑-trans ˘-idempotent-⊒ ⟩
         (R ˘) ˘ ⊑ S
    ⇐⟨ ˘-universal-⇒ ⟩
         R ˘ ⊑ S ˘ 
    ⇐∎

˘-monotonic-⇐ : ∀ {i j k} {A : Set i} {B : Set j} {R S : B ← A ⊣ k} →
                 R ⊑ S → R ˘ ⊑ S ˘ 
˘-monotonic-⇐ {R = R}{S} =
    ⇐-begin
       R ˘ ⊑ S ˘ 
    ⇐⟨ ˘-universal-⇐ ⟩
       (R ˘) ˘ ⊑ S
    ⇐⟨ ⊑-trans ˘-idempotent-⊑ ⟩
       R ⊑ S
    ⇐∎
     
-- distributivity rules

˘-○-distr-⊒ : ∀ {i j k l m} {A : Set i} {B : Set j} {C : Set k} → (R : A ← B ⊣ l) → (S : B ← C ⊣ m) →
        (R ○ S)˘ ⊒ S ˘ ○ R ˘
˘-○-distr-⊒ R S a c  (b , bRa , cSb) = (b , cSb , bRa) 

˘-○-distr-⊑ : ∀ {i j k l m} {A : Set i} {B : Set j} {C : Set k} → (R : A ← B ⊣ l) → (S : B ← C ⊣ m) →
        (R ○ S)˘ ⊑ S ˘ ○ R ˘
˘-○-distr-⊑ R S a c (b , cSb , bRa) = (b , bRa , cSb)

˘-○-distr3-⊒ : ∀ {i j k l m n o} {A : Set i} {B : Set j} {C : Set k} {D : Set l} → 
     (R : A ← B ⊣ m) → (S : B ← C ⊣ n) → (T : C ← D ⊣ o) →
        (R ○ S ○ T)˘ ⊒ T ˘ ○ S ˘ ○ R ˘
˘-○-distr3-⊒ R S T a d (c , (b , bRa , bSc) , cTd) = 
     (b , (c , cTd , bSc) , bRa)  

˘-○-distr3-⊑ : ∀ {i j k l m n o} {A : Set i} {B : Set j} {C : Set k} {D : Set l} → 
     {R : A ← B ⊣ m} → {S : B ← C ⊣ n} → {T : C ← D ⊣ o} →
        (R ○ S ○ T)˘ ⊑ T ˘ ○ S ˘ ○ R ˘ 
˘-○-distr3-⊑ {R} {S} {T} a d (b , (c , cTd , bSc) , bRa) = 
     (c , (b , bRa , bSc) , cTd)

˘-⨉-distr-⊑ : ∀ {i j k l m n} {A : Set i} {B : Set j} {C : Set k} {D : Set l} →
  {R : B ← A ⊣ m} → {S : D ← C ⊣ n} → (R ⨉ S)˘ ⊑ (R ˘ ⨉ S ˘)
˘-⨉-distr-⊑ (b , d) (a , c) (bRa , dSc) = bRa , dSc

˘-⨉-distr-⊒ : ∀ {i j k l m n} {A : Set i} {B : Set j} {C : Set k} {D : Set l} →
  {R : B ← A ⊣ m} → {S : D ← C ⊣ n} → (R ⨉ S)˘ ⊒ (R ˘ ⨉ S ˘)
˘-⨉-distr-⊒ (b , d) (a , c) (bRa , dSc) = bRa , dSc

