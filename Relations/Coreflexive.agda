module Relations.Coreflexive where

open import Level
open import Data.Product
open import Sets
open import Relations

-- coreflexives built from sets

_¿ : ∀ {i} {A : Set i} → ℙ A → (A ← A)
(p ¿) b a = (a ≡ b) × p a

set-corefl⊑idR : {A : Set} → (s : ℙ A) → s ¿ ⊑ idR
set-corefl⊑idR s b a (a≡b , bRa) = a≡b

-- coreflexives are idempotent: C ○ C ≑ C

corefl-idempotent-⊒ : ∀ {i} {A : Set i} {C : A ← A} → C ⊑ idR → C ○ C ⊒ C
corefl-idempotent-⊒ C⊑idR x y yCx with C⊑idR x y yCx
corefl-idempotent-⊒ C⊑idR x .x xCx | refl = x , xCx , xCx

corefl-idempotent-⊑ : ∀ {i} {A : Set i} {C : A ← A} → C ⊑ idR → C ○ C ⊑ C
corefl-idempotent-⊑ C⊑idR y x (z , zCx , yCz) with C⊑idR z x zCx | C⊑idR y z yCz
corefl-idempotent-⊑ C⊑idR x .x (.x , xCx , xCx') | refl | refl = xCx

open import Data.List using (List)
open import Data.List.Utilities using (check; corefl-check)
check-idempotent : ∀ {A : Set} → (p : ℙ (A × List A)) → 
                   check (p ¿) ○ check (p ¿) ⊒ check (p ¿)
check-idempotent p = corefl-idempotent-⊒ (corefl-check (set-corefl⊑idR p))

-- Coref as a datatype

Coref : ∀ {i} (A : Set i) → Set (suc i)
Coref A = Σ (A ← A) (λ R → R ⊑ idR)

