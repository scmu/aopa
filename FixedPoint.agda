module FixedPoint where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relation.Binary
open import Data.Product

open import AlgebraicReasoning.Implications

-- LowerBound P _≼_ lb : lb is a lowerbound for elements
--   satsifying P.

LowerBound : ∀ {i j} {A : Set i}
             → (P : A → Set j)
             → (_≼_ : A → A → Set j)
             → A → Set (i ⊔ℓ j)
LowerBound P _≼_ lb = ∀ {x} → P x → lb ≼ x

-- Least P _≼_ x : x is a least element that satisfies P.

Least : ∀ {i j} {A : Set i}
        → (P : A → Set j)
        → (_≼_ : A → A → Set j)
        → A → Set (i ⊔ℓ j)
Least P _≼_ x = (P x × LowerBound P _≼_ x)

-- Least prefixed-point.
       
PrefixP : ∀ {i j} {A : Set i}
         → (_≼_ : A → A → Set j)
         → (f : A → A) → (μf : A)
         → Set j
PrefixP _≼_ f x = f x ≼ x

LeastPrefixedPoint : ∀ {i j} {A : Set i}
       → (_≼_ : A → A → Set j)
       → (f : A → A) → (μf : A) → Set (i ⊔ℓ j)
LeastPrefixedPoint _≼_ f = Least (PrefixP _≼_ f) _≼_

-- Least fixed-point.

  -- FixP has the same definition as PrefixP. Anyway,
  -- repeated for clarity.

FixP : ∀ {i j} {A : Set i}
       → (_≈_ : A → A → Set j) → (f : A → A) 
       → (μf : A) → Set j
FixP _≈_ f x = f x ≈ x

LeastFixedPoint : ∀ {i j} {A : Set i}
       → (_≈_ _≼_ : A → A → Set j) → (f : A → A) 
       → (μf : A) → Set (i ⊔ℓ j)
LeastFixedPoint _≈_ _≼_ f = Least (FixP _≈_ f) _≼_ 

-- Properties

  -- least fixed-points are unique --- up to _≈_.

lpfp-unique : ∀ {i j} {A : Set i}
              → (_≈_ _≼_ : A → A → Set j)
              → IsPartialOrder _≈_ _≼_
              → (f : A → A) 
              → (μf₁ : A) → LeastPrefixedPoint _≼_ f μf₁
              → (μf₂ : A) → LeastPrefixedPoint _≼_ f μf₂
              → μf₁ ≈ μf₂
lpfp-unique _≈_ _≼_ partial f μf₁ (pfp₁ , lb₁) μf₂ (pfp₂ , lb₂) =
     antisym (lb₁ pfp₂) (lb₂ pfp₁)
    where open IsPartialOrder partial

   -- least fixed-points are also unique up to _≈_, for similar reasons.

lfp-unique : ∀ {i j} {A : Set i}
              → (_≈_ _≼_ : A → A → Set j)
              → IsPartialOrder _≈_ _≼_
              → (f : A → A) 
              → (μf₁ : A) → LeastFixedPoint _≈_ _≼_ f μf₁
              → (μf₂ : A) → LeastFixedPoint _≈_ _≼_ f μf₂
              → μf₁ ≈ μf₂
lfp-unique _≈_ _≼_ partial f μf₁ (fp₁ , lb₁) μf₂ (fp₂ , lb₂) =
     antisym (lb₁ fp₂) (lb₂ fp₁)
    where open IsPartialOrder partial

 -- least prefixed-point μf of a monotonic function f 
 -- satisfies μf ≼ f μf.

lpfp⇒≽ : ∀ {i j} {A : Set i}
         → (_≼_ : A → A → Set j) (f : A → A) 
         → (∀ {x y} → x ≼ y → f x ≼ f y)
         → (μf : A)
         → LeastPrefixedPoint _≼_ f μf → μf ≼ f μf
lpfp⇒≽ _≼_ f f-mono μf (fμf≼μf , least) =
  (⇐-begin
     μf ≼ f μf
   ⇐⟨ least ⟩
     f (f μf) ≼ f μf
   ⇐⟨ f-mono ⟩
     f μf ≼ μf
   ⇐∎) fμf≼μf

 -- least prefixed-point μf of a monotonic function f
 -- is also a fixed point.

lpfp⇒fixp : ∀ {i j} {A : Set i}
            → (_≈_ _≼_ : A → A → Set j)
            → IsPartialOrder _≈_ _≼_
            → (f : A → A) → (∀ {x y} → x ≼ y → f x ≼ f y)
            → (μf : A) 
            → LeastPrefixedPoint _≼_ f μf → FixP _≈_ f μf
lpfp⇒fixp _≈_ _≼_ partial f f-mono μf (fμf≼μf , least) = 
   antisym fμf≼μf (lpfp⇒≽ _≼_ f f-mono μf (fμf≼μf , least))
  where open IsPartialOrder partial

  -- and μf is also a lower bound for fixed points.

lpfp⇒lb : ∀ {i j} {A : Set i}
          → (_≈_ _≼_ : A → A → Set j)
          → IsPartialOrder _≈_ _≼_
          → (f : A → A) 
          → (μf : A)
          → LeastPrefixedPoint _≼_ f μf → LowerBound (FixP _≈_ f) _≼_ μf
lpfp⇒lb _≈_ _≼_ partial f μf (fμf≼μf , least) fx≈x = least (reflexive fx≈x)
    where open IsPartialOrder partial

  -- Thus a least prefixed point is also a least fixed point.

lpfp⇒lfp : ∀ {i j} {A : Set i}
           → (_≈_ _≼_ : A → A → Set j)
           → IsPartialOrder _≈_ _≼_
           → (f : A → A) → (∀ {x y} → x ≼ y → f x ≼ f y)
           → (μf : A)
           → LeastPrefixedPoint _≼_ f μf → LeastFixedPoint _≈_ _≼_ f μf 
lpfp⇒lfp _≈_ _≼_ partial f f-mono μf lpfp =
     lpfp⇒fixp _≈_ _≼_ partial f f-mono μf lpfp ,
     lpfp⇒lb   _≈_ _≼_ partial f μf lpfp

  {- The situation with the other direction is a bit awkward.

     Given a least prefixed-point μf, we cannot prove that it is also
     a least fixed-point. We may only prove that μf equals any
     least fixed point up to _≈_.
  -}

lfp⇒lpfp≈ : ∀ {i j} {A : Set i}
           → (_≈_ _≼_ : A → A → Set j)
           → IsPartialOrder _≈_ _≼_
           → (f : A → A) → (∀ {x y} → x ≼ y → f x ≼ f y)
           → (μf : A) → LeastPrefixedPoint _≼_ f μf
           → (φf : A) → LeastFixedPoint _≈_ _≼_ f φf
           → μf ≈ φf
lfp⇒lpfp≈ _≈_ _≼_ partial f f-mono μf lpfp φf lfp = 
     lfp-unique _≈_ _≼_ partial f μf 
       (lpfp⇒lfp _≈_ _≼_ partial f f-mono μf lpfp) φf lfp
    where open IsPartialOrder partial
