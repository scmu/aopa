module FixedPoint where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relation.Binary
open import Data.Product

open import AlgebraicReasoning.Implications

 -- least prefixed-point.

XFix : ∀ {i j} {A : Set i}
         → (_≼_ : A → A → Set j)
         → (f : A → A) → (μf : A)
         → Set j
XFix _≼_ f x = f x ≼ x

       
LPFP : ∀ {i j} {A : Set i}
       → (_≼_ : A → A → Set j)
       → (f : A → A) → (μf : A)
       → Set (i ⊔ℓ j)
LPFP _≼_ f μf = XFix _≼_ f μf ×
                (∀ {x} → XFix _≼_ f x → μf ≼ x)

 -- least fixed-point.

LFP : ∀ {i j} {A : Set i}
       → (_≈_ _≼_ : A → A → Set j)
       → (f : A → A) → (μf : A)
       → Set (i ⊔ℓ j)
LFP _≈_ _≼_ f μf = XFix _≈_ f μf ×
                   (∀ {x} → XFix _≈_ f x → μf ≼ x) 

least-≽ : ∀ {i j} {A : Set i}
           → (_≼_ : A → A → Set j)
           → (f : A → A) → (∀ {x y} → x ≼ y → f x ≼ f y)
           → (μf : A)
           → LPFP _≼_ f μf → μf ≼ f μf
least-≽ _≼_ f f-mono μf (fμf≼μf , least) =
  (⇐-begin
     μf ≼ f μf
   ⇐⟨ least ⟩
     f (f μf) ≼ f μf
   ⇐⟨ f-mono ⟩
     f μf ≼ μf
   ⇐∎) fμf≼μf

least-least : ∀ {i j} {A : Set i}
              → (_≈_ _≼_ : A → A → Set j)
              → (∀ {x y} → x ≈ y → x ≼ y)  
              → (f : A → A) 
              → (μf : A)
              → LPFP _≼_ f μf → (∀ {x} → XFix _≈_ f x → μf ≼ x)
least-least _≈_ _≼_ ≼-refl f μf (fμf≼μf , least) fx≈x = least (≼-refl fx≈x)

lpfp⇒lfp : ∀ {i j} {A : Set i}
           → (_≈_ _≼_ : A → A → Set j)
           → IsPartialOrder _≈_ _≼_
           → (f : A → A) → (∀ {x y} → x ≼ y → f x ≼ f y)
           → (μf : A)
           → LPFP _≼_ f μf → LFP _≈_ _≼_ f μf
lpfp⇒lfp _≈_ _≼_ partial f f-mono μf (fμf≼μf , least) =
     antisym fμf≼μf (least-≽ _≼_ f f-mono μf (fμf≼μf , least)) ,
     least-least _≈_ _≼_ reflexive f μf (fμf≼μf , least)
  where open IsPartialOrder partial
