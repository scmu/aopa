module Relations.WellFound where

{-

Accessibility and well-foundedness. This is a specialised version
of that in Logic.Induction.WellFounded.

Apart from being a bit streamlined, another reason we define our
own for AoPA is that we made this decision that in R x y, x is
the input while y is the output. The reason is that y could in
general depend on x (although it has not happen yet). However,
that means the "smaller" side of R is opposite to that assumed
by Logic.Induction.WellFounded.

-}
open import Data.Product
open import Data.Nat
open import Sets --  using  (_≡_; ≡-refl; ...)
open import Relations
open import Relations.MonoFactor

-- Recall the Monotype Factor
{-
_⍀_ : {A B : Set} → B ← A → ℙ B → ℙ A
(R ⍀ P) a = ∀ b → R b a → P b
-}

-- Accessibility

data Acc {A : Set}(R : A → A → Set) : A → Set where
  acc : (x : A) → (∀ y → R y x → Acc R y) → Acc R x
--  acc : (R ⍀ Acc R) ⊆ Acc R

private
  acc-elim : {a : Set} (R : a → a → Set) {P : a → Set} →
    ((x : a) → (∀ y → R y x → Acc R y) →
                   (∀ y → R y x → P y) → P x) →
       (x : a) → Acc R x → P x
  acc-elim R f x (acc .x h) =
     f x h (λ y yRx → acc-elim R f y (h y yRx)) 

-- The fold induced from Acc.

acc-fold : {a : Set} (R : a → a → Set) {P : a → Set} →
  ((x : a) → (∀ y → R y x → P y) → P x) →
     (x : a) → Acc R x → P x
acc-fold R f x (acc .x h) = f x (λ y yRx → acc-fold R f y (h y yRx))

{- Another type of acc-fold

  acc-fold : {a : Set} (R : a → a → Set) {P : a → Set}
          → R ⍀ P ⊆ P
          → Acc R ⊆ P
-}

{-
The auxiliary function g in acc-fold could be written inline
like this:

  acc-fold : {a : Set} (R : a → a → Set) {P : a → Set} →
    ((x : a) → (∀ y → R x y → P y) → P x) →
       (x : a) → (accx : Acc R x) → P x
  acc-fold R {P} f x (acc .x h) = f x (λ y yRx → acc-fold R f y (h y yRx)) 

However, this version is too strict on accx. As a result,
when I tried to prove foldR-to-unfoldr in Unfold.agda, 
acc-fold cannot be expended after "with f b."

Currently, however, Agda gives me a type error when 
I tried to do "with f b" in foldR-to-unfoldr. See Unfold.agda.

-}

-- A relation is well-founded if every element in a is
-- accessible.

well-found : {a : Set} → (a → a → Set) → Set
well-found R = ∀ x → Acc R x

-- rec-wf behaves like a fixed-point operator.

rec-wf : {a : Set} {R : a → a → Set} {P : a → Set} →
   well-found R →
      ((x : a) → ((y : a) → R y x → P y) → P x) → 
         (x : a) → P x
rec-wf {a}{R} wf f x = acc-fold R f x (wf x) 

-- The relation >' on natural numbers is well-founded.

ℕ<-wf : well-found _<′_
ℕ<-wf n = acc n (access n)
  where access : (n : ℕ) → (m : ℕ) → m <′ n → Acc _<′_ m
        access zero m () 
        access (suc n) .n ≤′-refl      = acc n (access n)
        access (suc n) m (≤′-step m<n) = access n m m<n 

-- New accessibility from old.

acc-⊑ : {A : Set}{R S : A ← A} →  R ⊑ S  →  Acc S ⊆ Acc R
acc-⊑ {A}{R} R⊑S x (acc .x h) = acc x access  
  where access : (y : A) → R y x → Acc R y
        access y yRx = acc-⊑ R⊑S y (h y (R⊑S y x yRx)) 

acc-fRfº : {A B : Set}{R : A ← A}{f : A → B} →
   (x : A) → Acc (fun f ○ R ○ (fun f)˘) (f x) → Acc R x
acc-fRfº {A}{B}{R}{f} x (acc ._ h) = acc x access 
  where access : (y : A) → R y x → Acc R y
        access y yRx = 
         acc-fRfº y (h (f y) (y , (x , refl , yRx) , refl))

data _⁺ {A : Set}(R : A ← A) : A → A → Set where
  ⁺-base : ∀ {x y} → R x y → (R ⁺) x y
  ⁺-step : ∀ {x z} → Σ A (λ y → (R ⁺) x y × R y z) → (R ⁺) x z 

acc-tc : {A : Set}{R : A ← A} → 
      (x : A) → Acc R x → Acc (R ⁺) x
acc-tc {A}{R} x ac = acc x (access x ac)
  where access : (x : A) → Acc R x → (y : A) → (R ⁺) y x → Acc (R ⁺) y
        access x (acc .x h) y (⁺-base yRx) = acc-tc y (h y yRx)  
        access x (acc .x h) y (⁺-step (z , (yR⁺z , zRx))) = 
           access z (h z zRx) y yR⁺z
