module Examples.Sorting.Spec where

open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary
  using (Setoid;        module Setoid;
         DecSetoid;     module DecSetoid;
         DecTotalOrder; module DecTotalOrder;
         Decidable; Transitive)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.List    using (List; []; _∷_; foldr)

open import Sets using (ℙ; ⊆-refl; ⊇-refl;
                        _≡_; ≡-refl; ≡-sym; ≡-trans; ≡-subst)
open import Relations
open import Relations.Converse
open import Relations.Coreflexive
open import Relations.Function
open import Relations.CompChain

open import Data.List.Utilities using (All)
open import Data.List.Fold 
     using (nil; cons; foldR; idR⊒foldR; foldR-monotonic; corefl-foldR)

open import AlgebraicReasoning.Relations
     using (⊑-begin_; _⊑⟨_⟩_; _⊑∎; 
            ⊒-begin_; _⊒⟨_⟩_; _⊒∎)

-- Values 

-- PJ: Trying to find a simple concept to parameterise the derivation on
-- * It looks like a DecTotalOrder is enough to extract most components
-- * Some lemmas are defined in Value-properties
-- * Still needs cleaning up (but changes not that important for paper)

module Value (Val-decTotalOrder : DecTotalOrder) where
  Val-decSetoid : DecSetoid
  Val-decSetoid = DecTotalOrder.Eq.decSetoid Val-decTotalOrder

  Val-setoid : Setoid
  Val-setoid = DecSetoid.setoid Val-decSetoid

  Val : Set
  Val = Setoid.carrier Val-setoid

  _≤_ : Val → Val → Set
  _≤_ = DecTotalOrder._≤_ Val-decTotalOrder

  _≤?_ : Decidable _≤_
  _≤?_ = DecTotalOrder._≤?_ Val-decTotalOrder

  ≤-trans : Transitive _≤_
  ≤-trans = DecTotalOrder.trans Val-decTotalOrder

import Data.Nat
open Data.Nat using (decTotalOrder)
Val-decTotalOrder : DecTotalOrder
Val-decTotalOrder = decTotalOrder

open Value Val-decTotalOrder public

module Value-properties where

  open Data.Nat using (ℕ; zero; suc; 
                       _<_; z≤n; s≤s; ≤-pred)

  -- some lemmas for _≤_

  ≰-elim : ∀ {m n} → ¬ m ≤ n → n < m
  ≰-elim {zero}   {n}      0≰n       = ⊥-elim (0≰n z≤n)
  ≰-elim {suc k₁} {zero}   1+k₁≰0    = s≤s z≤n
  ≰-elim {suc k₁} {suc k₂} 1+k₁≰1+k₂ =
    s≤s (≰-elim (λ k₁≤k₂ → 1+k₁≰1+k₂ (s≤s k₁≤k₂)))

  <-relax : ∀ {m n} → m < n → m ≤ n
  <-relax {m}      {zero}   ()
  <-relax {zero}   {suc k₂} 0<1+k₂    = z≤n
  <-relax {suc k₁} {suc k₂} 1+k₁<1+k₂ = s≤s (<-relax (≤-pred 1+k₁<1+k₂))

open Value-properties public using (≰-elim; <-relax)


-- bags.

import Examples.Sorting.Bags
open Examples.Sorting.Bags Val-setoid public 
  using (Bag; bCons; bNil; 
          _|≈|_; Bag-decSetoid; |≈|-refl; |≈|-sym;
         |≈|-cong; ≡-|≈|-cong; |≈|-≡-cong;
         prop-bCons-commute; prop-bNil≠bCons)

bagify : List Val → Bag
bagify = foldr bCons bNil

nilUniq : {z : List Val}  →  bagify z ≡ bNil  →  z ≡ []
nilUniq {[]}    _            = ≡-refl
nilUniq {a ∷ x} bcons·z≡bNil 
   with prop-bNil≠bCons (≡-|≈|-cong (λ x → x) (≡-sym bcons·z≡bNil)) 
... | ()

-- permutation

permute : List Val ← List Val
permute = ((fun bagify)˘) ○ fun bagify

permute-˘-idem : permute ˘ ⊑ permute
permute-˘-idem =
   ⊑-begin
       permute ˘
   ⊑⟨ ⊑-refl ⟩
       ((fun bagify)˘ ○ fun bagify)˘
   ⊑⟨ ˘-○-distr-⊑ ((fun bagify)˘) (fun bagify) ⟩
       (fun bagify)˘ ○ ((fun bagify)˘)˘ 
   ⊑⟨ ○-monotonic-r ˘-idempotent-⊑ ⟩
                    (fun bagify)˘ ○ fun bagify
   ⊑⟨ ⊑-refl ⟩
       permute
   ⊑∎

permute-idem : permute ○ permute ⊑ permute
permute-idem = 
   ⊑-begin
      permute ○ permute
   ⊑⟨ ⊑-refl ⟩
      ((fun bagify)˘ ○ fun bagify) ○ (fun bagify)˘ ○ fun bagify
   ⊑⟨ ○-assocr ⟩
      (fun bagify)˘ ○ fun bagify ○ (fun bagify)˘ ○ fun bagify
   ⊑⟨ ⇦-mono ((fun bagify)˘ ‥)  (fun bagify ● (fun bagify)˘ ‥)
             (idR  ‥) fun-simple  ⟩
      (fun bagify)˘ ○ idR ○ fun bagify
   ⊑⟨  ○-monotonic-r id-intro-l ⟩
      (fun bagify)˘ ○ fun bagify
   ⊑⟨ ⊑-refl ⟩
      permute
   ⊑∎
 
-- ordered?

lbound : ℙ (Val × List Val)
lbound (a , xs) = All (λ b → a ≤ b) xs
-- lbound (a , []   ) = ⊤
-- lbound (a , b ∷ x) = (a ≤ b) × lbound (a , x)

ordered? : List Val ← List Val
ordered? = foldR (cons ○ (lbound ¿)) nil

ordered?⊑idR : ordered? ⊑ idR
ordered?⊑idR = corefl-foldR (set-corefl⊑idR lbound) ⊆-refl

sort : List Val ← List Val
sort = ordered? ○ permute
