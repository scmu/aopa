{-# OPTIONS --universe-polymorphism #-}

module AlgebraicReasoning.MonoPreorderReasoning where
open import Level
open import AlgebraicReasoning.PolyPreorderReasoning as PPR

{-
module Mono 
       {i j : Level}
       (_∼_   : {A : Set i} → A → A → Set j) 
       (refl  : {A : Set i} {x : A} → x ∼ x)
       (trans : {A : Set i} {x y z : A} → x ∼ y → y ∼ z → x ∼ z)
   = PPR.UnaryCarrier {i} {i} {j} (λ A → A) _∼_ refl trans
-}

module Mono
     {i j : Level} {A : Set i}
     (_∼_   : A → A → Set j) 
     (refl  : {x     : A } → x ∼ x)
     (trans : {x y z : A} → x ∼ y → y ∼ z → x ∼ z)
    where

  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _∼⟨_⟩_ --  _≈⟨_⟩_
  infix  1 begin_

  private

    data _IsRelatedTo_ (x y : A) : Set j where
      relTo : x ∼ y → x IsRelatedTo y

  begin_ : {x y : A} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _∼⟨_⟩_ : (x : A) {y z : A} → x ∼ y → 
              y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

  byDef : {x : A} → x ∼ x
  byDef = refl

  _∎ : (x : A) → x IsRelatedTo x
  _∎ _ = relTo byDef

{-
module Sets
     {i : Level} 
     (_∼_   : Set i → Set i → Set i) 
     (refl  : {x     : Set i } → x ∼ x)
     (trans : {x y z : Set i} → x ∼ y → y ∼ z → x ∼ z)
    where

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _∼⟨_⟩_ --  _≈⟨_⟩_
  infix  1 begin_

  private

    data _IsRelatedTo_ (x y : Set i) : Set i where
      relTo : x ∼ y → x IsRelatedTo y

  begin_ : {x y : Set i} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _∼⟨_⟩_ : (x : Set i) {y z : Set i} → x ∼ y → 
              y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

  byDef : {x : Set i} → x ∼ x
  byDef = refl

  _∎ : (x : Set i) → x IsRelatedTo x
  _∎ _ = relTo byDef
-}
