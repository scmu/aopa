------------------------------------------------------------------------
-- Several polymorphic variations of the PreorderReasoning module 
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module AlgebraicReasoning.PolyPreorderReasoning where

open import Level -- renaming (_⊔_ to _⊔l_)

module UnaryCarrier
     {i j k : Level}
     (F : Set i → Set j)
     (_∼_   : {A : Set i} → F A → F A → Set k) 
     (refl  : {A : Set i}{x     : F A} → x ∼ x)
     (trans : {A : Set i}{x y z : F A} → x ∼ y → y ∼ z → x ∼ z)
    where

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _∼⟨_⟩_ --  _≈⟨_⟩_
  infix  1 begin_

  private

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

    data _IsRelatedTo_ {A : Set i} (x y : F A) : Set k where
      relTo : x ∼ y → x IsRelatedTo y

  begin_ : {A : Set i} {x y : F A} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _∼⟨_⟩_ :  {A : Set i} (x : F A) {y z : F A} → x ∼ y → 
              y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

-- _≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
-- _ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (refl x≈y) y∼z)

-- ≈-byDef : ∀ {x} → x ≈ x
-- ≈-byDef = IsEquivalence₁.refl isEquivalence

  byDef : {A : Set i}{x : F A} → x ∼ x
  byDef = refl

  _∎ : {A : Set i} (x : F A) → x IsRelatedTo x
  _∎ _ = relTo byDef

-----------------------------

module BinaryCarrier
     {i j k l : Level}
     (F : Set i → Set j → Set k)
     (_∼_   : {A : Set i} {B : Set j} → F A B → F A B → Set l) 
     (refl  : {A : Set i} {B : Set j} {x     : F A B} → x ∼ x)
     (trans : {A : Set i} {B : Set j} {x y z : F A B} → x ∼ y → y ∼ z → x ∼ z)
    where

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _∼⟨_⟩_ --  _≈⟨_⟩_
  infix  1 begin_

  private

    data _IsRelatedTo_ {A : Set i} {B : Set j} (x y : F A B) : Set l where
      relTo : x ∼ y → x IsRelatedTo y

  begin_ : {A : Set i} {B : Set j} {x y : F A B} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _∼⟨_⟩_ :  {A : Set i} {B : Set j} (x : F A B) {y z : F A B} → x ∼ y → 
              y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

  byDef : {A : Set i} {B : Set j} {x : F A B} → x ∼ x
  byDef = refl

  _∎ : {A : Set i} {B : Set j} (x : F A B) → x IsRelatedTo x
  _∎ _ = relTo byDef
