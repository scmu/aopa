------------------------------------------------------------------------
-- Several polymorphic variations of the PreorderReasoning module 
------------------------------------------------------------------------

module AlgebraicReasoning.PolyPreorderReasoning1 where

module UnaryCarrier
     (F : Set -> Set1)
     (_∼_   : {A : Set} → F A → F A → Set) 
     (refl  : {A : Set}{x     : F A} → x ∼ x)
     (trans : {A : Set}{x y z : F A} → x ∼ y → y ∼ z → x ∼ z)
    where

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _∼⟨_⟩_ --  _≈⟨_⟩_
  infix  1 begin_

  private

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

    data _IsRelatedTo_ {A : Set} (x y : F A) : Set where
      relTo : x ∼ y → x IsRelatedTo y

  begin_ : {A : Set} {x y : F A} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _∼⟨_⟩_ :  {A : Set} (x : F A) {y z : F A} → x ∼ y → 
              y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

-- _≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
-- _ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (refl x≈y) y∼z)

-- ≈-byDef : ∀ {x} → x ≈ x
-- ≈-byDef = IsEquivalence₁.refl isEquivalence

  byDef : {A : Set}{x : F A} → x ∼ x
  byDef = refl

  _∎ : {A : Set} (x : F A) → x IsRelatedTo x
  _∎ _ = relTo byDef

-----------------------------

module BinaryCarrier
     (F : Set → Set → Set1)
     (_∼_   : {A B : Set} → F A B → F A B → Set) 
     (refl  : {A B : Set}{x     : F A B} → x ∼ x)
     (trans : {A B : Set}{x y z : F A B} → x ∼ y → y ∼ z → x ∼ z)
    where

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _∼⟨_⟩_ --  _≈⟨_⟩_
  infix  1 begin_

  private

    data _IsRelatedTo_ {A B : Set} (x y : F A B) : Set where
      relTo : x ∼ y → x IsRelatedTo y

  begin_ : {A B : Set} {x y : F A B} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _∼⟨_⟩_ :  {A B : Set} (x : F A B) {y z : F A B} → x ∼ y → 
              y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

  byDef : {A B : Set}{x : F A B} → x ∼ x
  byDef = refl

  _∎ : {A B : Set} (x : F A B) → x IsRelatedTo x
  _∎ _ = relTo byDef

-----------------------------

module BinaryCarrier₁
     (F : Set → Set1 → Set1)
     (_∼_   : {A : Set}{B : Set1} → F A B → F A B → Set1) 
     (refl  : {A : Set}{B : Set1}{x     : F A B} → x ∼ x)
     (trans : {A : Set}{B : Set1}{x y z : F A B} → x ∼ y → y ∼ z → x ∼ z)
    where

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _∼⟨_⟩_ --  _≈⟨_⟩_
  infix  1 begin_

  private

    data _IsRelatedTo_ {A : Set}{B : Set1}(x y : F A B) : Set1 where
      relTo : x ∼ y → x IsRelatedTo y

  begin_ : {A : Set}{B : Set1}{x y : F A B} → x IsRelatedTo y → x ∼ y
  begin relTo x∼y = x∼y

  _∼⟨_⟩_ :  {A : Set}{B : Set1}(x : F A B) {y z : F A B} → x ∼ y → 
              y IsRelatedTo z → x IsRelatedTo z
  _ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

  byDef : {A : Set}{B : Set1}{x : F A B} → x ∼ x
  byDef = refl

  _∎ : {A : Set}{B : Set1}(x : F A B) → x IsRelatedTo x
  _∎ _ = relTo byDef
