module Data.Generic where

open import Sets
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; id)
open import Level renaming (_⊔_ to _⊔ℓ_)

open import Relations

-- Polynomial bifunctors

data PolyF : Set where
  zer : PolyF 
  one  : PolyF
  arg₁ : PolyF
  arg₂ : PolyF
  _⊕_ : PolyF → PolyF → PolyF
  _⊗_ : PolyF → PolyF → PolyF
  fix : PolyF → PolyF

data Zero {i} : Set i where

data One {i} : Set i where
  tt : One

data Fst {i j} (A : Set i) : Set (i ⊔ℓ j) where
  fst : A → Fst {i} {j} A

data Snd {i j} (X : Set j) : Set (i ⊔ℓ j) where
  snd : X → Snd {i} {j} X

mutual

 ⟦_⟧ : PolyF → ∀{i j} → (A : Set i) (X : Set j) → Set (i ⊔ℓ j)
 ⟦ zer ⟧ A X = Zero
 ⟦ one ⟧ A X = One
 ⟦ arg₁ ⟧ {i} {j} A X = Fst {i} {j} A
 ⟦ arg₂ ⟧ {i} {j} A X = Snd {i} {j} X
 ⟦ l ⊕ r ⟧ A X = ⟦ l ⟧ A X ⊎ ⟦ r ⟧ A X
 ⟦ l ⊗ r ⟧ A X = ⟦ l ⟧ A X × ⟦ r ⟧ A X
 ⟦ fix F ⟧ {i} {j} A X = Snd {i} {j} (μ F X)

 data μ (F : PolyF) {i} (A : Set i) : Set i where
   In : ⟦ F ⟧ A (μ F A) → μ F A


mutual 
  fold : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
       → (⟦ F ⟧ A B → B) → μ F A → B
  fold F f (In xs) = f (bimapFold F F f xs)

  -- bimapFold F F f = bimap F id (fold F f) 
  bimapFold : (F G : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
          → (⟦ F ⟧ A B → B) → ⟦ G ⟧ A (μ F A) → ⟦ G ⟧ A B
  bimapFold F zer f ()
  bimapFold F one f tt = tt
  bimapFold F arg₁ f (fst a) = fst a
  bimapFold F arg₂ f (snd x) = snd (fold F f x)
  bimapFold F (G₁ ⊕ G₂) f (inj₁ x) = inj₁ (bimapFold F G₁ f x)
  bimapFold F (G₁ ⊕ G₂) f (inj₂ y) = inj₂ (bimapFold F G₂ f y)
  bimapFold F (G₁ ⊗ G₂) f (x , y) = bimapFold F G₁ f x , bimapFold F G₂ f y
  bimapFold F (fix G) f (snd (In xs)) = snd {!!}
    -- (map G (fold F f) xs)

  map : ∀ {i j} {A : Set i} {B : Set j} →
      ∀ F → (A → B) → μ F A → μ F B
  map F f = fold F (In ∘ bimap F f id)

  bimap : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set j} {B₁ : Set k} {B₂ : Set l}
        → (A₁ → A₂) → (B₁ → B₂) → ⟦ F ⟧ A₁ B₁ → ⟦ F ⟧ A₂ B₂
  bimap zer f g ()
  bimap one f g tt = tt
  bimap arg₁ f g (fst a) = fst (f a)
  bimap arg₂ f g (snd b) = snd (g b)
  bimap (F₁ ⊕ F₂) f g (inj₁ x) = inj₁ (bimap F₁ f g x)
  bimap (F₁ ⊕ F₂) f g (inj₂ y) = inj₂ (bimap F₂ f g y)
  bimap (F₁ ⊗ F₂) f g (x , y) = bimap F₁ f g x , bimap F₂ f g y
  bimap (fix F) f g (snd xs) = snd (map F g xs)

{-
mutual

 fold-universal : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
                → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B)
                → (∀ xs → h (In xs) ≡ f (bimap F id h xs))
                → (∀ xs → h xs ≡ fold F f xs)
 fold-universal F h f hom (In xs) 
   rewrite hom xs = cong f (mapFold-univ F F h f hom xs)

 mapFold-univ : (F G : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
               → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B) 
               → (∀ xs → h (In xs) ≡ f (bimap F id h xs))
               → (Gxs : ⟦ G ⟧ A (μ F A)) 
               → bimap G id h Gxs ≡ mapFold F G f Gxs
 mapFold-univ F zer h f hom ()
 mapFold-univ F one h f hom tt = refl
 mapFold-univ F arg₁ h f hom (fst a) = refl
 mapFold-univ F arg₂ h f hom (snd xs) = cong snd (fold-universal F h f hom xs)
 mapFold-univ F (G₁ ⊕ G₂) h f hom (inj₁ x) = cong inj₁ (mapFold-univ F G₁ h f hom x)
 mapFold-univ F (G₁ ⊕ G₂) h f hom (inj₂ y) = cong inj₂ (mapFold-univ F G₂ h f hom y)
 mapFold-univ F (G₁ ⊗ G₂) h f hom (x , y) 
   rewrite mapFold-univ F G₁ h f hom x | mapFold-univ F G₂ h f hom y = refl
 mapFold-univ F (fix G) h f hom (snd xs) = ?
-}
-- relational fold
{-
bimapR : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set j} {B₁ : Set k} {B₂ : Set l}
        → (A₂ ← A₁) → (B₂ ← B₁) → (⟦ F ⟧ A₂ B₂ ← ⟦ F ⟧ A₁ B₁)
bimapR zer R S () _
bimapR one R S tt tt = ⊤
bimapR arg₁ R S (fst a₁) (fst a₂) = R a₁ a₂
bimapR arg₂ R S (snd b₁) (snd b₂) = S b₁ b₂
bimapR (F₁ ⊕ F₂) R S (inj₁ x₁) (inj₁ x₂) = bimapR F₁ R S x₁ x₂
bimapR (F₁ ⊕ F₂) R S (inj₁ x₁) (inj₂ y₂) = ⊥
bimapR (F₁ ⊕ F₂) R S (inj₂ y₁) (inj₁ x₂) = ⊥
bimapR (F₁ ⊕ F₂) R S (inj₂ y₁) (inj₂ y₂) = bimapR F₂ R S y₁ y₂
bimapR (F₁ ⊗ F₂) R S (x₁ , y₁) (x₂ , y₂) = bimapR F₁ R S x₁ x₂ × bimapR F₂ R S y₁ y₂

foldR : (F : PolyF) → {A B : Set} → (B ← ⟦ F ⟧ A B) → (B ← μ F A)
foldR F R = ∈ ₁∘ fold F (Λ (R ○ bimapR F idR ∈))
  -}