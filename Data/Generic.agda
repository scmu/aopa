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

data Zero {i} : Set i where

data One {i} : Set i where
  tt : One

data Fst {i j} (A : Set i) : Set (i ⊔ℓ j) where
  fst : A → Fst {i} {j} A

data Snd {i j} (X : Set j) : Set (i ⊔ℓ j) where
  snd : X → Snd {i} {j} X

⟦_⟧ : PolyF → ∀{i j} → (A : Set i) (X : Set j) → Set (i ⊔ℓ j)
⟦ zer ⟧ A X = Zero
⟦ one ⟧ A X = One
⟦ arg₁ ⟧ {i} {j} A X = Fst {i} {j} A
⟦ arg₂ ⟧ {i} {j} A X = Snd {i} {j} X
⟦ l ⊕ r ⟧ A X = ⟦ l ⟧ A X ⊎ ⟦ r ⟧ A X
⟦ l ⊗ r ⟧ A X = ⟦ l ⟧ A X × ⟦ r ⟧ A X

data μ (F : PolyF) {i} (A : Set i) : Set i where
  In : ⟦ F ⟧ A (μ F A) → μ F A

bimap : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set j} {B₁ : Set k} {B₂ : Set l}
        → (A₁ → A₂) → (B₁ → B₂) → ⟦ F ⟧ A₁ B₁ → ⟦ F ⟧ A₂ B₂
bimap zer f g ()
bimap one f g tt = tt
bimap arg₁ f g (fst a) = fst (f a)
bimap arg₂ f g (snd b) = snd (g b)
bimap (F₁ ⊕ F₂) f g (inj₁ x) = inj₁ (bimap F₁ f g x)
bimap (F₁ ⊕ F₂) f g (inj₂ y) = inj₂ (bimap F₂ f g y)
bimap (F₁ ⊗ F₂) f g (x , y) = bimap F₁ f g x , bimap F₂ f g y

bimap-comp : (F : PolyF) → ∀ {i j k l m n} {A₁ : Set i} {A₂ : Set j} {A₃ : Set k} {B₁ : Set l} {B₂ : Set m} {B₃ : Set n}
            → (f : A₂ → A₃) → (g : B₂ → B₃) → (h : A₁ → A₂) → (k : B₁ → B₂)
            → (∀ x → bimap F (f ∘ h) (g ∘ k) x ≡ bimap F f g (bimap F h k x))
bimap-comp zer f g h k ()
bimap-comp one f g h k tt = refl
bimap-comp arg₁ f g h k (fst x) = refl
bimap-comp arg₂ f g h k (snd y) = refl
bimap-comp (F₁ ⊕ F₂) f g h k (inj₁ x) = cong inj₁ (bimap-comp F₁ f g h k x)
bimap-comp (F₁ ⊕ F₂) f g h k (inj₂ y) = cong inj₂ (bimap-comp F₂ f g h k y)
bimap-comp (F₁ ⊗ F₂) f g h k (x , y)
  rewrite bimap-comp F₁ f g h k x | bimap-comp F₂ f g h k y = refl

mutual 
  fold : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
       → (⟦ F ⟧ A B → B) → μ F A → B
  fold F f (In xs) = f (mapFold F F f xs)

  mapFold : (F G : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
          → (⟦ F ⟧ A B → B) → ⟦ G ⟧ A (μ F A) → ⟦ G ⟧ A B
  mapFold F zer f ()
  mapFold F one f tt = tt
  mapFold F arg₁ f (fst a) = fst a
  mapFold F arg₂ f (snd x) = snd (fold F f x)
  mapFold F (G₁ ⊕ G₂) f (inj₁ x) = inj₁ (mapFold F G₁ f x)
  mapFold F (G₁ ⊕ G₂) f (inj₂ y) = inj₂ (mapFold F G₂ f y)
  mapFold F (G₁ ⊗ G₂) f (x , y) = mapFold F G₁ f x , mapFold F G₂ f y

mutual

 fold-universal-l : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
                → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B)
                → (∀ xs → h (In xs) ≡ f (bimap F id h xs))
                → (∀ xs → h xs ≡ fold F f xs)
 fold-universal-l F h f hom (In xs) 
   rewrite hom xs = cong f (mapFold-univ-l F F h f hom xs)

 mapFold-univ-l : (F G : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
               → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B) 
               → (∀ xs → h (In xs) ≡ f (bimap F id h xs))
               → (Gxs : ⟦ G ⟧ A (μ F A)) 
               → bimap G id h Gxs ≡ mapFold F G f Gxs
 mapFold-univ-l F zer h f hom ()
 mapFold-univ-l F one h f hom tt = refl
 mapFold-univ-l F arg₁ h f hom (fst a) = refl
 mapFold-univ-l F arg₂ h f hom (snd xs) = cong snd (fold-universal-l F h f hom xs)
 mapFold-univ-l F (G₁ ⊕ G₂) h f hom (inj₁ x) = cong inj₁ (mapFold-univ-l F G₁ h f hom x)
 mapFold-univ-l F (G₁ ⊕ G₂) h f hom (inj₂ y) = cong inj₂ (mapFold-univ-l F G₂ h f hom y)
 mapFold-univ-l F (G₁ ⊗ G₂) h f hom (x , y) 
   rewrite mapFold-univ-l F G₁ h f hom x | mapFold-univ-l F G₂ h f hom y = refl

mutual
  fold-universal-r : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j}
                    → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B)
                    → (∀ xs → h xs ≡ fold F f xs)
                    → (∀ xs → h (In xs) ≡ f (bimap F id h xs))
  fold-universal-r F h f hom xs
    rewrite hom (In xs) = cong f (mapFold-univ-r F F h f hom xs)

  mapFold-univ-r : (F G : PolyF) → ∀ {i j} {A : Set i} {B : Set j}
                  → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B)
                  → (∀ xs → h xs ≡ fold F f xs)
                  → (Gxs : ⟦ G ⟧ A (μ F A))
                  → mapFold F G f Gxs ≡ bimap G id h Gxs
  mapFold-univ-r F zer h f hom ()
  mapFold-univ-r F one h f hom tt = refl
  mapFold-univ-r F arg₁ h f hom (fst x) = refl
  mapFold-univ-r F arg₂ h f hom (snd y) = cong snd (sym (hom y))
  mapFold-univ-r F (G₁ ⊕ G₂) h f hom (inj₁ x) = cong inj₁ (mapFold-univ-r F G₁ h f hom x)
  mapFold-univ-r F (G₁ ⊕ G₂) h f hom (inj₂ y) = cong inj₂ (mapFold-univ-r F G₂ h f hom y)
  mapFold-univ-r F (G₁ ⊗ G₂) h f hom (x , y)
    rewrite mapFold-univ-r F G₁ h f hom x | mapFold-univ-r F G₂ h f hom y = refl

fold-fusion : (F : PolyF) → ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
             → (h : B → C) → (f : ⟦ F ⟧ A B → B) → (g : ⟦ F ⟧ A C → C)
             → (∀ Fb → h (f Fb) ≡ g (bimap F id h Fb))
             → (∀ xs → h (fold F f xs) ≡ fold F g xs)
fold-fusion F h f g hom = fold-universal-l F (h ∘ fold F f) g hom'
  where
    hom' : ∀ xs → h (fold F f (In xs)) ≡ g (bimap F id (h ∘ fold F f) xs)
    hom' xs
      rewrite fold-universal-r F (fold F f) f (λ _ → refl) xs | bimap-comp F id h id (fold F f) xs = hom (bimap F id (fold F f) xs)

-- relational fold

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
  
