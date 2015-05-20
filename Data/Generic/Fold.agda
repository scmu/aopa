module Data.Generic.Fold where

open import Function using (_∘_; id)
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import Level renaming (_⊔_ to _⊔ℓ_)

open import Relations
open import Relations.CompChain
open import AlgebraicReasoning.ExtensionalEquality 
            using (_≐_; ≐-refl; ≐-sym; ≐-trans; ≐-trans'; 
                   pre-∘-cong; post-∘-cong)
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations

open import Data.Generic.Core


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

{-
  Universal property of fold:
    h ≐ fold F f  ≡  h ∘ In ≐ f ∘ bimap F id h
  We split it into two directions: fold-universal-⇐ and fold-universal-⇒.
-}

mutual

 fold-universal-⇐ : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
                → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B)
                → (h ∘ In ≐ f ∘ bimap F id h)
                → (h ≐ fold F f)
 fold-universal-⇐ F h f hom (In xs) 
   rewrite hom xs = cong f (mapFold-univ-⇐ F F h f hom xs)

 mapFold-univ-⇐ : (F G : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
               → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B) 
               → (h ∘ In ≐ f ∘ bimap F id h)
               → bimap G id h ≐ mapFold F G f
 mapFold-univ-⇐ F zer h f hom ()
 mapFold-univ-⇐ F one h f hom tt = refl
 mapFold-univ-⇐ F arg₁ h f hom (fst a) = refl
 mapFold-univ-⇐ F arg₂ h f hom (snd xs) = cong snd (fold-universal-⇐ F h f hom xs)
 mapFold-univ-⇐ F (G₁ ⊕ G₂) h f hom (inj₁ x) = cong inj₁ (mapFold-univ-⇐ F G₁ h f hom x)
 mapFold-univ-⇐ F (G₁ ⊕ G₂) h f hom (inj₂ y) = cong inj₂ (mapFold-univ-⇐ F G₂ h f hom y)
 mapFold-univ-⇐ F (G₁ ⊗ G₂) h f hom (x , y) 
   rewrite mapFold-univ-⇐ F G₁ h f hom x | mapFold-univ-⇐ F G₂ h f hom y = refl

mutual
  fold-universal-⇒ : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j}
                    → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B)
                    → (h ≐ fold F f)
                    → (h ∘ In ≐ f ∘ bimap F id h)
  fold-universal-⇒ F h f hom xs
    rewrite hom (In xs) = cong f (mapFold-univ-⇒ F F h f hom xs)

  mapFold-univ-⇒ : (F G : PolyF) → ∀ {i j} {A : Set i} {B : Set j}
                  → (h : μ F A → B) → (f : ⟦ F ⟧ A B → B)
                  → (h ≐ fold F f)
                  → mapFold F G f ≐ bimap G id h
  mapFold-univ-⇒ F zer h f hom ()
  mapFold-univ-⇒ F one h f hom tt = refl
  mapFold-univ-⇒ F arg₁ h f hom (fst x) = refl
  mapFold-univ-⇒ F arg₂ h f hom (snd y) = cong snd (sym (hom y))
  mapFold-univ-⇒ F (G₁ ⊕ G₂) h f hom (inj₁ x) = cong inj₁ (mapFold-univ-⇒ F G₁ h f hom x)
  mapFold-univ-⇒ F (G₁ ⊕ G₂) h f hom (inj₂ y) = cong inj₂ (mapFold-univ-⇒ F G₂ h f hom y)
  mapFold-univ-⇒ F (G₁ ⊗ G₂) h f hom (x , y)
    rewrite mapFold-univ-⇒ F G₁ h f hom x | mapFold-univ-⇒ F G₂ h f hom y = refl

fold-computation : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
                 → (f : ⟦ F ⟧ A B → B)
                 → (fold F f ∘ In ≐ f ∘ bimap F id (fold F f))
fold-computation F f = fold-universal-⇒ F (fold F f) f ≐-refl

fold-fusion : (F : PolyF) → ∀ {i j} {A : Set i} {B C : Set j}
             → (h : B → C) → (f : ⟦ F ⟧ A B → B) → (g : ⟦ F ⟧ A C → C)
             → (h ∘ f ≐ g ∘ bimap F id h)
             → (h ∘ fold F f ≐ fold F g)
fold-fusion F h f g hom = 
   (⇐-begin 
      h ∘ fold F f ≐ fold F g
    ⇐⟨ fold-universal-⇐ F (h ∘ fold F f) g ⟩ 
      h ∘ fold F f ∘ In ≐ g ∘ bimap F id (h ∘ fold F f)
    ⇐⟨ ≐-trans (pre-∘-cong h (fold-computation F f)) ⟩ 
      h ∘ f ∘ bimap F id (fold F f) ≐ g ∘ bimap F id (h ∘ fold F f) 
    ⇐⟨ ≐-trans' (pre-∘-cong g (≐-sym (bimap-comp F id h id (fold F f)))) ⟩ 
      h ∘ f ∘ bimap F id (fold F f) ≐ g ∘ bimap F id h ∘ bimap F id (fold F f)
    ⇐⟨ post-∘-cong (bimap F id (fold F f)) ⟩ 
      h ∘ f ≐ g ∘ bimap F id h ⇐∎) hom

{-
  In the fold-fusion theorem proved above B and C must have the
  same level due to the restriction of AlgebraicReasoning.Implications.

  AlgebraicReasoning modules currently demands that all the 
  related components have the same type (or the same level, if they are Sets).

  If {A : Set i} {B : Set j} {C : Set k}, 
   h ∘ fold F f ≐ fold F g  :  Set (k ⊔ℓ i)  (and all the equations except the last one)
       since both sides have type μ F A → C, while
   h ∘ f ≐ g ∘ bimap F id h  :  Set (k ⊔ℓ (j ⊔ℓ i))
       since both side have type  ⟦ F ⟧ A B → C
  
  We temporarily sidestep the problem by letting {B C : Set j}.
-}

{- A direct, and more general proof. -}

fold-fusion' : (F : PolyF) → ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
             → (h : B → C) → (f : ⟦ F ⟧ A B → B) → (g : ⟦ F ⟧ A C → C)
             → (h ∘ f ≐ g ∘ bimap F id h)
             → (h ∘ fold F f ≐ fold F g)

fold-fusion' F h f g hom = fold-universal-⇐ F (h ∘ fold F f) g hom'
  where
    hom' : ∀ xs → h (fold F f (In xs)) ≡ g (bimap F id (h ∘ fold F f) xs)
    hom' xs rewrite fold-universal-⇒ F (fold F f) f (λ _ → refl) xs | 
                    bimap-comp F id h id (fold F f) xs = hom (bimap F id (fold F f) xs)



mutual

  foldR : (F : PolyF) → ∀ {A B : Set}
                        → (B ← ⟦ F ⟧ A B ⊣ zero) → (B ← μ F A)
  foldR F R y (In xs) = ∃ (λ ys → mapFoldR F F R ys xs × R y ys)
                        -- (R ○ mapFoldR F F R) y xs expanded

  mapFoldR : (F G : PolyF) → ∀ {A B : Set}
             → (B ← ⟦ F ⟧ A B) → (⟦ G ⟧ A B ← ⟦ G ⟧ A (μ F A) ⊣ zero)
  mapFoldR F zer R y ()
  mapFoldR F one R tt tt = ⊤  -- ⊤ : Set. Thus A has to be a Set.
  mapFoldR F arg₁ R (fst x₀) (fst x₁) = x₀ ≡ x₁
  mapFoldR F arg₂ R (snd x₀) (snd xs) = foldR F R x₀ xs -- foldR F R x₀ xs
  mapFoldR F (G₀ ⊕ G₁) R (inj₁ x₀) (inj₁ x₁) = mapFoldR F G₀ R x₀ x₁
  mapFoldR F (G₀ ⊕ G₁) R (inj₁ x₀) (inj₂ x₁) = ⊥
  mapFoldR F (G₀ ⊕ G₁) R (inj₂ x₀) (inj₁ x₁) = ⊥
  mapFoldR F (G₀ ⊕ G₁) R (inj₂ x₀) (inj₂ x₁) = mapFoldR F G₁ R x₀ x₁
  mapFoldR F (G₀ ⊗ G₁) R (x₀ , y₀) (x₁ , y₁) = mapFoldR F G₀ R x₀ x₁ × mapFoldR F G₁ R y₀ y₁

-- Alternative notations... for those who loves the banana brackets!

⦇_⦈ : {F : PolyF} → ∀ {A B : Set}
   → (B ← ⟦ F ⟧ A B ⊣ zero) → (B ← μ F A)
⦇ R ⦈ = foldR _ R

⦇_∣_⦈ : (F : PolyF) → ∀ {A B : Set}
   → (B ← ⟦ F ⟧ A B ⊣ zero) → (B ← μ F A)
⦇ F ∣ R ⦈ = foldR F R

-- Be explicit that mapFoldR F G R is just fmapR G (foldR F R).

mapFold-bimap-⊑ : (F G : PolyF) → {A B : Set}
                → (R : B ← ⟦ F ⟧ A B)
                → mapFoldR F G R ⊑ fmapR G (foldR F R) 
mapFold-bimap-⊑ F zer R () () mF
mapFold-bimap-⊑ F one R tt tt mF = Data.Unit.tt
mapFold-bimap-⊑ F arg₁ R (fst x) (fst ._) refl = refl
mapFold-bimap-⊑ F arg₂ R (snd ys) (snd xs) mF = mF
mapFold-bimap-⊑ F (G₀ ⊕ G₁) R (inj₁ y) (inj₁ x) mF = mapFold-bimap-⊑ F G₀ R y x mF
mapFold-bimap-⊑ F (G₀ ⊕ G₁) R (inj₁ y) (inj₂ x) ()
mapFold-bimap-⊑ F (G₀ ⊕ G₁) R (inj₂ y) (inj₁ x) ()
mapFold-bimap-⊑ F (G₀ ⊕ G₁) R (inj₂ y) (inj₂ x) mF = mapFold-bimap-⊑ F G₁ R y x mF
mapFold-bimap-⊑ F (G₀ ⊗ G₁) R (x₀ , y₀) (x₁ , y₁) (mF₀ , mF₁) = 
   mapFold-bimap-⊑ F G₀ R x₀ x₁ mF₀ ,
   mapFold-bimap-⊑ F G₁ R y₀ y₁ mF₁

mapFold-bimap-⊒ : (F G : PolyF) → {A B : Set}
                → (R : B ← ⟦ F ⟧ A B)
                → mapFoldR F G R ⊒ fmapR G ⦇ R ⦈ 
mapFold-bimap-⊒ F zer R () () bm
mapFold-bimap-⊒ F one R tt tt bm = Data.Unit.tt
mapFold-bimap-⊒ F arg₁ R (fst x) (fst ._) refl = refl
mapFold-bimap-⊒ F arg₂ R (snd ys) (snd xs) bm = bm
mapFold-bimap-⊒ F (G₀ ⊕ G₁) R (inj₁ y) (inj₁ x) bm = mapFold-bimap-⊒ F G₀ R y x bm
mapFold-bimap-⊒ F (G₀ ⊕ G₁) R (inj₁ y) (inj₂ x) ()
mapFold-bimap-⊒ F (G₀ ⊕ G₁) R (inj₂ y) (inj₁ x) ()
mapFold-bimap-⊒ F (G₀ ⊕ G₁) R (inj₂ y) (inj₂ x) bm = mapFold-bimap-⊒ F G₁ R y x bm
mapFold-bimap-⊒ F (G₀ ⊗ G₁) R (x₀ , y₀) (x₁ , y₁) (bm₀ , bm₁) = 
   mapFold-bimap-⊒ F G₀ R x₀ x₁ bm₀ ,
   mapFold-bimap-⊒ F G₁ R y₀ y₁ bm₁

mapFold-bimap : (F G : PolyF) → {A B : Set}
              → (R : B ← ⟦ F ⟧ A B)
              → mapFoldR F G R ≑ fmapR G ⦇ R ⦈
mapFold-bimap F G R = (mapFold-bimap-⊑ F G R) , (mapFold-bimap-⊒ F G R)

-- computation rules:
--  foldR F R ○ fun In ≑ R ○ bimapR F idR (foldR F R)

foldR-computation'-⊑ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → ⦇ R ⦈ ○ fun In ⊑ R ○ mapFoldR F F R
foldR-computation'-⊑ F R b xs (._ , refl , p) = p

foldR-computation'-⊒ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → ⦇ R ⦈ ○ fun In ⊒ R ○ mapFoldR F F R
foldR-computation'-⊒ F R b xs p = In xs , refl , p

foldR-computation-⊑ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → (⦇ R ⦈ ○ fun In ⊑ R ○ bimapR F idR ⦇ R ⦈)
foldR-computation-⊑ F R = 
  ⊑-begin 
    foldR F R ○ fun In
  ⊑⟨ foldR-computation'-⊑ F R ⟩ 
    R ○ mapFoldR F F R 
  ⊑⟨ ○-monotonic-r (mapFold-bimap-⊑ F F R) ⟩ 
    R ○ bimapR F idR (foldR F R) 
  ⊑∎

foldR-computation-⊒ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → (⦇ R ⦈ ○ fun In ⊒ R ○ fmapR F ⦇ R ⦈)
foldR-computation-⊒ F R = 
  ⊒-begin 
    ⦇ R ⦈ ○ fun In
  ⊒⟨ foldR-computation'-⊒ F R ⟩ 
    R ○ mapFoldR F F R 
  ⊒⟨ ○-monotonic-r (mapFold-bimap-⊒ F F R) ⟩ 
    R ○ fmapR F ⦇ R ⦈
  ⊒∎

foldR-computation : (F : PolyF) → {A B : Set}
                  → (R : B ← ⟦ F ⟧ A B)
                  → (⦇ R ⦈ ○ fun In ≑ R ○ fmapR F ⦇ R ⦈)
foldR-computation F R = foldR-computation-⊑ F R , foldR-computation-⊒ F R

-- The Eilenberg-Wright lemma.

mutual

  Eilenberg-Wright-⊑ : ∀ (F : PolyF) → {A B : Set} → (R : B ← ⟦ F ⟧ A B) 
                       → ⦇ R ⦈ ⊑ ∈ ₁∘ fold F (Λ (R ○ fmapR F ∈))
  Eilenberg-Wright-⊑ F R b (In xs) (ys , mF , bRys) = 
    ys , mapFold-bimapΛ-⊑ F F R ys xs mF , bRys

  mapFold-bimapΛ-⊑ : (F G : PolyF) → {A B : Set}
                    → (R : B ← ⟦ F ⟧ A B) →
                    ∀ ys xs 
                    → mapFoldR F G R ys xs
                    → fmapR G ∈ ys (mapFold F G (Λ (R ○ fmapR F ∈)) xs)
  mapFold-bimapΛ-⊑ F zer R () () mF
  mapFold-bimapΛ-⊑ F one R tt tt mF = Data.Unit.tt
  mapFold-bimapΛ-⊑ F arg₁ R (fst x) (fst ._) refl = refl
  mapFold-bimapΛ-⊑ F arg₂ R (snd b) (snd xs) mF = Eilenberg-Wright-⊑ F R b xs mF
  mapFold-bimapΛ-⊑ F (G₀ ⊕ G₁) R (inj₁ x₀) (inj₁ x₁) mF = 
     mapFold-bimapΛ-⊑ F G₀ R x₀ x₁ mF
  mapFold-bimapΛ-⊑ F (G₀ ⊕ G₁) R (inj₁ _) (inj₂ _) ()
  mapFold-bimapΛ-⊑ F (G₀ ⊕ G₁) R (inj₂ _) (inj₁ _) ()
  mapFold-bimapΛ-⊑ F (G₀ ⊕ G₁) R (inj₂ y₀) (inj₂ y₁) mF = mapFold-bimapΛ-⊑ F G₁ R y₀ y₁ mF
  mapFold-bimapΛ-⊑ F (G₀ ⊗ G₁) R (x₀ , y₀) (x₁ , y₁) (mF₀ , mF₁) = 
     mapFold-bimapΛ-⊑ F G₀ R x₀ x₁ mF₀ ,
     mapFold-bimapΛ-⊑ F G₁ R y₀ y₁ mF₁

mutual

  Eilenberg-Wright-⊒ : ∀ (F : PolyF) → {A B : Set} → (R : B ← ⟦ F ⟧ A B) 
                       → ⦇ R ⦈ ⊒ ∈ ₁∘ fold F (Λ (R ○ fmapR F ∈))
  Eilenberg-Wright-⊒ F R b (In xs) (ys , bm , bRys) = 
    ys , mapFold-bimapΛ-⊒ F F R ys xs bm , bRys

  mapFold-bimapΛ-⊒ : (F G : PolyF) → {A B : Set}
                    → (R : B ← ⟦ F ⟧ A B) →
                    ∀ ys xs 
                    → fmapR G ∈ ys (mapFold F G (Λ (R ○ fmapR F ∈)) xs)
                    → mapFoldR F G R ys xs
  mapFold-bimapΛ-⊒ F zer R () () bm 
  mapFold-bimapΛ-⊒ F one R tt tt bm = Data.Unit.tt
  mapFold-bimapΛ-⊒ F arg₁ R (fst x) (fst ._) refl = refl
  mapFold-bimapΛ-⊒ F arg₂ R (snd b) (snd xs) bm = 
    Eilenberg-Wright-⊒ F R b xs bm
  mapFold-bimapΛ-⊒ F (G₀ ⊕ G₁) R (inj₁ x₀) (inj₁ x₁) bm = 
     mapFold-bimapΛ-⊒ F G₀ R x₀ x₁ bm
  mapFold-bimapΛ-⊒ F (G₀ ⊕ G₁) R (inj₁ _) (inj₂ _) ()
  mapFold-bimapΛ-⊒ F (G₀ ⊕ G₁) R (inj₂ _) (inj₁ _) ()
  mapFold-bimapΛ-⊒ F (G₀ ⊕ G₁) R (inj₂ y₀) (inj₂ y₁) bm = mapFold-bimapΛ-⊒ F G₁ R y₀ y₁ bm
  mapFold-bimapΛ-⊒ F (G₀ ⊗ G₁) R (x₀ , y₀) (x₁ , y₁) (bm₀ , bm₁) = 
     mapFold-bimapΛ-⊒ F G₀ R x₀ x₁ bm₀ ,
     mapFold-bimapΛ-⊒ F G₁ R y₀ y₁ bm₁

Eilenberg-Wright : ∀ (F : PolyF) → {A B : Set} → (R : B ← ⟦ F ⟧ A B) 
                   → ⦇ R ⦈ ≑ ∈ ₁∘ fold F (Λ (R ○ fmapR F ∈))
Eilenberg-Wright F R = (Eilenberg-Wright-⊑ F R) , (Eilenberg-Wright-⊒ F R)

-- universal properties.

mutual

  foldR-universal-⇐-⊑ : (F : PolyF) → {A B : Set}
                      → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                      → (S ○ fun In ⊑ R ○ fmapR F S)
                      → (S ⊑ ⦇ R ⦈)
  foldR-universal-⇐-⊑ F S R hom b (In xs) bSInxs with 
    hom b xs (_ , refl , bSInxs)
  ... | (ys , ysbFxs , bRys) = ys , mapFoldR-univ-⇐-⊑ F F S R hom ys xs ysbFxs , bRys

  mapFoldR-univ-⇐-⊑ : (F G : PolyF) → {A B : Set}
                    → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                    → (S ○ fun In ⊑ R ○ fmapR F S)
                    → fmapR G S ⊑ mapFoldR F G R
  mapFoldR-univ-⇐-⊑ F zer S R hom () y bm
  mapFoldR-univ-⇐-⊑ F one S R hom tt tt bm = Data.Unit.tt
  mapFoldR-univ-⇐-⊑ F arg₁ S R hom (fst y) (fst .y) refl = refl
  mapFoldR-univ-⇐-⊑ F arg₂ S R hom (snd x) (snd y) bm = 
    foldR-universal-⇐-⊑ F S R hom x y bm
  mapFoldR-univ-⇐-⊑ F (G₀ ⊕ G₁) S R hom (inj₁ x₀) (inj₁ x₁) bm = 
    mapFoldR-univ-⇐-⊑ F G₀ S R hom x₀ x₁ bm
  mapFoldR-univ-⇐-⊑ F (G₀ ⊕ G₁) S R hom (inj₁ x) (inj₂ y) ()
  mapFoldR-univ-⇐-⊑ F (G₀ ⊕ G₁) S R hom (inj₂ y) (inj₁ x) ()
  mapFoldR-univ-⇐-⊑ F (G₀ ⊕ G₁) S R hom (inj₂ y₀) (inj₂ y₁) bm = 
    mapFoldR-univ-⇐-⊑ F G₁ S R hom y₀ y₁ bm
  mapFoldR-univ-⇐-⊑ F (G₀ ⊗ G₁) S R hom (x₀ , y₀) (x₁ , y₁) (bm₀ , bm₁) = 
    mapFoldR-univ-⇐-⊑ F G₀ S R hom x₀ x₁ bm₀ ,
    mapFoldR-univ-⇐-⊑ F G₁ S R hom y₀ y₁ bm₁ 

mutual

  foldR-universal-⇐-⊒ : (F : PolyF) → {A B : Set}
                      → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                      → (R ○ fmapR F S ⊑ S ○ fun In)
                      → (⦇ R ⦈ ⊑ S)
  foldR-universal-⇐-⊒ F S R hom b (In xs) (ys , mF , bRys) with 
    hom b xs (ys , mapFoldR-univ-⇐-⊒ F F S R hom ys xs mF , bRys)
  ...  | (._ , refl , bSxs) = bSxs

  mapFoldR-univ-⇐-⊒ : (F G : PolyF) → {A B : Set}
                    → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                    → (R ○ fmapR F S ⊑ S ○ fun In)
                    → mapFoldR F G R ⊑ fmapR G S
  mapFoldR-univ-⇐-⊒ F zer S R hom () y bm
  mapFoldR-univ-⇐-⊒ F one S R hom tt tt bm = Data.Unit.tt
  mapFoldR-univ-⇐-⊒ F arg₁ S R hom (fst y) (fst .y) refl = refl
  mapFoldR-univ-⇐-⊒ F arg₂ S R hom (snd x) (snd y) bm = 
    foldR-universal-⇐-⊒ F S R hom x y bm
  mapFoldR-univ-⇐-⊒ F (G₀ ⊕ G₁) S R hom (inj₁ x₀) (inj₁ x₁) bm = 
    mapFoldR-univ-⇐-⊒ F G₀ S R hom x₀ x₁ bm
  mapFoldR-univ-⇐-⊒ F (G₀ ⊕ G₁) S R hom (inj₁ x) (inj₂ y) ()
  mapFoldR-univ-⇐-⊒ F (G₀ ⊕ G₁) S R hom (inj₂ y) (inj₁ x) ()
  mapFoldR-univ-⇐-⊒ F (G₀ ⊕ G₁) S R hom (inj₂ y₀) (inj₂ y₁) bm = 
    mapFoldR-univ-⇐-⊒ F G₁ S R hom y₀ y₁ bm
  mapFoldR-univ-⇐-⊒ F (G₀ ⊗ G₁) S R hom (x₀ , y₀) (x₁ , y₁) (bm₀ , bm₁) =
    mapFoldR-univ-⇐-⊒ F G₀ S R hom x₀ x₁ bm₀ ,
    mapFoldR-univ-⇐-⊒ F G₁ S R hom y₀ y₁ bm₁


foldR-monotonic : (F : PolyF) → {A B : Set}
                → (R S : B ← ⟦ F ⟧ A B)
                → R ⊑ S → ⦇ R ⦈ ⊑ ⦇ S ⦈
foldR-monotonic F R S =
  ⇐-begin
    ⦇ R ⦈ ⊑ ⦇ S ⦈
  ⇐⟨ foldR-universal-⇐-⊑ F ⦇ R ⦈ S ⟩
    ⦇ R ⦈ ○ fun In ⊑ S ○ fmapR F ⦇ R ⦈
  ⇐⟨ ⊑-trans (foldR-computation-⊑ F R) ⟩
    R ○ fmapR F ⦇ R ⦈ ⊑ S ○ fmapR F ⦇ R ⦈
  ⇐⟨ ○-monotonic-l ⟩
    R ⊑ S
  ⇐∎

mutual
  idR-foldR-⊑ : (F : PolyF) → ∀ {A} → idR ⊑ foldR F {A} (fun In)
  idR-foldR-⊑ F (In x) (In .x) refl = (_ , (idR-mapFoldR-⊑ F F x x refl) , refl)

  idR-mapFoldR-⊑ : (F G : PolyF) → ∀ {A} → idR ⊑ mapFoldR F G {A} (fun In)
  idR-mapFoldR-⊑ F zer () ._ refl
  idR-mapFoldR-⊑ F one tt .tt refl = Data.Unit.tt
  idR-mapFoldR-⊑ F arg₁ (fst a) (fst .a) refl = refl
  idR-mapFoldR-⊑ F arg₂ (snd x) (snd .x) refl = idR-foldR-⊑ F x x refl
  idR-mapFoldR-⊑ F (G₀ ⊕ G₁) (inj₁ x) (inj₁ .x) refl = idR-mapFoldR-⊑ F G₀ x x refl
  idR-mapFoldR-⊑ F (G₀ ⊕ G₁) (inj₂ y) (inj₂ .y) refl = idR-mapFoldR-⊑ F G₁ y y refl
  idR-mapFoldR-⊑ F (G₀ ⊗ G₁) (x , y) (.x , .y) refl = (idR-mapFoldR-⊑ F G₀ x x refl , idR-mapFoldR-⊑ F G₁ y y refl)

mutual
  idR-foldR-⊒ : (F : PolyF) → ∀ {A} → idR ⊒ foldR F {A} (fun In)
  idR-foldR-⊒ F (In y) (In x) (.y , mf , refl) with idR-mapFoldR-⊒ F F y x mf
  idR-foldR-⊒ F (In x) (In .x) (.x , mf , refl) | refl = refl

  idR-mapFoldR-⊒ : (F G : PolyF) → ∀ {A} → idR ⊒ mapFoldR F G {A} (fun In)
  idR-mapFoldR-⊒ F zer () () _
  idR-mapFoldR-⊒ F one tt tt _ = refl
  idR-mapFoldR-⊒ F arg₁ (fst a) (fst .a) refl = refl
  idR-mapFoldR-⊒ F arg₂ (snd y) (snd x) f with idR-foldR-⊒ F y x f
  idR-mapFoldR-⊒ F arg₂ (snd y) (snd .y) f | refl = refl
  idR-mapFoldR-⊒ F (G₀ ⊕ G₁) (inj₁ y₁) (inj₁ x₁) mf with idR-mapFoldR-⊒ F G₀ y₁ x₁ mf
  idR-mapFoldR-⊒ F (G₀ ⊕ G₁) (inj₁ y₁) (inj₁ .y₁) mf | refl = refl
  idR-mapFoldR-⊒ F (G₀ ⊕ G₁) (inj₁ y₁) (inj₂ x₂) ()
  idR-mapFoldR-⊒ F (G₀ ⊕ G₁) (inj₂ y₂) (inj₁ x₁) ()
  idR-mapFoldR-⊒ F (G₀ ⊕ G₁) (inj₂ y₂) (inj₂ x₂) mf with idR-mapFoldR-⊒ F G₁ y₂ x₂ mf
  idR-mapFoldR-⊒ F (G₀ ⊕ G₁) (inj₂ y₂) (inj₂ .y₂) mf | refl = refl
  idR-mapFoldR-⊒ F (G₀ ⊗ G₁) (y₁ , y₂) (x₁ , x₂) mf with idR-mapFoldR-⊒ F G₀ y₁ x₁ (proj₁ mf) | idR-mapFoldR-⊒ F G₁ y₂ x₂ (proj₂ mf)
  idR-mapFoldR-⊒ F (G₀ ⊗ G₁) (y₁ , y₂) (.y₁ , .y₂) mf | refl | refl = refl


-- Fusion Theorems

foldR-fusion-⊒ : (F : PolyF) → {A B C : Set}
               → (S : C ← B) → (R : B ← ⟦ F ⟧ A B) → (T : C ← ⟦ F ⟧ A C)
               → (S ○ R ⊒ T ○ fmapR F S)
               → (S ○ ⦇ R ⦈ ⊒ ⦇ T ⦈)
foldR-fusion-⊒ F S R T = 
   ⇐-begin
     ⦇ T ⦈ ⊑ S ○ ⦇ R ⦈
   ⇐⟨ foldR-universal-⇐-⊒ F (S ○ ⦇ R ⦈) T ⟩ 
     T ○ fmapR F (S ○ ⦇ R ⦈) ⊑ (S ○ ⦇ R ⦈) ○ fun In
   ⇐⟨ ⊒-trans ○-assocl ⟩
     T ○ fmapR F (S ○ ⦇ R ⦈) ⊑ S ○ ⦇ R ⦈ ○ fun In
   ⇐⟨ ⊒-trans (○-monotonic-r (foldR-computation-⊒ F R)) ⟩ 
     T ○ fmapR F (S ○ ⦇ R ⦈) ⊑ S ○ R ○ fmapR F ⦇ R ⦈
   ⇐⟨ ⊑-trans (○-monotonic-r (bimapR-monotonic-⊑ F id-idempotent-⊒ ⊑-refl)) ⟩ 
     T ○ bimapR F (idR ○ idR) (S ○ ⦇ R ⦈) ⊑ S ○ R ○ fmapR F ⦇ R ⦈
   ⇐⟨ ⊑-trans (○-monotonic-r (bimapR-functor-⊒ F)) ⟩ 
     T ○ fmapR F S ○ fmapR F ⦇ R ⦈ ⊑ S ○ R ○ fmapR F ⦇ R ⦈
   ⇐⟨ ⇦-mono-l (T ● fmapR F S ‥) (S ● R ‥) ⟩ 
     T ○ fmapR F S ⊑ S ○ R 
   ⇐∎

foldR-fusion-⊑ : (F : PolyF) → {A B C : Set}
               → (S : C ← B) → (R : B ← ⟦ F ⟧ A B) → (T : C ← ⟦ F ⟧ A C)
               → (S ○ R ⊑ T ○ fmapR F S)
               → (S ○ ⦇ R ⦈ ⊑ ⦇ T ⦈)
foldR-fusion-⊑ F S R T = 
   ⇐-begin
     S ○ ⦇ R ⦈ ⊑ ⦇ T ⦈ 
   ⇐⟨ foldR-universal-⇐-⊑ F (S ○ ⦇ R ⦈) T ⟩ 
    (S ○ ⦇ R ⦈) ○ fun In ⊑ T ○ fmapR F (S ○ ⦇ R ⦈) 
   ⇐⟨ ⊑-trans ○-assocr ⟩
     S ○ ⦇ R ⦈ ○ fun In ⊑ T ○ fmapR F (S ○ ⦇ R ⦈)  
   ⇐⟨ ⊑-trans (○-monotonic-r (foldR-computation-⊑ F R)) ⟩ 
     S ○ R ○ fmapR F ⦇ R ⦈ ⊑ T ○ fmapR F (S ○ ⦇ R ⦈)  
   ⇐⟨ ⊒-trans (○-monotonic-r (bimapR-monotonic-⊒ F id-idempotent-⊑ ⊒-refl)) ⟩ 
     S ○ R ○ fmapR F ⦇ R ⦈ ⊑ T ○ bimapR F (idR ○ idR) (S ○ ⦇ R ⦈) 
   ⇐⟨ ⊒-trans (○-monotonic-r (bimapR-functor-⊑ F)) ⟩ 
     S ○ R ○ fmapR F ⦇ R ⦈ ⊑ T ○ fmapR F S ○ fmapR F ⦇ R ⦈
   ⇐⟨ ⇦-mono-l (S ● R ‥) (T ● fmapR F S ‥)  ⟩ 
     S ○ R ⊑ T ○ fmapR F S
   ⇐∎

