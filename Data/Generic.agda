module Data.Generic where

open import Sets
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Level renaming (_⊔_ to _⊔ℓ_)

open import Relations
open import Relations.Factor
open import Relations.Function
open import Relations.Converse
open import Relations.CompChain
open import FixedPoint
open import AlgebraicReasoning.ExtensionalEquality 
            using (_≐_; ≐-refl; ≐-sym; ≐-trans; ≐-trans'; 
                   pre-∘-cong; post-∘-cong)
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations

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

-- functional fold 

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

-- relational bimap

bimapR : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set j} {B₁ : Set k} {B₂ : Set l}
        → (A₂ ← A₁ ⊣ zero) → (B₂ ← B₁ ⊣ zero) → (⟦ F ⟧ A₂ B₂ ← ⟦ F ⟧ A₁ B₁ ⊣ zero)
bimapR zer R S () _
bimapR one R S tt tt = ⊤  -- available only as Set.
bimapR arg₁ R S (fst a₁) (fst a₂) = R a₁ a₂
bimapR arg₂ R S (snd b₁) (snd b₂) = S b₁ b₂
bimapR (F₁ ⊕ F₂) R S (inj₁ x₁) (inj₁ x₂) = bimapR F₁ R S x₁ x₂
bimapR (F₁ ⊕ F₂) R S (inj₁ x₁) (inj₂ y₂) = ⊥
bimapR (F₁ ⊕ F₂) R S (inj₂ y₁) (inj₁ x₂) = ⊥
bimapR (F₁ ⊕ F₂) R S (inj₂ y₁) (inj₂ y₂) = bimapR F₂ R S y₁ y₂
bimapR (F₁ ⊗ F₂) R S (x₁ , y₁) (x₂ , y₂) = bimapR F₁ R S x₁ x₂ × bimapR F₂ R S y₁ y₂

bimapR-functor-⊑ : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set} {A₃ : Set j} {B₁ : Set k} {B₂ : Set} {B₃ : Set l}
                   {R : A₃ ← A₂} {S : B₃ ← B₂} {T : A₂ ← A₁} {U : B₂ ← B₁}
                  → bimapR F R S ○ bimapR F T U ⊑ bimapR F (R ○ T) (S ○ U)
bimapR-functor-⊑ zer () _ _
bimapR-functor-⊑ one tt tt _ = Data.Unit.tt
bimapR-functor-⊑ arg₁ (fst z) (fst x) (fst y , yTx , zRy) = (y , yTx , zRy)
bimapR-functor-⊑ arg₂ (snd z) (snd x) (snd y , yUx , zSy) = (y , yUx , zSy)
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₁ z₁) (inj₁ x₁) (inj₁ y₁ , yTUx , zRSy) = bimapR-functor-⊑ F₁ z₁ x₁ (y₁ , yTUx , zRSy)
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₁ z₁) (inj₁ x₁) (inj₂ y₂ , () , ())
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₁ z₁) (inj₂ x₂) (inj₁ y₁ , () , zRSy)
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₁ z₁) (inj₂ x₂) (inj₂ y₂ , yTUx , ())
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₂ z₂) (inj₁ x₁) (inj₁ y₁ , yTUx , ())
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₂ z₂) (inj₁ x₁) (inj₂ y₂ , () , zRSy)
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₂ z₂) (inj₂ x₂) (inj₁ y₁ , () , ())
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₂ z₂) (inj₂ x₂) (inj₂ y₂ , yTUx , zRSy) = bimapR-functor-⊑ F₂ z₂ x₂ (y₂ , yTUx , zRSy)
bimapR-functor-⊑ (F₁ ⊗ F₂) (z₁ , z₂) (x₁ , x₂) ((y₁ , y₂) , yTUx , zRSy) =
   (bimapR-functor-⊑ F₁ z₁ x₁ (y₁ , (proj₁ yTUx) , (proj₁ zRSy)) , bimapR-functor-⊑ F₂ z₂ x₂ (y₂ , (proj₂ yTUx) , (proj₂ zRSy)))

bimapR-functor-⊒ : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set} {A₃ : Set j} {B₁ : Set k} {B₂ : Set} {B₃ : Set l}
                   {R : A₃ ← A₂} {S : B₃ ← B₂} {T : A₂ ← A₁} {U : B₂ ← B₁}
                  → bimapR F R S ○ bimapR F T U ⊒ bimapR F (R ○ T) (S ○ U)
bimapR-functor-⊒ zer () _ _
bimapR-functor-⊒ one tt tt _ = (tt , Data.Unit.tt , Data.Unit.tt)
bimapR-functor-⊒ arg₁ (fst z) (fst x) (y , yTx , zRy) = (fst y , yTx , zRy)
bimapR-functor-⊒ arg₂ (snd z) (snd x) (y , yUx , zSy) = (snd y , yUx , zSy)
bimapR-functor-⊒ (F₁ ⊕ F₂) (inj₁ z₁) (inj₁ x₁) zRTSUx =
   let
     (y₁ , yRTx , zSUy) = bimapR-functor-⊒ F₁ z₁ x₁ zRTSUx
   in (inj₁ y₁ , yRTx , zSUy)
bimapR-functor-⊒ (F₁ ⊕ F₂) (inj₁ z₁) (inj₂ x₂) ()
bimapR-functor-⊒ (F₁ ⊕ F₂) (inj₂ z₂) (inj₁ x₁) ()
bimapR-functor-⊒ (F₁ ⊕ F₂) (inj₂ z₂) (inj₂ x₂) zRTSUx =
   let
     (y₂ , yRTx , zSUy) = bimapR-functor-⊒ F₂ z₂ x₂ zRTSUx
   in (inj₂ y₂ , yRTx , zSUy)
bimapR-functor-⊒ (F₁ ⊗ F₂) (z₁ , z₂) (x₁ , x₂) zRTSUx =
   let
     (y₁ , yRTx₁ , zSUy₁) = bimapR-functor-⊒ F₁ z₁ x₁ (proj₁ zRTSUx)
     (y₂ , yRTx₂ , zSUy₂) = bimapR-functor-⊒ F₂ z₂ x₂ (proj₂ zRTSUx)
   in ((y₁ , y₂) , (yRTx₁ , yRTx₂) , (zSUy₁ , zSUy₂))

bimapR-monotonic-⊑ : (F : PolyF) → ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
                     {R S : B ← A} {T U : D ← C}
                    → (R ⊑ S) → (T ⊑ U) → (bimapR F R T ⊑ bimapR F S U)
bimapR-monotonic-⊑ zer R⊑S T⊑U () _ _
bimapR-monotonic-⊑ one R⊑S T⊑U tt tt _ = Data.Unit.tt
bimapR-monotonic-⊑ arg₁ R⊑S T⊑U (fst b) (fst a) bRa = R⊑S b a bRa
bimapR-monotonic-⊑ arg₂ R⊑S T⊑U (snd d) (snd c) dTc = T⊑U d c dTc
bimapR-monotonic-⊑ (F₁ ⊕ F₂) R⊑S T⊑U (inj₁ y₁) (inj₁ x₁) yRTx = bimapR-monotonic-⊑ F₁ R⊑S T⊑U y₁ x₁ yRTx
bimapR-monotonic-⊑ (F₁ ⊕ F₂) R⊑S T⊑U (inj₁ y₁) (inj₂ x₂) ()
bimapR-monotonic-⊑ (F₁ ⊕ F₂) R⊑S T⊑U (inj₂ y₂) (inj₁ x₁) ()
bimapR-monotonic-⊑ (F₁ ⊕ F₂) R⊑S T⊑U (inj₂ y₂) (inj₂ x₂) yRTx = bimapR-monotonic-⊑ F₂ R⊑S T⊑U y₂ x₂ yRTx
bimapR-monotonic-⊑ (F₁ ⊗ F₂) R⊑S T⊑U (y₁ , y₂) (x₁ , x₂) yRTx =
   (bimapR-monotonic-⊑ F₁ R⊑S T⊑U y₁ x₁ (proj₁ yRTx) , bimapR-monotonic-⊑ F₂ R⊑S T⊑U y₂ x₂ (proj₂ yRTx))

bimapR-monotonic-⊒ : (F : PolyF) → ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
                     {R S : B ← A} {T U : D ← C}
                    → (R ⊒ S) → (T ⊒ U) → (bimapR F R T ⊒ bimapR F S U)
bimapR-monotonic-⊒ zer R⊒S T⊒U () _ _
bimapR-monotonic-⊒ one R⊒S T⊒U tt tt _ = Data.Unit.tt
bimapR-monotonic-⊒ arg₁ R⊒S T⊒U (fst b) (fst a) bRa = R⊒S b a bRa
bimapR-monotonic-⊒ arg₂ R⊒S T⊒U (snd d) (snd c) dTc = T⊒U d c dTc
bimapR-monotonic-⊒ (F₁ ⊕ F₂) R⊒S T⊒U (inj₁ y₁) (inj₁ x₁) yRTx = bimapR-monotonic-⊒ F₁ R⊒S T⊒U y₁ x₁ yRTx
bimapR-monotonic-⊒ (F₁ ⊕ F₂) R⊒S T⊒U (inj₁ y₁) (inj₂ x₂) ()
bimapR-monotonic-⊒ (F₁ ⊕ F₂) R⊒S T⊒U (inj₂ y₂) (inj₁ x₁) ()
bimapR-monotonic-⊒ (F₁ ⊕ F₂) R⊒S T⊒U (inj₂ y₂) (inj₂ x₂) yRTx = bimapR-monotonic-⊒ F₂ R⊒S T⊒U y₂ x₂ yRTx
bimapR-monotonic-⊒ (F₁ ⊗ F₂) R⊒S T⊒U (y₁ , y₂) (x₁ , x₂) yRTx =
   (bimapR-monotonic-⊒ F₁ R⊒S T⊒U y₁ x₁ (proj₁ yRTx) , bimapR-monotonic-⊒ F₂ R⊒S T⊒U y₂ x₂ (proj₂ yRTx))


bimapR-˘-preservation-⊑ : (F : PolyF) → ∀ {i j} {A : Set} {B : Set i} {C : Set j}
                        → {R : C ← B}
                        →  (bimapR F idR R) ˘ ⊑ bimapR F {A₁ = A} idR (R ˘)
bimapR-˘-preservation-⊑ zer () _ _
bimapR-˘-preservation-⊑ one tt tt _ = Data.Unit.tt
bimapR-˘-preservation-⊑ arg₁ (fst a) (fst .a) refl = refl
bimapR-˘-preservation-⊑ arg₂ (snd b₁) (snd b₂) b₂Rb₁ = b₂Rb₁
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₁ x₁) (inj₁ y₁) pf = bimapR-˘-preservation-⊑ F₁ x₁ y₁ pf
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₁ x₁) (inj₂ y₂) ()
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₂ x₂) (inj₁ y₁) ()
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₂ x₂) (inj₂ y₂) pf = bimapR-˘-preservation-⊑ F₂ x₂ y₂ pf
bimapR-˘-preservation-⊑ (F₁ ⊗ F₂) (x₁ , x₂) (y₁ , y₂) pf =
  (bimapR-˘-preservation-⊑ F₁ x₁ y₁ (proj₁ pf) , bimapR-˘-preservation-⊑ F₂ x₂ y₂ (proj₂ pf))


bimapR-˘-preservation-⊒ : (F : PolyF) → ∀ {i j} {A : Set} {B : Set i} {C : Set j}
                        → {R : C ← B}
                        →  (bimapR F idR R) ˘ ⊒ bimapR F {A₁ = A} idR (R ˘)
bimapR-˘-preservation-⊒ zer () _ _
bimapR-˘-preservation-⊒ one tt tt _ = Data.Unit.tt
bimapR-˘-preservation-⊒ arg₁ (fst a) (fst .a) refl = refl
bimapR-˘-preservation-⊒ arg₂ (snd b₁) (snd b₂) b₂Rb₁ = b₂Rb₁
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₁ x₁) (inj₁ y₁) pf = bimapR-˘-preservation-⊒ F₁ x₁ y₁ pf
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₁ x₁) (inj₂ y₂) ()
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₂ x₂) (inj₁ y₁) ()
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₂ x₂) (inj₂ y₂) pf = bimapR-˘-preservation-⊒ F₂ x₂ y₂ pf
bimapR-˘-preservation-⊒ (F₁ ⊗ F₂) (x₁ , x₂) (y₁ , y₂) pf =
  (bimapR-˘-preservation-⊒ F₁ x₁ y₁ (proj₁ pf) , bimapR-˘-preservation-⊒ F₂ x₂ y₂ (proj₂ pf))


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

-- Be explicit that mapFoldR F G R is just bimapR G idR (foldR F R).

mapFold-bimap-⊑ : (F G : PolyF) → {A B : Set}
                → (R : B ← ⟦ F ⟧ A B)
                → mapFoldR F G R ⊑ bimapR G idR (foldR F R) 
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
                → mapFoldR F G R ⊒ bimapR G idR (foldR F R) 
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
              → mapFoldR F G R ≑ bimapR G idR (foldR F R)
mapFold-bimap F G R = (mapFold-bimap-⊑ F G R) , (mapFold-bimap-⊒ F G R)

-- computation rules:
--  foldR F R ○ fun In ≑ R ○ bimapR F idR (foldR F R)

foldR-computation'-⊑ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → foldR F R ○ fun In ⊑ R ○ mapFoldR F F R
foldR-computation'-⊑ F R b xs (._ , refl , p) = p

foldR-computation'-⊒ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → foldR F R ○ fun In ⊒ R ○ mapFoldR F F R
foldR-computation'-⊒ F R b xs p = In xs , refl , p

foldR-computation-⊑ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → (foldR F R ○ fun In ⊑ R ○ bimapR F idR (foldR F R))
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
                     → (foldR F R ○ fun In ⊒ R ○ bimapR F idR (foldR F R))
foldR-computation-⊒ F R = 
  ⊒-begin 
    foldR F R ○ fun In
  ⊒⟨ foldR-computation'-⊒ F R ⟩ 
    R ○ mapFoldR F F R 
  ⊒⟨ ○-monotonic-r (mapFold-bimap-⊒ F F R) ⟩ 
    R ○ bimapR F idR (foldR F R) 
  ⊒∎

foldR-computation : (F : PolyF) → {A B : Set}
                  → (R : B ← ⟦ F ⟧ A B)
                  → (foldR F R ○ fun In ≑ R ○ bimapR F idR (foldR F R))
foldR-computation F R = foldR-computation-⊑ F R , foldR-computation-⊒ F R

-- The Eilenberg-Wright lemma.

mutual

  Eilenberg-Wright-⊑ : ∀ (F : PolyF) → {A B : Set} → (R : B ← ⟦ F ⟧ A B) 
                       → foldR F R ⊑ ∈ ₁∘ fold F (Λ (R ○ bimapR F idR ∈))
  Eilenberg-Wright-⊑ F R b (In xs) (ys , mF , bRys) = 
    ys , mapFold-bimapΛ-⊑ F F R ys xs mF , bRys

  mapFold-bimapΛ-⊑ : (F G : PolyF) → {A B : Set}
                    → (R : B ← ⟦ F ⟧ A B) →
                    ∀ ys xs 
                    → mapFoldR F G R ys xs
                    → bimapR G idR ∈ ys (mapFold F G (Λ (R ○ bimapR F idR ∈)) xs)
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
                       → foldR F R ⊒ ∈ ₁∘ fold F (Λ (R ○ bimapR F idR ∈))
  Eilenberg-Wright-⊒ F R b (In xs) (ys , bm , bRys) = 
    ys , mapFold-bimapΛ-⊒ F F R ys xs bm , bRys

  mapFold-bimapΛ-⊒ : (F G : PolyF) → {A B : Set}
                    → (R : B ← ⟦ F ⟧ A B) →
                    ∀ ys xs 
                    → bimapR G idR ∈ ys (mapFold F G (Λ (R ○ bimapR F idR ∈)) xs)
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
                   → foldR F R ≑ ∈ ₁∘ fold F (Λ (R ○ bimapR F idR ∈))
Eilenberg-Wright F R = (Eilenberg-Wright-⊑ F R) , (Eilenberg-Wright-⊒ F R)

-- universal properties.

mutual

  foldR-universal-⇐-⊑ : (F : PolyF) → {A B : Set}
                      → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                      → (S ○ fun In ⊑ R ○ bimapR F idR S)
                      → (S ⊑ foldR F R)
  foldR-universal-⇐-⊑ F S R hom b (In xs) bSInxs with 
    hom b xs (_ , refl , bSInxs)
  ... | (ys , ysbFxs , bRys) = ys , mapFoldR-univ-⇐-⊑ F F S R hom ys xs ysbFxs , bRys

  mapFoldR-univ-⇐-⊑ : (F G : PolyF) → {A B : Set}
                    → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                    → (S ○ fun In ⊑ R ○ bimapR F idR S)
                    → bimapR G idR S ⊑ mapFoldR F G R
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
                      → (R ○ bimapR F idR S ⊑ S ○ fun In)
                      → (foldR F R ⊑ S)
  foldR-universal-⇐-⊒ F S R hom b (In xs) (ys , mF , bRys) with 
    hom b xs (ys , mapFoldR-univ-⇐-⊒ F F S R hom ys xs mF , bRys)
  ...  | (._ , refl , bSxs) = bSxs

  mapFoldR-univ-⇐-⊒ : (F G : PolyF) → {A B : Set}
                    → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                    → (R ○ bimapR F idR S ⊑ S ○ fun In)
                    → mapFoldR F G R ⊑ bimapR G idR S
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
                → R ⊑ S → foldR F R ⊑ foldR F S
foldR-monotonic F R S =
  ⇐-begin
    foldR F R ⊑ foldR F S
  ⇐⟨ foldR-universal-⇐-⊑ F (foldR F R) S ⟩
    (foldR F R) ○ fun In ⊑ S ○ bimapR F idR (foldR F R)
  ⇐⟨ ⊑-trans (foldR-computation-⊑ F R) ⟩
    R ○ bimapR F idR (foldR F R) ⊑ S ○ bimapR F idR (foldR F R)
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
               → (S ○ R ⊒ T ○ bimapR F idR S)
               → (S ○ foldR F R ⊒ foldR F T)
foldR-fusion-⊒ F S R T = 
   ⇐-begin
     foldR F T ⊑ S ○ foldR F R 
   ⇐⟨ foldR-universal-⇐-⊒ F (S ○ foldR F R) T ⟩ 
     T ○ bimapR F idR (S ○ foldR F R) ⊑ (S ○ foldR F R) ○ fun In
   ⇐⟨ ⊒-trans ○-assocl ⟩
     T ○ bimapR F idR (S ○ foldR F R) ⊑ S ○ foldR F R ○ fun In
   ⇐⟨ ⊒-trans (○-monotonic-r (foldR-computation-⊒ F R)) ⟩ 
     T ○ bimapR F idR (S ○ foldR F R) ⊑ S ○ R ○ bimapR F idR (foldR F R)
   ⇐⟨ ⊑-trans (○-monotonic-r (bimapR-monotonic-⊑ F id-idempotent-⊒ ⊑-refl)) ⟩ 
     T ○ bimapR F (idR ○ idR) (S ○ foldR F R) ⊑ S ○ R ○ bimapR F idR (foldR F R)
   ⇐⟨ ⊑-trans (○-monotonic-r (bimapR-functor-⊒ F)) ⟩ 
     T ○ bimapR F idR S ○ bimapR F idR (foldR F R) ⊑
              S ○ R ○ bimapR F idR (foldR F R)
   ⇐⟨ ⇦-mono-l (T ● bimapR F idR S ‥) (S ● R ‥) ⟩ 
     T ○ bimapR F idR S ⊑ S ○ R 
   ⇐∎

foldR-fusion-⊑ : (F : PolyF) → {A B C : Set}
               → (S : C ← B) → (R : B ← ⟦ F ⟧ A B) → (T : C ← ⟦ F ⟧ A C)
               → (S ○ R ⊑ T ○ bimapR F idR S)
               → (S ○ foldR F R ⊑ foldR F T)
foldR-fusion-⊑ F S R T = 
   ⇐-begin
     S ○ foldR F R ⊑ foldR F T 
   ⇐⟨ foldR-universal-⇐-⊑ F (S ○ foldR F R) T ⟩ 
    (S ○ foldR F R) ○ fun In ⊑ T ○ bimapR F idR (S ○ foldR F R) 
   ⇐⟨ ⊑-trans ○-assocr ⟩
     S ○ foldR F R ○ fun In ⊑ T ○ bimapR F idR (S ○ foldR F R)  
   ⇐⟨ ⊑-trans (○-monotonic-r (foldR-computation-⊑ F R)) ⟩ 
     S ○ R ○ bimapR F idR (foldR F R) ⊑ T ○ bimapR F idR (S ○ foldR F R)  
   ⇐⟨ ⊒-trans (○-monotonic-r (bimapR-monotonic-⊒ F id-idempotent-⊑ ⊒-refl)) ⟩ 
     S ○ R ○ bimapR F idR (foldR F R) ⊑ T ○ bimapR F (idR ○ idR) (S ○ foldR F R) 
   ⇐⟨ ⊒-trans (○-monotonic-r (bimapR-functor-⊑ F)) ⟩ 
     S ○ R ○ bimapR F idR (foldR F R) ⊑
       T ○ bimapR F idR S ○ bimapR F idR (foldR F R) 
   ⇐⟨ ⇦-mono-l (S ● R ‥) (T ● bimapR F idR S ‥)  ⟩ 
     S ○ R ⊑ T ○ bimapR F idR S
   ⇐∎


-- hylomorphism are least prefix points

hylo-lpfp : {A B C : Set} {F : PolyF} {R : B ← ⟦ F ⟧ A B} {S : C ← ⟦ F ⟧ A C}
                        → LeastPrefixedPoint (_⊑_) (λ X → R ○ bimapR F idR X ○ (S ˘)) (foldR F R ○ (foldR F S ˘))
hylo-lpfp {F = F} {R} {S} = (pfp , least)
  where
    pfp : R ○ bimapR F idR (foldR F R ○ (foldR F S ˘)) ○ (S ˘) ⊑ foldR F R ○ (foldR F S ˘)
    pfp =
      ⊑-begin
        R ○ bimapR F idR (foldR F R ○ (foldR F S ˘)) ○ (S ˘)
      ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F id-idempotent-⊒ ⊑-refl)) ⟩
        R ○ bimapR F (idR ○ idR) (foldR F R ○ (foldR F S ˘)) ○ (S ˘)
      ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-functor-⊒ F)) ⟩
        R ○ (bimapR F idR (foldR F R) ○ bimapR F idR (foldR F S ˘)) ○ (S ˘)
      ⊑⟨ ○-monotonic-r ○-assocr ⟩
        R ○ bimapR F idR (foldR F R) ○ bimapR F idR (foldR F S ˘) ○ (S ˘)
      ⊑⟨ ⇦-mono-l (R ● bimapR F idR (foldR F R) ‥) (foldR F R ● fun In ‥) (foldR-computation-⊒ F R) ⟩
        foldR F R ○ fun In ○ bimapR F idR (foldR F S ˘) ○ (S ˘)
      ⊑⟨ ○-monotonic-r ˘-idempotent-⊒ ⟩
        foldR F R ○ ((fun In ○ bimapR F idR (foldR F S ˘) ○ (S ˘)) ˘) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ ˘-○-distr3-⊑) ⟩
        foldR F R ○ (((S ˘) ˘) ○ (bimapR F idR (foldR F S ˘) ˘) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (○-monotonic-l ˘-idempotent-⊑)) ⟩
        foldR F R ○ (S ○ (bimapR F idR (foldR F S ˘) ˘) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (○-monotonic-r (○-monotonic-l (bimapR-˘-preservation-⊑ F)))) ⟩
        foldR F R ○ (S ○ (bimapR F idR ((foldR F S ˘) ˘)) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F ⊑-refl ˘-idempotent-⊑)))) ⟩
        foldR F R ○ (S ○ bimapR F idR (foldR F S) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (⇦-mono-l (S ● bimapR F idR (foldR F S) ‥) (foldR F S ● fun In ‥) (foldR-computation-⊒ F S))) ⟩
        foldR F R ○ (foldR F S ○ (fun In) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (○-monotonic-r fun-simple)) ⟩
        foldR F R ○ (foldR F S ○ idR) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ id-intro-r) ⟩
        foldR F R ○ (foldR F S ˘)
      ⊑∎

    least : ∀ {X} → R ○ bimapR F idR X ○ (S ˘) ⊑ X → foldR F R ○ (foldR F S ˘) ⊑ X
    least {X} =
      ⇐-begin
        foldR F R ○ (foldR F S ˘) ⊑ X
      ⇐⟨ /-universal-⇒ ⟩
        foldR F R ⊑ X / (foldR F S ˘)
      ⇐⟨ foldR-universal-⇐-⊒ F (X / (foldR F S ˘)) R ⟩
        R ○ bimapR F idR (X / (foldR F S ˘)) ⊑ (X / (foldR F S ˘)) ○ fun In
      ⇐⟨ ⊑-trans id-elim-r ⟩
        (R ○ bimapR F idR (X / (foldR F S ˘))) ○ idR ⊑ (X / (foldR F S ˘)) ○ fun In
      ⇐⟨ ⊑-trans (○-monotonic-r fun-entire) ⟩
        (R ○ bimapR F idR (X / (foldR F S ˘))) ○ (fun In ˘) ○ (fun In) ⊑ (X / (foldR F S ˘)) ○ fun In
      ⇐⟨ ⇦-mono-l (R ○ bimapR F idR (X / (foldR F S ˘)) ● (fun In ˘) ‥) ((X / (foldR F S ˘)) ‥) ⟩
        (R ○ bimapR F idR (X / (foldR F S ˘))) ○ (fun In ˘) ⊑ X / (foldR F S ˘)
      ⇐⟨ /-universal-⇐ ⟩
        ((R ○ bimapR F idR (X / (foldR F S ˘))) ○ (fun In ˘)) ○ (foldR F S ˘) ⊑ X
      ⇐⟨ ⊑-trans ○-assocr ⟩
        (R ○ bimapR F idR (X / (foldR F S ˘))) ○ (fun In ˘) ○ (foldR F S ˘) ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-r In˘FS˘⊑FS˘S˘) ⟩
        (R ○ bimapR F idR (X / (foldR F S ˘))) ○ (bimapR F idR (foldR F S ˘)) ○ (S ˘) ⊑ X
      ⇐⟨ ⊑-trans ○-assocl ⟩
        ((R ○ bimapR F idR (X / (foldR F S ˘))) ○ bimapR F idR (foldR F S ˘)) ○ (S ˘) ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-l ○-assocr) ⟩
        (R ○ (bimapR F idR (X / (foldR F S ˘))) ○ bimapR F idR (foldR F S ˘)) ○ (S ˘) ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-l (⇦-mono-r (R ‥) (bimapR-functor-⊑ F))) ⟩
        (R ○ bimapR F (idR ○ idR) (X / (foldR F S ˘) ○ (foldR F S ˘))) ○ (S ˘) ⊑ X
      ⇐⟨ ⊑-trans (⇦-mono-l ((R ○ bimapR F (idR ○ idR) (X / (foldR F S ˘) ○ foldR F S ˘)) ‥) (R ● bimapR F idR X ‥) (○-monotonic-r (bimapR-monotonic-⊑ F id-idempotent-⊑ (/-universal-⇒ ⊑-refl)))) ⟩
        R ○ bimapR F idR X ○ (S ˘) ⊑ X
      ⇐∎
     where
       In˘FS˘⊑FS˘S˘ : (fun In ˘) ○ (foldR F S ˘) ⊑ (bimapR F idR (foldR F S ˘)) ○ (S ˘)
       In˘FS˘⊑FS˘S˘ =
         (⇐-begin
            (fun In ˘) ○ (foldR F S ˘) ⊑ (bimapR F idR (foldR F S ˘)) ○ (S ˘)
          ⇐⟨ ⊑-trans (˘-○-distr-⊒ (foldR F S) (fun In)) ⟩
            (foldR F S ○ fun In) ˘ ⊑ (bimapR F idR (foldR F S ˘)) ○ (S ˘)
          ⇐⟨ ⊒-trans (○-monotonic-l (bimapR-˘-preservation-⊑ F)) ⟩
            (foldR F S ○ fun In) ˘ ⊑ (bimapR F idR (foldR F S) ˘) ○ (S ˘)
          ⇐⟨ ⊒-trans (˘-○-distr-⊑ S (bimapR F idR (foldR F S))) ⟩
            (foldR F S ○ fun In) ˘ ⊑ (S ○ bimapR F idR (foldR F S)) ˘
          ⇐⟨ ˘-monotonic-⇒ ⟩
            foldR F S ○ fun In ⊑ S ○ bimapR F idR (foldR F S)
          ⇐∎) (foldR-computation-⊑ F S) 

