module Data.Generic where

open import Sets
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Level renaming (_⊔_ to _⊔ℓ_)

open import Relations
open import Relations.PowerTrans
open import AlgebraicReasoning.ExtensionalEquality 
            using (_≐_; ≐-refl; ≐-sym; ≐-trans; ≐-trans'; 
                   pre-∘-cong; post-∘-cong)
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Sets
            using (⊆-begin_; _⊆⟨_⟩_; _⊆∎)

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


Λ-fusion-⊑ : {A B C : Set}
            → {R : C ← B} → (f : A → B)
            → (Λ R) ∘ f ⊑ Λ (R ○ fun f)
Λ-fusion-⊑ f a c cRfa = (f a , refl , cRfa)

Λ-fusion-⊒ : {A B C : Set}
            → {R : C ← B} → (f : A → B)
            → (Λ R) ∘ f ⊒ Λ (R ○ fun f)
Λ-fusion-⊒ f a c (b , fa≡b , cRb) rewrite fa≡b = cRb


bimapR-absorption-⊆ : (F : PolyF) → {A B C : Set} {f : B → ℙ C}
                     → (xs : ⟦ F ⟧ A B)
                     → Λ (bimapR F idR ∈) (bimap F id f xs) ⊆ Λ (bimapR F idR (∈ ₁∘ f)) xs
bimapR-absorption-⊆ zer () _ _
bimapR-absorption-⊆ one tt tt pf = pf
bimapR-absorption-⊆ arg₁ (fst a₁) (fst a₂) pf = pf
bimapR-absorption-⊆ arg₂ (snd b) (snd c) pf = pf
bimapR-absorption-⊆ (F₁ ⊕ F₂) (inj₁ x₁) (inj₁ x₂) pf = bimapR-absorption-⊆ F₁ x₁ x₂ pf
bimapR-absorption-⊆ (F₁ ⊕ F₂) (inj₁ x) (inj₂ y) ()
bimapR-absorption-⊆ (F₁ ⊕ F₂) (inj₂ y) (inj₁ x) ()
bimapR-absorption-⊆ (F₁ ⊕ F₂) (inj₂ y₁) (inj₂ y₂) pf = bimapR-absorption-⊆ F₂ y₁ y₂ pf
bimapR-absorption-⊆ (F₁ ⊗ F₂) (x₁ , x₂) (y₁ , y₂) pf =
   (bimapR-absorption-⊆ F₁ x₁ y₁ (proj₁ pf) , bimapR-absorption-⊆ F₂ x₂ y₂ (proj₂ pf))

bimapR-absorption-⊇ : (F : PolyF) → {A B C : Set} {f : B → ℙ C}
                     → (xs : ⟦ F ⟧ A B)
                     → Λ (bimapR F idR ∈) (bimap F id f xs) ⊇ Λ (bimapR F idR (∈ ₁∘ f)) xs
bimapR-absorption-⊇ zer () _ _
bimapR-absorption-⊇ one tt tt pf = pf
bimapR-absorption-⊇ arg₁ (fst a₁) (fst a₂) pf = pf
bimapR-absorption-⊇ arg₂ (snd b) (snd c) pf = pf
bimapR-absorption-⊇ (F₁ ⊕ F₂) (inj₁ x₁) (inj₁ x₂) pf = bimapR-absorption-⊇ F₁ x₁ x₂ pf
bimapR-absorption-⊇ (F₁ ⊕ F₂) (inj₁ x) (inj₂ y) ()
bimapR-absorption-⊇ (F₁ ⊕ F₂) (inj₂ y) (inj₁ x) ()
bimapR-absorption-⊇ (F₁ ⊕ F₂) (inj₂ y₁) (inj₂ y₂) pf = bimapR-absorption-⊇ F₂ y₁ y₂ pf
bimapR-absorption-⊇ (F₁ ⊗ F₂) (x₁ , x₂) (y₁ , y₂) pf =
   (bimapR-absorption-⊇ F₁ x₁ y₁ (proj₁ pf) , bimapR-absorption-⊇ F₂ x₂ y₂ (proj₂ pf))


ΛbimapR-absorption-⊑ : (F : PolyF) → {A B C : Set}
                      → (R : C ← ⟦ F ⟧ A C) → (f : B → ℙ C)
                      → Λ (R ○ bimapR F idR ∈) ∘ bimap F id f ⊑ Λ (R ○ bimapR F idR (∈ ₁∘ f))
ΛbimapR-absorption-⊑ F R f xs c (ys , pf , cRys) = (ys , bimapR-absorption-⊆ F xs ys pf , cRys)

ΛbimapR-absorption-⊒ : (F : PolyF) → {A B C : Set}
                      → (R : C ← ⟦ F ⟧ A C) → (f : B → ℙ C)
                      → Λ (R ○ bimapR F idR ∈) ∘ bimap F id f ⊒ Λ (R ○ bimapR F idR (∈ ₁∘ f))
ΛbimapR-absorption-⊒ F R f xs c (ys , pf , cRys) = (ys , bimapR-absorption-⊇ F xs ys pf , cRys)


mutual
  bimap⊆mapFold : (F G : PolyF) → {A B : Set}
                 → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                 → (S ○ fun In ⊑ R ○ bimapR F idR S)
                 → (xs : ⟦ G ⟧ A (μ F A)) 
                 → (Λ (bimapR G idR ∈) (bimap G id (Λ S) xs) ⊆ Λ (bimapR G idR ∈) (mapFold F G (Λ (R ○ bimapR F idR ∈)) xs))
  bimap⊆mapFold F zer S R SIn⊑RS () _ _
  bimap⊆mapFold F one S R SIn⊑RS tt tt pf = pf
  bimap⊆mapFold F arg₁ S R SIn⊑RS (fst a₁) (fst a₂) pf = pf
  bimap⊆mapFold F arg₂ S R SIn⊑RS (snd x) (snd b) pf = ΛS⊑fold F S R SIn⊑RS x b pf
  bimap⊆mapFold F (G₁ ⊕ G₂) S R SIn⊑RS (inj₁ x₁) (inj₁ y₁) pf = bimap⊆mapFold F G₁ S R SIn⊑RS x₁ y₁ pf
  bimap⊆mapFold F (G₁ ⊕ G₂) S R SIn⊑RS (inj₁ x₁) (inj₂ y₂) ()
  bimap⊆mapFold F (G₁ ⊕ G₂) S R SIn⊑RS (inj₂ x₂) (inj₁ y₁) ()
  bimap⊆mapFold F (G₁ ⊕ G₂) S R SIn⊑RS (inj₂ x₂) (inj₂ y₂) pf = bimap⊆mapFold F G₂ S R SIn⊑RS x₂ y₂ pf
  bimap⊆mapFold F (G₁ ⊗ G₂) S R SIn⊑RS (x₁ , x₂) (y₁ , y₂) pf =
     (bimap⊆mapFold F G₁ S R SIn⊑RS x₁ y₁ (proj₁ pf) , bimap⊆mapFold F G₂ S R SIn⊑RS x₂ y₂ (proj₂ pf))

  ΛS⊑fold : (F : PolyF) → {A B : Set}
           → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
           → (S ○ fun In ⊑ R ○ bimapR F idR S)
           → (Λ S ⊑ fold F (Λ (R ○ bimapR F idR ∈)))
  ΛS⊑fold F S R SIn⊑RS (In xs) =
     ⊆-begin
       Λ S (In xs)
     ⊆⟨ Λ-fusion-⊑ In xs ⟩
       Λ (S ○ fun In) xs
     ⊆⟨ Λ-monotonic SIn⊑RS xs ⟩
       Λ (R ○ bimapR F idR S) xs
     ⊆⟨ ΛbimapR-absorption-⊒ F R (Λ S) xs ⟩
       Λ (R ○ bimapR F idR ∈) (bimap F id (Λ S) xs)
     ⊆⟨ ΛRbimap⊆fold ⟩
       fold F (Λ (R ○ bimapR F idR ∈)) (In xs)
     ⊆∎
   where
     ΛRbimap⊆fold : Λ (R ○ bimapR F idR ∈) (bimap F id (Λ S) xs) ⊆ fold F (Λ (R ○ bimapR F idR ∈)) (In xs)
     ΛRbimap⊆fold b (ys , pf , bRys) = (ys , bimap⊆mapFold F F S R SIn⊑RS xs ys pf , bRys)
 
foldR-universal-⊑ : (F : PolyF) → {A B : Set}
                   → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                   → (S ○ fun In ⊑ R ○ bimapR F idR S)
                   → (S ⊑ foldR F R)
foldR-universal-⊑ F S R SIn⊑RS =
  (⇐-begin
    S ⊑ foldR F R
   ⇐⟨ ⇐-refl ⟩
    S ⊑ ∈ ₁∘ fold F (Λ (R ○ bimapR F idR ∈))
   ⇐⟨ Λ∈-galois-2 ⟩
    Λ S ⊑ fold F (Λ (R ○ bimapR F idR ∈))
   ⇐∎) (ΛS⊑fold F S R SIn⊑RS)


mutual
  mapFold⊆bimap : (F G : PolyF) → {A B : Set}
                 → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                 → (R ○ bimapR F idR S ⊑ S ○ fun In)
                 → (xs : ⟦ G ⟧ A (μ F A)) 
                 → (Λ (bimapR G idR ∈) (mapFold F G (Λ (R ○ bimapR F idR ∈)) xs) ⊆ Λ (bimapR G idR ∈) (bimap G id (Λ S) xs))
  mapFold⊆bimap F zer S R RS⊑SIn () _ _
  mapFold⊆bimap F one S R RS⊑SIn tt tt pf = pf
  mapFold⊆bimap F arg₁ S R RS⊑SIn (fst a₁) (fst a₂) pf = pf
  mapFold⊆bimap F arg₂ S R RS⊑SIn (snd x) (snd b) pf = fold⊑ΛS F S R RS⊑SIn x b pf
  mapFold⊆bimap F (G₁ ⊕ G₂) S R RS⊑SIn (inj₁ x₁) (inj₁ y₁) pf = mapFold⊆bimap F G₁ S R RS⊑SIn x₁ y₁ pf
  mapFold⊆bimap F (G₁ ⊕ G₂) S R RS⊑SIn (inj₁ x₁) (inj₂ y₂) ()
  mapFold⊆bimap F (G₁ ⊕ G₂) S R RS⊑SIn (inj₂ x₂) (inj₁ y₁) ()
  mapFold⊆bimap F (G₁ ⊕ G₂) S R RS⊑SIn (inj₂ x₂) (inj₂ y₂) pf = mapFold⊆bimap F G₂ S R RS⊑SIn x₂ y₂ pf
  mapFold⊆bimap F (G₁ ⊗ G₂) S R RS⊑SIn (x₁ , x₂) (y₁ , y₂) pf =
     (mapFold⊆bimap F G₁ S R RS⊑SIn x₁ y₁ (proj₁ pf) , mapFold⊆bimap F G₂ S R RS⊑SIn x₂ y₂ (proj₂ pf))

  fold⊑ΛS : (F : PolyF) → {A B : Set}
           → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
           → (R ○ bimapR F idR S ⊑ S ○ fun In)
           → (fold F (Λ (R ○ bimapR F idR ∈)) ⊑ Λ S)
  fold⊑ΛS F S R RS⊑SIn (In xs) =
     ⊆-begin
       fold F (Λ (R ○ bimapR F idR ∈)) (In xs)
     ⊆⟨ fold⊆ΛRbimap ⟩
       (Λ (R ○ bimapR F idR ∈)) (bimap F id (Λ S) xs)
     ⊆⟨ ΛbimapR-absorption-⊑ F R (Λ S) xs ⟩
       Λ (R ○ bimapR F idR S) xs
     ⊆⟨ Λ-monotonic RS⊑SIn xs ⟩
       Λ (S ○ fun In) xs
     ⊆⟨ Λ-fusion-⊒ In xs ⟩
       Λ S (In xs)
     ⊆∎
   where
     fold⊆ΛRbimap : fold F (Λ (R ○ bimapR F idR ∈)) (In xs) ⊆ (Λ (R ○ bimapR F idR ∈)) (bimap F id (Λ S) xs)
     fold⊆ΛRbimap b (ys , pf , bRys) = (ys , (mapFold⊆bimap F F S R RS⊑SIn xs ys pf) , bRys)

foldR-universal-⊒ : (F : PolyF) → {A B : Set}
                   → (S : B ← μ F A) → (R : B ← ⟦ F ⟧ A B)
                   → (S ○ fun In ⊒ R ○ bimapR F idR S)
                   → (S ⊒ foldR F R )
foldR-universal-⊒ F S R RS⊑SIn =
  (⇐-begin
    foldR F R ⊑ S
   ⇐⟨ ⇐-refl ⟩
    ∈ ₁∘ fold F (Λ (R ○ bimapR F idR ∈)) ⊑ S
   ⇐⟨ Λ∈-galois-1 ⟩
     fold F (Λ (R ○ bimapR F idR ∈)) ⊑ Λ S
   ⇐∎) (fold⊑ΛS F S R RS⊑SIn)


foldR-computation-⊑ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → (foldR F R ○ fun In ⊑ R ○ bimapR F idR (foldR F R))
foldR-computation-⊑ F R =
   (⇐-begin
      foldR F R ○ fun In ⊑ R ○ bimapR F idR (foldR F R)
    ⇐⟨ Λ-monotonic ⟩
      Λ (foldR F R ○ fun In) ⊑ Λ (R ○ bimapR F idR (foldR F R))
    ⇐⟨ ⊑-trans (Λ-fusion-⊒ In) ⟩
      Λ (foldR F R) ∘ In ⊑ Λ (R ○ bimapR F idR (foldR F R))
    ⇐⟨ ⊑-trans (Λ∈-cancelation (fold F (Λ (R ○ bimapR F idR ∈))) ∘ In) ⟩
      fold F (Λ (R ○ bimapR F idR ∈)) ∘ In ⊑ Λ (R ○ bimapR F idR (foldR F R))
    ⇐∎) fold⊑ΛRbimap
  where
     fold⊑ΛRbimap : fold F (Λ (R ○ bimapR F idR ∈)) ∘ In ⊑ Λ (R ○ bimapR F idR (foldR F R))
     fold⊑ΛRbimap xs =
        ⊆-begin
          fold F (Λ (R ○ bimapR F idR ∈)) (In xs)
        ⊆⟨ ⊆-subst (fold-computation F (Λ (R ○ bimapR F idR ∈)) xs) ⟩
          Λ (R ○ bimapR F idR ∈) (bimap F id (fold F (Λ (R ○ bimapR F idR ∈))) xs)
        ⊆⟨ ΛbimapR-absorption-⊑ F R (fold F (Λ (R ○ bimapR F idR ∈))) xs ⟩
          Λ (R ○ bimapR F idR (foldR F R)) xs
        ⊆∎
       where
         ⊆-subst : {A : Set} {r s : ℙ A} → r ≡ s → r ⊆ s
         ⊆-subst r≡s rewrite r≡s = ⊆-refl

foldR-computation-⊒ : (F : PolyF) → {A B : Set}
                     → (R : B ← ⟦ F ⟧ A B)
                     → (foldR F R ○ fun In ⊒ R ○ bimapR F idR (foldR F R))
foldR-computation-⊒ F R =
   (⇐-begin
      R ○ bimapR F idR (foldR F R) ⊑ foldR F R ○ fun In
    ⇐⟨ Λ-monotonic ⟩
      Λ (R ○ bimapR F idR (foldR F R)) ⊑ Λ (foldR F R ○ fun In)
    ⇐⟨ ⊒-trans (Λ-fusion-⊑ In) ⟩
      Λ (R ○ bimapR F idR (foldR F R)) ⊑ Λ (foldR F R) ∘ In
    ⇐⟨ ⇐-refl ⟩
      Λ (R ○ bimapR F idR (foldR F R)) ⊑ Λ (∈ ₁∘ fold F (Λ (R ○ bimapR F idR ∈))) ∘ In
    ⇐⟨ ⊒-trans (∈Λ-cancelation (fold F (Λ (R ○ bimapR F idR ∈))) ∘ In) ⟩
      Λ (R ○ bimapR F idR (foldR F R)) ⊑ fold F (Λ (R ○ bimapR F idR ∈)) ∘ In
    ⇐∎) ΛRbimap⊑fold
  where
     ΛRbimap⊑fold : Λ (R ○ bimapR F idR (foldR F R)) ⊑ fold F (Λ (R ○ bimapR F idR ∈)) ∘ In
     ΛRbimap⊑fold xs =
        ⊆-begin
          Λ (R ○ bimapR F idR (foldR F R)) xs
        ⊆⟨ ⊆-refl ⟩
          Λ (R ○ bimapR F idR (∈ ₁∘ fold F (Λ (R ○ bimapR F idR ∈)))) xs
        ⊆⟨ ΛbimapR-absorption-⊒ F R (fold F (Λ (R ○ bimapR F idR ∈))) xs ⟩
          Λ (R ○ bimapR F idR ∈) (bimap F id (fold F (Λ (R ○ bimapR F idR ∈))) xs)
        ⊆⟨ ⊇-subst (fold-computation F (Λ (R ○ bimapR F idR ∈)) xs) ⟩
          fold F (Λ (R ○ bimapR F idR ∈)) (In xs)
        ⊆∎
       where
         ⊇-subst : {A : Set} {r s : ℙ A} → r ≡ s → r ⊇ s
         ⊇-subst r≡s rewrite r≡s = ⊇-refl


foldR-fusion-⊑ : (F : PolyF) → {A : Set} {B : Set} {C : Set}
                → (R : C ← B) → (S : B ← ⟦ F ⟧ A B) → (T : C ← ⟦ F ⟧ A C)
                → R ○ S ⊑ T ○ bimapR F idR R
                → R ○ foldR F S ⊑ foldR F T
foldR-fusion-⊑ F R S T =
  ⇒-begin
    R ○ S ⊑ T ○ bimapR F idR R
  ⇒⟨ ○-monotonic-l ⟩
    (R ○ S) ○ bimapR F idR (foldR F S) ⊑ (T ○ bimapR F idR R) ○ bimapR F idR (foldR F S)
  ⇒⟨ ⊑-trans ○-assocl ⟩
    R ○ S ○ bimapR F idR (foldR F S) ⊑ (T ○ bimapR F idR R) ○ bimapR F idR (foldR F S)
  ⇒⟨ ⊒-trans ○-assocr ⟩
    R ○ S ○ bimapR F idR (foldR F S) ⊑ T ○ bimapR F idR R ○ bimapR F idR (foldR F S)
  ⇒⟨ ⊒-trans (○-monotonic-r (bimapR-functor-⊑ F)) ⟩
    R ○ S ○ bimapR F idR (foldR F S) ⊑ T ○ bimapR F (idR ○ idR) (R ○ (foldR F S))
  ⇒⟨ ⊒-trans (○-monotonic-r (bimapR-monotonic-⊑ F id-idempotent-⊑ ⊑-refl)) ⟩
    R ○ S ○ bimapR F idR (foldR F S) ⊑ T ○ bimapR F idR (R ○ (foldR F S))
  ⇒⟨ ⊑-trans (○-monotonic-r (foldR-computation-⊑ F S)) ⟩
    R ○ (foldR F S) ○ fun In ⊑ T ○ bimapR F idR (R ○ foldR F S)
  ⇒⟨ ⊑-trans ○-assocr ⟩
    (R ○ (foldR F S)) ○ fun In ⊑ T ○ bimapR F idR (R ○ foldR F S)
  ⇒⟨ foldR-universal-⊑ F (R ○ foldR F S) T ⟩
    R ○ foldR F S ⊑ foldR F T
  ⇒∎

foldR-fusion-⊒ : (F : PolyF) → {A : Set} {B : Set} {C : Set}
                → (R : C ← B) → (S : B ← ⟦ F ⟧ A B) → (T : C ← ⟦ F ⟧ A C)
                → R ○ S ⊒ T ○ bimapR F idR R
                → R ○ foldR F S ⊒ foldR F T
foldR-fusion-⊒ F R S T =
   ⇒-begin
     T ○ bimapR F idR R ⊑ R ○ S
   ⇒⟨ ○-monotonic-l ⟩
     (T ○ bimapR F idR R) ○ bimapR F idR (foldR F S) ⊑ (R ○ S) ○ bimapR F idR (foldR F S)
   ⇒⟨ ⊑-trans ○-assocl ⟩
     T ○ bimapR F idR R ○ bimapR F idR (foldR F S) ⊑ (R ○ S) ○ bimapR F idR (foldR F S)
   ⇒⟨ ⊒-trans ○-assocr ⟩
     T ○ bimapR F idR R ○ bimapR F idR (foldR F S) ⊑ R ○ S ○ bimapR F idR (foldR F S)
   ⇒⟨ ⊒-trans (○-monotonic-r (foldR-computation-⊒ F S)) ⟩
     T ○ bimapR F idR R ○ bimapR F idR (foldR F S) ⊑ R ○ foldR F S ○ fun In
   ⇒⟨ ⊑-trans (○-monotonic-r (bimapR-functor-⊒ F)) ⟩
     T ○ bimapR F (idR ○ idR) (R ○ foldR F S) ⊑ R ○ foldR F S ○ fun In
   ⇒⟨ ⊑-trans (○-monotonic-r (bimapR-monotonic-⊑ F id-idempotent-⊒ ⊑-refl)) ⟩
     T ○ bimapR F idR (R ○ foldR F S) ⊑ R ○ foldR F S ○ fun In
   ⇒⟨ ⊒-trans ○-assocl ⟩
     T ○ bimapR F idR (R ○ foldR F S) ⊑ (R ○ foldR F S) ○ fun In
   ⇒⟨ foldR-universal-⊒ F (R ○ foldR F S) T ⟩
     foldR F T ⊑ R ○ foldR F S
   ⇒∎
