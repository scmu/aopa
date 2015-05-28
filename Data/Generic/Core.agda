module Data.Generic.Core where


open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id; const)
open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relation.Binary.PropositionalEquality

open import Relations
open import Relations.Function using (_≐_)
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

unfst : ∀ {i j} {A : Set i} → Fst {i} {j} A → A
unfst (fst x) = x

data Snd {i j} (X : Set j) : Set (i ⊔ℓ j) where
  snd : X → Snd {i} {j} X

unsnd : ∀ {i j} {X : Set j} → Snd {i} {j} X → X
unsnd (snd x) = x

⟦_⟧ : PolyF → ∀{i j} → (A : Set i) (X : Set j) → Set (i ⊔ℓ j)
⟦ zer ⟧ A X = Zero
⟦ one ⟧ A X = One
⟦ arg₁ ⟧ {i} {j} A X = Fst {i} {j} A
⟦ arg₂ ⟧ {i} {j} A X = Snd {i} {j} X
⟦ l ⊕ r ⟧ A X = ⟦ l ⟧ A X ⊎ ⟦ r ⟧ A X
⟦ l ⊗ r ⟧ A X = ⟦ l ⟧ A X × ⟦ r ⟧ A X

data μ (F : PolyF) {i} (A : Set i) : Set i where
  In : ⟦ F ⟧ A (μ F A) → μ F A

In-surjective : ∀ {F i}{A : Set i} → idR {A = μ F A} ⊑ fun In ○ fun In ˘
In-surjective (In xs) ._ refl = xs , refl , refl

In-injective : ∀ {F i}{A : Set i} → fun In ˘ ○ fun In ⊑ idR {A = ⟦ F ⟧ A (μ F A)}
In-injective xs ._ (._ , refl , refl) = refl

bimap : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set j} {B₁ : Set k} {B₂ : Set l}
        → (A₁ → A₂) → (B₁ → B₂) → ⟦ F ⟧ A₁ B₁ → ⟦ F ⟧ A₂ B₂
bimap zer f g ()
bimap one f g tt = tt
bimap arg₁ f g (fst a) = fst (f a)
bimap arg₂ f g (snd b) = snd (g b)
bimap (F₁ ⊕ F₂) f g (inj₁ x) = inj₁ (bimap F₁ f g x)
bimap (F₁ ⊕ F₂) f g (inj₂ y) = inj₂ (bimap F₂ f g y)
bimap (F₁ ⊗ F₂) f g (x , y) = bimap F₁ f g x , bimap F₂ f g y

fmap : (F : PolyF) → ∀ {i k l} {A : Set i} {B₁ : Set k} {B₂ : Set l}
     → (B₁ → B₂) → ⟦ F ⟧ A B₁ → ⟦ F ⟧ A B₂
fmap F f = bimap F id f

bimap-comp : (F : PolyF) → ∀ {i j k l m n} {A₁ : Set i} {A₂ : Set j} {A₃ : Set k} {B₁ : Set l} {B₂ : Set m} {B₃ : Set n}
            → (f : A₂ → A₃) → (g : B₂ → B₃) → (h : A₁ → A₂) → (k : B₁ → B₂)
            → (bimap F (f ∘ h) (g ∘ k) ≐ bimap F f g ∘ bimap F h k)
bimap-comp zer f g h k ()
bimap-comp one f g h k tt = refl
bimap-comp arg₁ f g h k (fst x) = refl
bimap-comp arg₂ f g h k (snd y) = refl
bimap-comp (F₁ ⊕ F₂) f g h k (inj₁ x) = cong inj₁ (bimap-comp F₁ f g h k x)
bimap-comp (F₁ ⊕ F₂) f g h k (inj₂ y) = cong inj₂ (bimap-comp F₂ f g h k y)
bimap-comp (F₁ ⊗ F₂) f g h k (x , y)
  rewrite bimap-comp F₁ f g h k x | bimap-comp F₂ f g h k y = refl

-- lifting a predicate


bimapP : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
        → (A → Set) → (B → Set) → (⟦ F ⟧ A B → Set)
bimapP zer P Q ()
bimapP one P Q tt = ⊤
bimapP arg₁ P Q (fst x) = P x
bimapP arg₂ P Q (snd x) = Q x
bimapP (F₀ ⊕ F₁) P Q (inj₁ x) = bimapP F₀ P Q x
bimapP (F₀ ⊕ F₁) P Q (inj₂ y) = bimapP F₁ P Q y
bimapP (F₀ ⊗ F₁) P Q (x , y) = bimapP F₀ P Q x × bimapP F₁ P Q y

fmapP : (F : PolyF) → ∀ {i j} {A : Set i} {B : Set j} 
      → (B → Set) → (⟦ F ⟧ A B → Set)
fmapP F P = bimapP F (const ⊤) P


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

fmapR : (F : PolyF) → ∀ {k l} {A : Set} {B₁ : Set k} {B₂ : Set l}
      → (B₂ ← B₁ ⊣ zero) → (⟦ F ⟧ A B₂ ← ⟦ F ⟧ A B₁ ⊣ zero)
fmapR F R = bimapR F idR R

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

bimapR-functor : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set} {A₃ : Set j}
                 {B₁ : Set k} {B₂ : Set} {B₃ : Set l}
                 {R : A₃ ← A₂} {S : B₃ ← B₂} {T : A₂ ← A₁} {U : B₂ ← B₁}
               → bimapR F R S ○ bimapR F T U ≑ bimapR F (R ○ T) (S ○ U)
bimapR-functor F = bimapR-functor-⊑ F , bimapR-functor-⊒ F

bimapR-monotonic : (F : PolyF) → ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
                     {R S : B ← A} {T U : D ← C}
                    → (R ⊑ S) → (T ⊑ U) → (bimapR F R T ⊑ bimapR F S U)
bimapR-monotonic zer R⊑S T⊑U () _ _
bimapR-monotonic one R⊑S T⊑U tt tt _ = Data.Unit.tt
bimapR-monotonic arg₁ R⊑S T⊑U (fst b) (fst a) bRa = R⊑S b a bRa
bimapR-monotonic arg₂ R⊑S T⊑U (snd d) (snd c) dTc = T⊑U d c dTc
bimapR-monotonic (F₁ ⊕ F₂) R⊑S T⊑U (inj₁ y₁) (inj₁ x₁) yRTx = bimapR-monotonic F₁ R⊑S T⊑U y₁ x₁ yRTx
bimapR-monotonic (F₁ ⊕ F₂) R⊑S T⊑U (inj₁ y₁) (inj₂ x₂) ()
bimapR-monotonic (F₁ ⊕ F₂) R⊑S T⊑U (inj₂ y₂) (inj₁ x₁) ()
bimapR-monotonic (F₁ ⊕ F₂) R⊑S T⊑U (inj₂ y₂) (inj₂ x₂) yRTx = bimapR-monotonic F₂ R⊑S T⊑U y₂ x₂ yRTx
bimapR-monotonic (F₁ ⊗ F₂) R⊑S T⊑U (y₁ , y₂) (x₁ , x₂) yRTx =
   (bimapR-monotonic F₁ R⊑S T⊑U y₁ x₁ (proj₁ yRTx) , bimapR-monotonic F₂ R⊑S T⊑U y₂ x₂ (proj₂ yRTx))

bimapR-cong : (F : PolyF) → ∀ {i j k l} {A : Set i} {B : Set j}
              {C : Set k} {D : Set l}
              {R S : B ← A} {T U : D ← C}
            → (R ≑ S) → (T ≑ U) → (bimapR F R T ≑ bimapR F S U)
bimapR-cong F (R⊑S , R⊒S) (T⊑U , T⊒U) =
  bimapR-monotonic F R⊑S T⊑U , bimapR-monotonic F R⊒S T⊒U

fmapR-functor : (F : PolyF) → ∀ {k l} {A : Set} {B₁ : Set k} {B₂ : Set} {B₃ : Set l}
                   {R : B₃ ← B₂} {S : B₂ ← B₁}
                  → fmapR F {A = A} R ○ fmapR F S ≑ fmapR F (R ○ S)
fmapR-functor F {R = R} {S} =
  ≑-begin
   fmapR F R ○ fmapR F S
  ≑⟨ bimapR-functor F ⟩
   bimapR _ (idR ○ idR) (R ○ S)
  ≑⟨ bimapR-cong _ id-idempotent ≑-refl ⟩
   fmapR F (R ○ S)
  ≑∎

fmapR-functor-⊑ : (F : PolyF) → ∀ {k l} {A : Set} {B₁ : Set k} {B₂ : Set} {B₃ : Set l}
                   {R : B₃ ← B₂} {S : B₂ ← B₁}
                  → fmapR F {A = A} R ○ fmapR F S ⊑ fmapR F (R ○ S)
fmapR-functor-⊑ F = proj₁ (fmapR-functor F)


fmapR-functor-⊒ : (F : PolyF) → ∀ {k l} {A : Set} {B₁ : Set k} {B₂ : Set} {B₃ : Set l}
                   {R : B₃ ← B₂} {S : B₂ ← B₁}
                  → fmapR F {A = A} R ○ fmapR F S ⊒ fmapR F (R ○ S)
fmapR-functor-⊒ F = proj₂ (fmapR-functor F)

fmapR-monotonic : (F : PolyF) → ∀ {k l} {A : Set} {B : Set k} {C : Set l}
                  {R S : B ← C}
                → (R ⊑ S) → (fmapR F {A = A} R ⊑ fmapR F S)   
fmapR-monotonic F = bimapR-monotonic F ⊑-refl

fmapR-cong : (F : PolyF) → ∀ {k l} {A : Set} {B : Set k} {C : Set l}
             {R S : B ← C}
           → (R ≑ S) → (fmapR F {A = A} R ≑ fmapR F S)
fmapR-cong F = bimapR-cong F ≑-refl           

bimapR-˘-preservation-⊑ : (F : PolyF) →
                        ∀ {i j k l} {A₀ : Set i} {A₁ : Set j} {B₀ : Set k} {B₁ : Set l}
                        → {R : A₀ ← A₁} {S : B₀ ← B₁}
                        → (bimapR F R S) ˘ ⊑ bimapR F (R ˘) (S ˘)
bimapR-˘-preservation-⊑ zer () _ _
bimapR-˘-preservation-⊑ one tt tt _ = Data.Unit.tt
bimapR-˘-preservation-⊑ arg₁ (fst a) (fst a') a'Ra = a'Ra
bimapR-˘-preservation-⊑ arg₂ (snd b₁) (snd b₂) b₂Rb₁ = b₂Rb₁
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₁ x₁) (inj₁ y₁) pf = bimapR-˘-preservation-⊑ F₁ x₁ y₁ pf
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₁ x₁) (inj₂ y₂) ()
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₂ x₂) (inj₁ y₁) ()
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₂ x₂) (inj₂ y₂) pf = bimapR-˘-preservation-⊑ F₂ x₂ y₂ pf
bimapR-˘-preservation-⊑ (F₁ ⊗ F₂) (x₁ , x₂) (y₁ , y₂) pf =
  (bimapR-˘-preservation-⊑ F₁ x₁ y₁ (proj₁ pf) , bimapR-˘-preservation-⊑ F₂ x₂ y₂ (proj₂ pf))

bimapR-˘-preservation-⊒ : (F : PolyF) →
                        ∀ {i j k l} {A₀ : Set i} {A₁ : Set j} {B₀ : Set k} {B₁ : Set l}
                        → {R : A₀ ← A₁} {S : B₀ ← B₁}
                        → (bimapR F R S) ˘ ⊒ bimapR F (R ˘) (S ˘)
bimapR-˘-preservation-⊒ zer () _ _
bimapR-˘-preservation-⊒ one tt tt _ = Data.Unit.tt
bimapR-˘-preservation-⊒ arg₁ (fst a₁) (fst a₂) a₂Ra₁ = a₂Ra₁
bimapR-˘-preservation-⊒ arg₂ (snd b₁) (snd b₂) b₂Sb₁ = b₂Sb₁
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₁ x₁) (inj₁ y₁) pf = bimapR-˘-preservation-⊒ F₁ x₁ y₁ pf
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₁ x₁) (inj₂ y₂) ()
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₂ x₂) (inj₁ y₁) ()
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₂ x₂) (inj₂ y₂) pf = bimapR-˘-preservation-⊒ F₂ x₂ y₂ pf
bimapR-˘-preservation-⊒ (F₁ ⊗ F₂) (x₁ , x₂) (y₁ , y₂) pf =
  (bimapR-˘-preservation-⊒ F₁ x₁ y₁ (proj₁ pf) , bimapR-˘-preservation-⊒ F₂ x₂ y₂ (proj₂ pf))

bimapR-˘-preservation : (F : PolyF) →
                        ∀ {i j k l} {A₀ : Set i} {A₁ : Set j} {B₀ : Set k} {B₁ : Set l}
                        → {R : A₀ ← A₁} {S : B₀ ← B₁}
                        → (bimapR F R S) ˘ ≑ bimapR F (R ˘) (S ˘)
bimapR-˘-preservation F = bimapR-˘-preservation-⊑ F , bimapR-˘-preservation-⊒ F                   

fmapR-˘-preservation : (F : PolyF) → ∀ {i j} {A : Set} {B : Set i} {C : Set j}
                     → {R : C ← B}
                     → (fmapR F R) ˘ ≑ fmapR F {A = A} (R ˘)
fmapR-˘-preservation F {R = R} = -- fmapR-˘-preservation-⊑ F , fmapR-˘-preservation-⊒ F 
  ≑-begin
    (fmapR F R) ˘
  ≑⟨ bimapR-˘-preservation F ⟩
    bimapR F (idR ˘) (R ˘)
  ≑⟨ bimapR-cong F id˘≑id ≑-refl ⟩
    fmapR F (R ˘)
  ≑∎
 where open import Relations.Converse using (id˘≑id)
  
fmapR-˘-preservation-⊑ : (F : PolyF) → ∀ {i j} {A : Set} {B : Set i} {C : Set j}
                        → {R : C ← B}
                        → (fmapR F R) ˘ ⊑ fmapR F {A = A} (R ˘)
fmapR-˘-preservation-⊑ F = proj₁ (fmapR-˘-preservation F)

fmapR-˘-preservation-⊒ : (F : PolyF) → ∀ {i j} {A : Set} {B : Set i} {C : Set j}
                        → {R : C ← B}
                        →  (fmapR F R) ˘ ⊒ fmapR F {A = A} (R ˘)
fmapR-˘-preservation-⊒ F = proj₂ (fmapR-˘-preservation F)                        
-- conversion between fmap and fmapR

{-
bimap-bimapR : (F : PolyF) → ∀ {A₁ A₂ B₁ B₂ : Set}
             → (f : A₁ → A₂) (g : B₁ → B₂)
             → fun (bimap F f g) ≑ bimapR F (fun f) (fun g)
bimap-bimapR F f g = {!!}             

-}

-- conversion between fmapP and fmapR

open import Relations.Coreflexive

fmap-¿-⊑ : (F : PolyF) → ∀ {A : Set} {B : Set}
         → (P : B → Set)
         → (fmapP F {A = A} P) ¿ ⊑ fmapR F (P ¿)
fmap-¿-⊑ zer P () _ _
fmap-¿-⊑ one P tt tt (refl , _) = Data.Unit.tt
fmap-¿-⊑ arg₁ P (fst a) (fst ._) (refl , _) = refl
fmap-¿-⊑ arg₂ P (snd b) (snd ._) (refl , Pb) = refl , Pb
fmap-¿-⊑ (F₀ ⊕ F₁) P (inj₁ x) (inj₁ ._) (refl , p) =
  fmap-¿-⊑ F₀ P x x (refl , p)
fmap-¿-⊑ (F₀ ⊕ F₁) P (inj₁ _) (inj₂ _) (() , _)
fmap-¿-⊑ (F₀ ⊕ F₁) P (inj₂ _) (inj₁ _) (() , _) 
fmap-¿-⊑ (F₀ ⊕ F₁) P (inj₂ x) (inj₂ ._) (refl , p) =
  fmap-¿-⊑ F₁ P x x (refl , p)
fmap-¿-⊑ (F₀ ⊗ F₁) P (x₀ , x₁) ._ (refl , p , q) =
  fmap-¿-⊑ F₀ P x₀ x₀ (refl , p) , fmap-¿-⊑ F₁ P x₁ x₁ (refl , q)

fmap-¿-⊒ : (F : PolyF) → ∀ {A : Set} {B : Set}
         → (P : B → Set)
         → (fmapP F {A = A} P) ¿ ⊒ fmapR F (P ¿)
fmap-¿-⊒ zer P () _ _
fmap-¿-⊒ one P tt tt _ = refl , Data.Unit.tt
fmap-¿-⊒ arg₁ P (fst x) (fst ._) refl = refl , Data.Unit.tt
fmap-¿-⊒ arg₂ P (snd x) (snd ._) (refl , Px) = refl , Px
fmap-¿-⊒ (F₀ ⊕ F₁) P (inj₁ x) (inj₁ x₁) bm with fmap-¿-⊒ F₀ P x x₁ bm
fmap-¿-⊒ (F₀ ⊕ F₁) P (inj₁ x) (inj₁ ._) bm | refl , q = refl , q
fmap-¿-⊒ (F₀ ⊕ F₁) P (inj₁ _) (inj₂ _) ()
fmap-¿-⊒ (F₀ ⊕ F₁) P (inj₂ _) (inj₁ _) ()
fmap-¿-⊒ (F₀ ⊕ F₁) P (inj₂ y) (inj₂ y₁) bm with fmap-¿-⊒ F₁ P y y₁ bm
fmap-¿-⊒ (F₀ ⊕ F₁) P (inj₂ y) (inj₂ ._) bm | refl , q = refl , q
fmap-¿-⊒ (F₀ ⊗ F₁) P (x₀ , y₀) (x₁ , y₁) (bm₀ , bm₁)
  with fmap-¿-⊒ F₀ P x₀ x₁ bm₀ | fmap-¿-⊒ F₁ P y₀ y₁ bm₁
fmap-¿-⊒ (F₀ ⊗ F₁) P (x₀ , y₀) (._ , ._) (bm₀ , bm₁) | refl , p | refl , q
  = refl , p , q

fmap-¿ : (F : PolyF) → ∀ {A : Set} {B : Set}
         → (P : B → Set)
         → (fmapP F {A = A} P) ¿ ≑ fmapR F (P ¿)
fmap-¿ F P = (fmap-¿-⊑ F P) , (fmap-¿-⊒ F P)

