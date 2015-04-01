{-# OPTIONS --universe-polymorphism #-}

module Relations where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Data.Product  using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)

open import Sets          using (_⊆_; ⊆-refl; ⊆-trans; 
                                 ℙ; singleton; _∪_; _∩_;
                                 _≡_; refl; subst; sym; cong)

_←_ : ∀ {i j k} → Set i → Set j → Set (suc k ⊔ℓ (j ⊔ℓ i)) -- Set (suc zero ⊔ℓ (j ⊔ℓ i))
_←_ {i} {j} {k} B A = B → A → Set k

_←_⊣_ :  ∀ {i j} → Set i → Set j → (k : Level) → Set (suc k ⊔ℓ (j ⊔ℓ i))
B  ← A ⊣ k = _←_ {k = k} B A

-- union and intersection

_⊔_ : ∀ {i j k} {A : Set i} {B : Set j} → (B ← A ⊣ k) → (B ← A ⊣ k) → (B ← A)
(r ⊔ s) b a = r b a ⊎ s b a

_⊓_ : ∀ {i j k} {A : Set i} {B : Set j} → (B ← A ⊣ k) → (B ← A ⊣ k) → (B ← A)
(r ⊓ s) b a = r b a × s b a

-- Relational Inclusion

infixr 6 _⊑_ _⊒_

_⊑_ : ∀ {i j k} {A : Set i} {B : Set j} → (B ← A ⊣ k) → (B ← A ⊣ k) → Set (k ⊔ℓ (j ⊔ℓ i))
R ⊑ S = ∀ b a → R b a → S b a

⊑-refl : ∀ {i j k} {A : Set i} {B : Set j} {R : B ← A ⊣ k} → R ⊑ R
⊑-refl _ a bRa = bRa

⊑-trans : ∀ {i j k} {A : Set i} {B : Set j} {R S T : B ← A ⊣ k} → R ⊑ S → S ⊑ T → R ⊑ T
⊑-trans R⊑S S⊑T b a bRa = S⊑T _ _ (R⊑S b a bRa) 

-- ⊓-universal :  R ⊑ S ⊓ T  ⇔  R ⊑ S  ×  R ⊑ T

⊓-universal-⇒ : ∀ {i j k} {A : Set i} {B : Set j} {R S T : B ← A ⊣ k} 
                → R ⊑ S ⊓ T → R ⊑ S × R ⊑ T
⊓-universal-⇒ R⊑S⊓T = (λ a b bRa → proj₁ (R⊑S⊓T a b bRa)) , 
                      (λ a b bRa → proj₂ (R⊑S⊓T a b bRa)) 

⊓-universal-⇐ : ∀ {i j k} {A : Set i} {B : Set j} {R S T : B ← A ⊣ k} 
                → R ⊑ S × R ⊑ T → R ⊑ S ⊓ T
⊓-universal-⇐ (R⊑S , R⊑T) a b bRa = (R⊑S a b bRa , R⊑T a b bRa)

⊑-⊓ : ∀ {i j k} {A : Set i} {B : Set j} 
      → (R S T : B ← A ⊣ k) → R ⊑ S ⊓ T → (R ⊑ S) × (R ⊑ T)
⊑-⊓ R S T = ⊓-universal-⇒

⊓-monotonic : ∀ {i j k} {A : Set i} {B : Set j} {R S T U : B ← A ⊣ k} 
              → R ⊑ T → S ⊑ U → R ⊓ S ⊑ T ⊓ U
⊓-monotonic R⊑T S⊑U a b (bRa , bSa) = R⊑T a b bRa , S⊑U a b bSa

-- ⊔-universal : R ⊔ S ⊑ T  ⇔  R ⊑ T  ×  S ⊑ T

⊔-universal-⇒ : ∀ {i j k} {A : Set i} {B : Set j} {R S T : B ← A ⊣ k} 
                → R ⊔ S ⊑ T → R ⊑ T × S ⊑ T
⊔-universal-⇒ R⊔S⊑T = (λ a b bRa → R⊔S⊑T a b (inj₁ bRa)),
                       (λ a b bSa → R⊔S⊑T a b (inj₂ bSa))

⊔-universal-⇐ : ∀ {i j k} {A : Set i} {B : Set j} {R S T : B ← A ⊣ k} 
                → R ⊑ T × S ⊑ T → R ⊔ S ⊑ T
⊔-universal-⇐ (R⊑T , S⊑T) a b (inj₁ bRa) = R⊑T a b bRa
⊔-universal-⇐ (R⊑T , S⊑T) a b (inj₂ bSa) = S⊑T a b bSa

⊔-monotonic : ∀ {i j k} {A : Set i} {B : Set j} {R S T U : B ← A ⊣ k} 
              → R ⊑ T → S ⊑ U → R ⊔ S ⊑ T ⊔ U
⊔-monotonic R⊑T S⊑U a b (inj₁ bRa) = inj₁ (R⊑T a b bRa)
⊔-monotonic R⊑T S⊑U a b (inj₂ bSa) = inj₂ (S⊑U a b bSa)

_⊒_ : ∀ {i j k} {A : Set i} {B : Set j} → (B ← A ⊣ k) → (B ← A) → Set (k ⊔ℓ (j ⊔ℓ i))
R ⊒ S = S ⊑ R

⊒-refl : ∀ {i j k} {A : Set i} {B : Set j} {R : B ← A ⊣ k} → R ⊒ R
⊒-refl = ⊑-refl

⊒-trans : ∀ {i j k} {A : Set i} {B : Set j} {R S T : B ← A ⊣ k} 
          → R ⊒ S → S ⊒ T → R ⊒ T
⊒-trans R⊒S S⊒T = ⊑-trans S⊒T R⊒S

infix 4 _≑_

_≑_ : ∀ {i j k} {A : Set i} {B : Set j} → (B ← A ⊣ k) → (B ← A) → Set (k ⊔ℓ (j ⊔ℓ i))
R ≑ S = (R ⊑ S × S ⊑ R)

-- converse and composition

_˘ : ∀ {i j k} {A : Set i} {B : Set j} → (B ← A ⊣ k) → A ← B
(r ˘) a b = r b a

infixr 8 _·_ 
infixr 9 _○_ _₁∘_

_·_ : {A B : Set} → (B ← A) → ℙ A → ℙ B
(R · s)  b = ∃ (λ a → (s a × R b a))

_○_ : ∀ {i j k l m} {A : Set i}{B : Set j}{C : Set k} → (C ← B ⊣ l) → (B ← A ⊣ m) → (C ← A ⊣ (j ⊔ℓ l ⊔ℓ m))
(R ○ S) c a = ∃ (λ b → S b a × R c b)

-- Another variation of the standard function composition.
-- Currently it's used only for cases where B is a set.
-- For example, when R is ∈, T/∋, min, etc.

-- Was:
--  _₁∘_ : ∀ {k} {A : Set} {B : Set1} {C : Set} → (C ← B ⊣ k) → (A → B) → (C ← A)
-- The new type does not enforce the intuition that if A : Set i, B : Set (suc i).
-- Is this definition redundant, or can it be generalised to something else?

_₁∘_ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} → (C ← B ⊣ l) → (A → B) → (C ← A)
(R ₁∘ S) c a = R c (S a) 

{-
-- perhaps we do not need it now that we have _₁∘_?

_₁∘₁_ : ∀ {k} {A : Set} {B : Set1} {C : Set1} → (C ← B ⊣ k) → (A → B) → (C ← A)
(R ₁∘₁ S) c a = R c (S a) 
-}


○-assocl : ∀ {i j k l m n o} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
            → {R : D ← C ⊣ m} {S : C ← B ⊣ n} {T : B ← A ⊣ o}
            → R ○ (S ○ T) ⊑ (R ○ S) ○ T
○-assocl d a (c , (b , (bTa , cSb)) , dRc) = 
             (b , (bTa , (c , (cSb  , dRc))))

○-assocr :  ∀ {i j k l m n o} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
            → {R : D ← C ⊣ m} {S : C ← B ⊣ n} {T : B ← A ⊣ o}
            → (R ○ S) ○ T ⊑ R ○ (S ○ T)
○-assocr d a (b , (bTa , (c , (cSb  , dRc)))) =
             (c , ((b , (bTa , cSb)) , dRc))

○-monotonic-r : ∀ {i j k l m} {A : Set i} {B : Set j} {C : Set k} 
                   {T : C ← B ⊣ l} {R S : B ← A ⊣ m}
                → R ⊑ S → T ○ R ⊑ T ○ S
○-monotonic-r R⊑S c a (b , (bRa , cTb)) = 
                      (b , (R⊑S b a bRa , cTb))  

○-monotonic-l : ∀ {i j k l m} {A : Set i} {B : Set j} {C : Set k} 
                  {T : B ← A ⊣ l} {R S : C ← B ⊣ m}
                → R ⊑ S → R ○ T ⊑ S ○ T
○-monotonic-l R⊑S c a (b , (bTa , cRb)) =
                      (b , (bTa , R⊑S c b cRb))

 -- can this type be more general?
modular-law : ∀ {i j} {A : Set i} {B : Set j} {C : Set j} {R : C ← B ⊣ j} {S : B ← A ⊣ j} {T : C ← A} 
              → (R ○ S) ⊓ T ⊑ R ○ (S ⊓ (R ˘ ○ T))
modular-law c a ((b , bSa , cRb) , cTa) = b , (bSa , (c , cTa , cRb)) , cRb

○-⊔-distr-l-⊑ : ∀ {i j k l} {A : Set i} {B C : Set j} {R : C ← B ⊣ k} {S : B ← A ⊣ l} {T : B ← A} 
                → R ○ (S ⊔ T) ⊑ (R ○ S) ⊔ (R ○ T)
○-⊔-distr-l-⊑ a c (b , inj₁ bSa , cRb) = inj₁ (b , bSa , cRb)
○-⊔-distr-l-⊑ a c (b , inj₂ bTa , cRb) = inj₂ (b , bTa , cRb)

○-⊔-distr-l-⊒ : ∀ {i j k l} {A : Set i} {B C : Set j} {R : C ← B ⊣ k} {S : B ← A ⊣ l} {T : B ← A} 
                → R ○ (S ⊔ T) ⊒ (R ○ S) ⊔ (R ○ T)
○-⊔-distr-l-⊒ a c (inj₁ (b , bSa , cRb)) = b , inj₁ bSa , cRb
○-⊔-distr-l-⊒ a c (inj₂ (b , bTa , cRb)) = b , inj₂ bTa , cRb

○-⊔-distr-r-⊑ : ∀ {i j k l} {A : Set i} {B C : Set j} {R : C ← B ⊣ k} {S : C ← B ⊣ k} {T : B ← A ⊣ l} 
                → (R ⊔ S) ○ T ⊑ (R ○ T) ⊔ (S ○ T)
○-⊔-distr-r-⊑ a c (b , bTa , inj₁ cRb) = inj₁ (b , bTa , cRb)
○-⊔-distr-r-⊑ a c (b , bTa , inj₂ cSb) = inj₂ (b , bTa , cSb)

○-⊔-distr-r-⊒ : ∀ {i j k l} {A : Set i} {B C : Set j} {R : C ← B ⊣ k} {S : C ← B ⊣ k} {T : B ← A ⊣ l} 
                → (R ⊔ S) ○ T ⊒ (R ○ T) ⊔ (S ○ T)
○-⊔-distr-r-⊒ a c (inj₁ (b , bTa , cRb)) = b , bTa , inj₁ cRb
○-⊔-distr-r-⊒ a c (inj₂ (b , bTa , cSb)) = b , bTa , inj₂ cSb

-- Primitive Relations

fun : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → (B ← A)
fun f b a = f a ≡ b


fun-comp : ∀ {i j} {A : Set i} {B : Set j} {C : Set j} {f : B → C} {g : A → B} →
            fun (f ∘ g)  ⊑  fun f ○ fun g
fun-comp {g = g} c a fga≡c = (g a , refl , fga≡c)

idR : ∀ {i} {A : Set i} → A ← A
idR = fun id

id-idempotent-⊒ : ∀ {i} {A : Set i} → idR ○ idR ⊒ idR {A = A}
id-idempotent-⊒ a .a refl = (a , refl , refl) 

id-idempotent-⊑ : ∀ {i} {A : Set i} → idR ○ idR ⊑ idR {A = A}
id-idempotent-⊑ a .a (.a , refl , refl) = refl 

id-intro-r : ∀ {i j} {A : Set i} {B : Set j} {R : B ← A ⊣ i} → R ⊒ R ○ idR
id-intro-r b a (.a , refl , bRa) = bRa  

id-intro-l : ∀ {i j} {A : Set i} {B : Set j} {R : B ← A ⊣ j} → R ⊒ idR ○ R
id-intro-l b a (.b , bRa , refl) = bRa

id-elim-r : ∀ {i j} {A : Set i} {B : Set j} {R : B ← A ⊣ i} → R ○ idR ⊒ R 
id-elim-r b a bRa = (a , refl , bRa) 

id-elim-l : ∀ {i j} {A : Set i} {B : Set j} {R : B ← A ⊣ j} → idR ○ R ⊒ R 
id-elim-l b a bRa = (b , bRa , refl) 

-- Power Transpose

Λ :  ∀ {i j} {A : Set i} {B : Set j} → (B ← A) → A → ℙ B
Λ R a = λ b → R b a

∈ : ∀ {i} {A : Set i} → (A ← ℙ A)
∈ a s = s a 

ℰ : ∀ {i j} {A : Set i} {B : Set (i ⊔ℓ j)} → (B ← A ⊣ j) → ℙ A → ℙ B
ℰ R = Λ (R ○ ∈)

∋ : ∀ {i} {A : Set i} → (ℙ A ← A)
∋ s a = s a 

-- ⊓₁-Λ-distr : (R ⊓₁ S) ₁∘ Λ T = (R ₁∘ Λ T) ⊓ (S ₁∘ Λ T)

⊓-Λ-distr-⊑ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} 
              → (R S : A ← ℙ B ⊣ l) → {T : B ← C}
              → (R ⊓ S) ₁∘ Λ T ⊑ (R ₁∘ Λ T) ⊓ (S ₁∘ Λ T)
⊓-Λ-distr-⊑ R S c a (aRTc , aSTc) = (aRTc , aSTc)

⊓-Λ-distr-⊒ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k}  
              → (R S : A ← ℙ B ⊣ l) → {T : B ← C}
              → (R ⊓ S) ₁∘ Λ T ⊒ (R ₁∘ Λ T) ⊓ (S ₁∘ Λ T)
⊓-Λ-distr-⊒ R S c a (aRTc , aSTc) = (aRTc , aSTc)

⊓-Λ-distr : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k}
            → (R S : A ← ℙ B ⊣ l) → {T : B ← C}
            → (R ⊓ S) ₁∘ Λ T ≑ (R ₁∘ Λ T) ⊓ (S ₁∘ Λ T)
⊓-Λ-distr R S = (⊓-Λ-distr-⊑ R S , ⊓-Λ-distr-⊒ R S)

{-
 -- Used in thin-universal-⇐. Is it necessary?
 -- Can it be subsumed by ⊓-Λ-distr-⊑?
₁⊓₁-Λ-distr : {A B C : Set} → (R S : ℙ A ← ℙ B) → {T : B ← C} →
              (R ⊓ S) ₁∘₁ Λ T ⊑ (R ₁∘₁ Λ T) ⊓ (S ₁∘₁ Λ T)
₁⊓₁-Λ-distr R S c a (aRTc , aSTc) = (aRTc , aSTc) 
-}

-- Products

infixr 2 _⨉_

_⨉_ : ∀ {i j k l m} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
     → (B ← A ⊣ m) → (D ← C ⊣ m) → ((B × D) ← (A × C)) 
(R ⨉ S) (b , d) (a , c) = (R b a × S d c)
