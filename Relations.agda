{-# OPTIONS --universe-polymorphism #-}

module Relations where

open import Level renaming (_⊔_ to _⊔l_)
open import Data.Product  using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)

open import Sets          using (_⊆_; ⊆-refl; ⊆-trans; 
                                 ℙ; singleton; _∪_; _∩_;
                                 _≡_; refl; subst; sym; cong)

_←_   : ∀ {i j : Level} → Set i → Set j → Set (suc zero ⊔l (j ⊔l i))
_←_ {i} {j} B A  =  B → A → Set

{-
_←₁_  : Set  → Set1 → Set1
B  ←₁ A  =  B → A → Set

_₁←_  : Set1 → Set  → Set1
B ₁←  A  =  B → A → Set

_₁←₁_ : Set1 → Set1 → Set1
B ₁←₁ A  =  B → A → Set
-}

-- union and intersection

_⊔_ : ∀ {i j : Level} {A : Set i} {B : Set j} → (B ← A) → (B ← A) → (B ← A)
(r ⊔ s) b a = r b a ⊎ s b a

_⊓_ : ∀ {i j : Level} {A : Set i} {B : Set j} → (B ← A) → (B ← A) → (B ← A)
(r ⊓ s) b a = r b a × s b a
{-
_⊓₁_ : {A : Set1}{B : Set} → (B ←₁ A) → (B ←₁ A) → (B ←₁ A)
(r ⊓₁ s) b a = r b a × s b a

_₁⊓_ : {A : Set}{B : Set1} → (B ₁← A) → (B ₁← A) → (B ₁← A)
(r ₁⊓ s) b a = r b a × s b a

_₁⊓₁_ : {A B : Set1} → (B ₁←₁ A) → (B ₁←₁ A) → (B ₁←₁ A)
(r ₁⊓₁ s) b a = r b a × s b a
-}
-- Relational Inclusion

infixr 6 _⊑_ _⊒_

_⊑_ : ∀ {i j : Level} {A : Set i} {B : Set j} → (B ← A) → (B ← A) → Set (j ⊔l i)
R ⊑ S = ∀ b a → R b a → S b a

⊑-refl : ∀ {i j : Level} {A : Set i} {B : Set j} {R : B ← A} → R ⊑ R
⊑-refl _ a bRa = bRa

⊑-trans : ∀ {i j : Level} {A : Set i} {B : Set j} {R S T : B ← A} → R ⊑ S → S ⊑ T → R ⊑ T
⊑-trans R⊑S S⊑T b a bRa = S⊑T _ _ (R⊑S b a bRa) 

-- ⊓-universal :  R ⊑ S ⊓ T  ⇔  R ⊑ S  ×  R ⊑ T

⊓-universal-⇒ : ∀ {i j : Level} {A : Set i} {B : Set j} {R S T : B ← A} 
                → R ⊑ S ⊓ T → R ⊑ S × R ⊑ T
⊓-universal-⇒ R⊑S⊓T = (λ a b bRa → proj₁ (R⊑S⊓T a b bRa)) , 
                      (λ a b bRa → proj₂ (R⊑S⊓T a b bRa)) 

⊓-universal-⇐ : ∀ {i j : Level} {A : Set i} {B : Set j} {R S T : B ← A} 
                → R ⊑ S × R ⊑ T → R ⊑ S ⊓ T
⊓-universal-⇐ (R⊑S , R⊑T) a b bRa = (R⊑S a b bRa , R⊑T a b bRa)

⊑-⊓ : ∀ {i j : Level} {A : Set i} {B : Set j} 
      → (R S T : B ← A) → R ⊑ S ⊓ T → (R ⊑ S) × (R ⊑ T)
⊑-⊓ R S T = ⊓-universal-⇒

⊓-monotonic : ∀ {i j : Level} {A : Set i} {B : Set j} {R S T U : B ← A} 
              → R ⊑ T → S ⊑ U → R ⊓ S ⊑ T ⊓ U
⊓-monotonic R⊑T S⊑U a b (bRa , bSa) = R⊑T a b bRa , S⊑U a b bSa

-- ⊔-universal : R ⊔ S ⊑ T  ⇔  R ⊑ T  ×  S ⊑ T

⊔-universal-⇒ : ∀ {i j : Level} {A : Set i} {B : Set j} {R S T : B ← A} 
                → R ⊔ S ⊑ T → R ⊑ T × S ⊑ T
⊔-universal-⇒ R⊔S⊑T = (λ a b bRa → R⊔S⊑T a b (inj₁ bRa)),
                       (λ a b bSa → R⊔S⊑T a b (inj₂ bSa))

⊔-universal-⇐ : ∀ {i j : Level} {A : Set i} {B : Set j} {R S T : B ← A} 
                → R ⊑ T × S ⊑ T → R ⊔ S ⊑ T
⊔-universal-⇐ (R⊑T , S⊑T) a b (inj₁ bRa) = R⊑T a b bRa
⊔-universal-⇐ (R⊑T , S⊑T) a b (inj₂ bSa) = S⊑T a b bSa

⊔-monotonic : ∀ {i j : Level} {A : Set i} {B : Set j} {R S T U : B ← A} 
              → R ⊑ T → S ⊑ U → R ⊔ S ⊑ T ⊔ U
⊔-monotonic R⊑T S⊑U a b (inj₁ bRa) = inj₁ (R⊑T a b bRa)
⊔-monotonic R⊑T S⊑U a b (inj₂ bSa) = inj₂ (S⊑U a b bSa)

_⊒_ : ∀ {i j : Level} {A : Set i} {B : Set j} → (B ← A) → (B ← A) → Set (j ⊔l i)
R ⊒ S = S ⊑ R

⊒-refl : ∀ {i j : Level} {A : Set i} {B : Set j} {R : B ← A} → R ⊒ R
⊒-refl = ⊑-refl

⊒-trans : ∀ {i j : Level} {A : Set i} {B : Set j} {R S T : B ← A} 
          → R ⊒ S → S ⊒ T → R ⊒ T
⊒-trans R⊒S S⊒T = ⊑-trans S⊒T R⊒S

infix 4 _≑_

_≑_ : ∀ {i j : Level} {A : Set i} {B : Set j} → (B ← A) → (B ← A) → Set (j ⊔l i)
R ≑ S = (R ⊑ S × S ⊑ R)
{-
_⊑₁_ : {A : Set1} {B : Set} → (B ←₁ A) → (B ←₁ A) → Set1
R ⊑₁ S = ∀ b a → R b a → S b a 

⊑₁-refl : {A : Set1} {B : Set} {R : B ←₁ A} → R ⊑₁ R
⊑₁-refl _ _ bRa = bRa

⊑₁-trans : {A : Set1} {B : Set} {R S T : B ←₁ A} → R ⊑₁ S → S ⊑₁ T → R ⊑₁ T
⊑₁-trans R⊑S S⊑T a b bRa = S⊑T a b (R⊑S a b bRa)

_⊒₁_ : {A : Set1} {B : Set} → (B ←₁ A) → (B ←₁ A) → Set1
R ⊒₁ S = S ⊑₁ R

⊒₁-refl : {A : Set1} {B : Set} {R : B ←₁ A} → R ⊒₁ R
⊒₁-refl = ⊑₁-refl

⊒₁-trans : {A : Set1} {B : Set} {R S T : B ←₁ A} → R ⊒₁ S → S ⊒₁ T → R ⊒₁ T
⊒₁-trans R⊒S S⊒T = ⊑₁-trans S⊒T R⊒S

_₁⊑_ : {A : Set} {B : Set1} → (B ₁← A) → (B ₁← A) → Set1
R ₁⊑ S = ∀ b a → R b a → S b a

₁⊑-refl : {A : Set} {B : Set1} {R : B ₁← A} → R ₁⊑ R
₁⊑-refl _ _ bRa = bRa

₁⊑-trans : {A : Set} {B : Set1} {R S T : B ₁← A} → R ₁⊑ S → S ₁⊑ T → R ₁⊑ T
₁⊑-trans R⊑S S⊑T a b bRa = S⊑T a b (R⊑S a b bRa)

_₁⊒_ : {A : Set} {B : Set1} → (B ₁← A) → (B ₁← A) → Set1
R ₁⊒ S = S ₁⊑ R

₁⊒-refl : {A : Set} {B : Set1} {R : B ₁← A} → R ₁⊒ R
₁⊒-refl = ₁⊑-refl

₁⊒-trans : {A : Set} {B : Set1} {R S T : B ₁← A} → R ₁⊒ S → S ₁⊒ T → R ₁⊒ T
₁⊒-trans R⊒S S⊒T = ₁⊑-trans S⊒T R⊒S
-}
-- converse and composition

_˘ : {i j : Level} {A : Set i} {B : Set j} → B ← A → A ← B
(r ˘) a b = r b a
{-
_˘₁ : {A : Set1} {B : Set} → B ←₁ A → A ₁← B
(r ˘₁) b a = r a b

_₁˘ : {A : Set} {B : Set1} → B ₁← A → A ←₁ B
(r ₁˘) b a = r a b

_₁˘₁ : {A B : Set1} → B ₁←₁ A → A ₁←₁ B
(r ₁˘₁) b a = r a b
-}
infixr 8 _·_ 
infixr 9 _○_
-- infixr 9 _○₁_
infixr 9 _₁∘_ _₁∘₁_

_·_ : {A B : Set} → (B ← A) → ℙ A → ℙ B
(R · s)  b = ∃ (λ a → (s a × R b a))

_○_ : {i k : Level} {A : Set i} {B : Set}{C : Set k} → C ← B → B ← A → C ← A
(R ○ S) c a = ∃ (λ b → S b a × R c b)

{-
_○₁_ : {A : Set1} {B C : Set} → C ← B → (B ←₁ A) → (C ←₁ A)
(R ○₁ S) c a = ∃ (λ b → S b a × R c b)

_₁○_ : {A B : Set} {C : Set1} → C ₁← B → (B ← A) → (C ₁← A)
(R ₁○ S) c a = ∃ (λ b → (S b a × R c b))
-}
-- Another variation of the standard function composition.
-- Currently it's used only for cases where B is a set.
-- For example, when R is ∈, T/∋, min, etc.
 
_₁∘_ : {A : Set} {B : Set1} {C : Set} → (C ← B) → (A → B) → (C ← A)
(R ₁∘ S) c a = R c (S a) 

_₁∘₁_ : {A : Set} {B : Set1} {C : Set1} → (C ← B) → (A → B) → (C ← A)
(R ₁∘₁ S) c a = R c (S a) 

{-
○₁-monotonic : {A : Set1} {B C : Set} {S T : C ← B} →
   S ⊑ T → (R : B ←₁ A) → (S ○₁ R) ⊑₁ (T ○₁ R)
○₁-monotonic S⊑T R c a (b , (bRa , cSb)) = (b , (bRa , S⊑T c b cSb)) 
-}

○-assocl : ∀ {i} {A : Set i} {B C D : Set} →
       {R : D ← C} {S : C ← B} {T : B ← A} →
            R ○ (S ○ T) ⊑ (R ○ S) ○ T
○-assocl d a (c , (b , (bTa , cSb)) , dRc) = 
             (b , (bTa , (c , (cSb  , dRc))))

○-assocr : ∀ {i} {A : Set i} {B C D : Set} →
      {R : D ← C} {S : C ← B} {T : B ← A} →
           (R ○ S) ○ T ⊑ R ○ (S ○ T)
○-assocr d a (b , (bTa , (c , (cSb  , dRc)))) =
             (c , ((b , (bTa , cSb)) , dRc))
{-
○₁-assocl : {A : Set1} {B C D : Set} →
       {R : D ← C} {S : C ← B} (T : B ←₁ A) →
            R ○₁ (S ○₁ T) ⊑₁ (R ○ S) ○₁ T
○₁-assocl T a d (c , ((b , (bTa , bSc)) , cRd)) = 
                (b , (bTa , c , (bSc  , cRd)))

○₁-assocr : {A : Set1} {B C D : Set} →
      {R : D ← C} {S : C ← B} (T : B ←₁ A) →
           (R ○ S) ○₁ T ⊑₁ R ○₁ (S ○₁ T)
○₁-assocr T a d (b , (aTb , c , (bSc  , cRd))) =
                (c , ((b , (aTb , bSc)) , cRd))
-}

○-monotonic-r : ∀ {i} {A : Set i} {B C : Set} {T : C ← B} {R S : B ← A} →
   R ⊑ S → T ○ R ⊑ T ○ S
○-monotonic-r R⊑S c a (b , (bRa , cTb)) = 
                      (b , (R⊑S b a bRa , cTb))  

○-monotonic-l : ∀ {i} {A : Set i} {B C : Set} {T : B ← A} {R S : C ← B} →
    R ⊑ S → R ○ T ⊑ S ○ T
○-monotonic-l R⊑S c a (b , (bTa , cRb)) =
                      (b , (bTa , R⊑S c b cRb))

modular-law : ∀ {i} {A : Set i} {B C : Set} {R : C ← B} {S : B ← A} {T : C ← A} 
              → (R ○ S) ⊓ T ⊑ R ○ (S ⊓ (R ˘ ○ T))
modular-law c a ((b , bSa , cRb) , cTa) = b , (bSa , (c , cTa , cRb)) , cRb

○-⊔-distr-l-⊑ : ∀ {i} {A : Set i} {B C : Set} {R : C ← B} {S : B ← A} {T : B ← A} 
                → R ○ (S ⊔ T) ⊑ (R ○ S) ⊔ (R ○ T)
○-⊔-distr-l-⊑ a c (b , inj₁ bSa , cRb) = inj₁ (b , bSa , cRb)
○-⊔-distr-l-⊑ a c (b , inj₂ bTa , cRb) = inj₂ (b , bTa , cRb)

○-⊔-distr-l-⊒ : ∀ {i} {A : Set i} {B C : Set} {R : C ← B} {S : B ← A} {T : B ← A} 
                → R ○ (S ⊔ T) ⊒ (R ○ S) ⊔ (R ○ T)
○-⊔-distr-l-⊒ a c (inj₁ (b , bSa , cRb)) = b , inj₁ bSa , cRb
○-⊔-distr-l-⊒ a c (inj₂ (b , bTa , cRb)) = b , inj₂ bTa , cRb

○-⊔-distr-r-⊑ : ∀ {i} {A : Set i} {B C : Set} {R : C ← B} {S : C ← B} {T : B ← A} 
                → (R ⊔ S) ○ T ⊑ (R ○ T) ⊔ (S ○ T)
○-⊔-distr-r-⊑ a c (b , bTa , inj₁ cRb) = inj₁ (b , bTa , cRb)
○-⊔-distr-r-⊑ a c (b , bTa , inj₂ cSb) = inj₂ (b , bTa , cSb)

○-⊔-distr-r-⊒ : ∀ {i} {A : Set i} {B C : Set} {R : C ← B} {S : C ← B} {T : B ← A} 
                → (R ⊔ S) ○ T ⊒ (R ○ T) ⊔ (S ○ T)
○-⊔-distr-r-⊒ a c (inj₁ (b , bTa , cRb)) = b , bTa , inj₁ cRb
○-⊔-distr-r-⊒ a c (inj₂ (b , bTa , cSb)) = b , bTa , inj₂ cSb

-- Primitive Relations

fun : {A B : Set} → (A → B) → (B ← A)
fun f b a = f a ≡ b

fun-comp : {A B C : Set} {f : B → C} {g : A → B} →
            fun (f ∘ g)  ⊑  fun f ○ fun g
fun-comp {g = g} c a fga≡c = (g a , refl , fga≡c)

idR : ∀ {A} → A ← A
idR = fun id

id-idempotent-⊒ : ∀ {A} → idR ○ idR ⊒ idR {A} 
id-idempotent-⊒ a .a refl = (a , refl , refl) 

id-idempotent-⊑ : ∀ {A} → idR ○ idR ⊑ idR {A}
id-idempotent-⊑ a .a (.a , refl , refl) = refl 

id-intro-r : ∀ {j} {A} {B : Set j} {R : B ← A} → R ⊒ R ○ idR
id-intro-r b a (.a , refl , bRa) = bRa  

id-intro-l : {A B : Set} {R : B ← A} → R ⊒ idR ○ R
id-intro-l b a (.b , bRa , refl) = bRa

id-elim-r : ∀ {j} {A} {B : Set j} {R : B ← A} → R ○ idR ⊒ R 
id-elim-r b a bRa = (a , refl , bRa) 

id-elim-l : {A B : Set} {R : B ← A} → idR ○ R ⊒ R 
id-elim-l b a bRa = (b , bRa , refl) 

-- Power Transpose

Λ :  ∀ {i} {A : Set i} {B : Set} → (B ← A) → A → ℙ B
Λ R a = λ b → R b a
{-
Λ₁ : {PA : Set1} {B : Set} → (B ←₁ PA) → PA → ℙ B
Λ₁ R a = λ b → R b a -}

∈ : {A : Set} → A ← ℙ A 
∈ a s = s a 

ℰ : {A B : Set} → (B ← A) → ℙ A → ℙ B
ℰ R = Λ (R ○ ∈)

∋ : {A : Set} → ℙ A ← A
∋ s a = s a 

-- ⊓₁-Λ-distr : (R ⊓₁ S) ₁∘ Λ T = (R ₁∘ Λ T) ⊓ (S ₁∘ Λ T)

⊓-Λ-distr-⊑ : {A B C : Set} → (R S : A ← ℙ B) → {T : B ← C} →
  (R ⊓ S) ₁∘ Λ T ⊑ (R ₁∘ Λ T) ⊓ (S ₁∘ Λ T)
⊓-Λ-distr-⊑ R S c a (aRTc , aSTc) = (aRTc , aSTc)

⊓-Λ-distr-⊒ : {A B C : Set} → (R S : A ← ℙ B) → {T : B ← C} →
  (R ⊓ S) ₁∘ Λ T ⊒ (R ₁∘ Λ T) ⊓ (S ₁∘ Λ T)
⊓-Λ-distr-⊒ R S c a (aRTc , aSTc) = (aRTc , aSTc)

⊓-Λ-distr : {A B C : Set} → (R S : A ← ℙ B) → {T : B ← C} →
  (R ⊓ S) ₁∘ Λ T ≑ (R ₁∘ Λ T) ⊓ (S ₁∘ Λ T)
⊓-Λ-distr R S = (⊓-Λ-distr-⊑ R S , ⊓-Λ-distr-⊒ R S)

 -- Used in thin-universal-⇐. Is it necessary?
₁⊓₁-Λ-distr : {A B C : Set} → (R S : ℙ A ← ℙ B) → {T : B ← C} →
  (R ⊓ S) ₁∘₁ Λ T ⊑ (R ₁∘₁ Λ T) ⊓ (S ₁∘₁ Λ T)
₁⊓₁-Λ-distr R S c a (aRTc , aSTc) = (aRTc , aSTc) 

-- Products

-- infixr 4 _,₁_ _₁,₁_
infixr 2 _⨉_ -- _×₁_ _⨉₁_ _₁×₁_ _₁⨉₁_

_⨉_ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l} → 
      (B ← A) → (D ← C) → ((B × D) ← (A × C)) 
(R ⨉ S) (b , d) (a , c) = (R b a × S d c)
{-
data _×₁_ (A : Set) (B : Set1): Set1 where
  _,₁_ : A → B → A ×₁ B

_⨉₁_ : {A B : Set} {C : Set1} {D : Set} → 
       (B ← A) → (D ←₁ C) → ((B × D) ←₁ (A ×₁ C)) 
(R ⨉₁ S) (b , d) (a ,₁ c) = (R b a × S d c)

data _₁×₁_ (A B : Set1): Set1 where
  _₁,₁_ : A → B → A ₁×₁ B

_₁⨉₁_ : {A : Set1}{B : Set}{C : Set1}{D : Set} → 
       (B ←₁ A) → (D ←₁ C) → ((B × D) ←₁ (A ₁×₁ C)) 
(R ₁⨉₁ S) (b , d) (a ₁,₁ c) = (R b a × S d c)

proj₁₁ : {A B : Set1} → (A ₁×₁ B) → A
proj₁₁ (a ₁,₁ b) = a
proj₁₂ : {A B : Set1} → (A ₁×₁ B) → B
proj₁₂ (a ₁,₁ b) = b

map-₁×₁ :  {a b c d : Set1}
      → (a → c) → (b → d) → (a ₁×₁ b → c ₁×₁ d)
map-₁×₁ f g (a ₁,₁ b) = (f a ₁,₁ g b) 

⊑-⊓ : ∀ {i} {A : Set i}{B : Set1} → (R S T : B ← A) → 
           R ⊑ S ⊓ T → (R ⊑ S) × (R ⊑ T)
⊑-⊓ R S T R⊑S⊓T = ((λ a b bRa → proj₁ (R⊑S⊓T a b bRa)) ,
                     (λ a b bRa → proj₂ (R⊑S⊓T a b bRa))) -}
