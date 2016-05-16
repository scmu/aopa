module Relations.Minimum where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Function  using (id; _$_; _∘_)
open import Data.Product  using (Σ; _×_; _,_; proj₁; proj₂)
         renaming (map to map-×)

open import Sets
open import Relations
open import Relations.Factor
open import Relations.Converse

open import AlgebraicReasoning.Relations
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Equivalence

min : {A : Set} → (A ← A) → (A ← ℙ A)
min R = ∈ ⊓ (R / ∋)

max : {A : Set} → (A ← A) → (A ← ℙ A)
max R = min (R ˘)

-- min-universal : X ⊑ min R ₁∘ Λ S ⇔ (X ⊑ S  ×  X ○ (S ˘) ⊑ R)

min-universal-⇒ : {A B : Set} →
   {R : A ← A} {S : A ← B} {X : A ← B} →
     X ⊑ min R ₁∘ Λ S → (X ⊑ S  ×  X ○ (S ˘) ⊑ R)
min-universal-⇒ {R = R} {S} {X} =
   ⇒-begin
     X ⊑ min R ₁∘ Λ S
   ⇒⟨  ⇒-refl  ⟩
     X ⊑ (∈ ⊓ (R / ∋)) ₁∘ Λ S
   ⇒⟨  ⊒-trans (⊓-Λ-distr-⊑ ∈ (R / ∋)) ⟩
     X ⊑ (∈ ₁∘ Λ S) ⊓ ((R / ∋) ₁∘ Λ S)
   ⇒⟨  ⊑-⊓ X (∈ ₁∘ Λ S) ((R / ∋) ₁∘ Λ S) ⟩
     (X ⊑ ∈ ₁∘ Λ S  ×  X ⊑ (R / ∋) ₁∘ Λ S)
   ⇒⟨  ⇒-refl  ⟩
     (X ⊑ S  ×  X ⊑ (R / ∋) ₁∘ Λ S)
   ⇒⟨  ⇒-refl  ⟩   -- /∋○Λ-cancelation-⊑ is deducible by Agda
     (X ⊑ S  ×  X ⊑ (R / (S ˘)))
   ⇒⟨  map-× id /-universal-⇒ ⟩
     (X ⊑ S  ×  X ○ (S ˘) ⊑ R)
   ⇒∎

min-universal-⇐ : {A B : Set} →
   {R : A ← A} {S : A ← B} {X : A ← B} →
     (X ⊑ S  ×  X ○ (S ˘) ⊑ R) → X ⊑ min R ₁∘ Λ S
min-universal-⇐ {R = R} {S} {X} =
   ⇐-begin
     X ⊑ min R ₁∘ Λ S
   ⇐⟨  ⇐-refl  ⟩
     X ⊑ (∈ ⊓ (R / ∋)) ₁∘ Λ S
   ⇐⟨ ⊒-trans (⊓-Λ-distr-⊒ ∈ (R / ∋)) ⟩
     X ⊑ (∈ ₁∘ Λ S) ⊓ ((R / ∋) ₁∘ Λ S)
   ⇐⟨ ⊓-universal-⇐ ⟩
     (X ⊑ ∈ ₁∘ Λ S  ×  X ⊑ (R / ∋) ₁∘ Λ S)
   ⇐⟨  ⇐-refl  ⟩
     (X ⊑ S  ×  X ⊑ (R / ∋) ₁∘ Λ S)
   ⇐⟨  ⇐-refl  ⟩   -- /∋○Λ-cancelation-⊒ is deducible by Agda
     (X ⊑ S  ×  X ⊑ (R / (S ˘)))
   ⇐⟨  map-× id /-universal-⇐ ⟩
     (X ⊑ S  ×  X ○ (S ˘) ⊑ R)
   ⇐∎

min-universal : {A B : Set} →
   {R : A ← A} {S : A ← B} {X : A ← B} →
      X ⊑ min R ₁∘ Λ S  ⇔  (X ⊑ S  ×  X ○ (S ˘) ⊑ R)
min-universal = (min-universal-⇒ , min-universal-⇐)

min-monotonic : {A B : Set} {R S : A ← A} {T : A ← B} →
  R ⊑ S → min R ₁∘ Λ T ⊑ min S ₁∘ Λ T
min-monotonic {_}{_} {R} {S} {T} =
  ⇐-begin
    min R ₁∘ Λ T ⊑ min S ₁∘ Λ T
  ⇐⟨ min-universal-⇐ ⟩
    (min R ₁∘ Λ T ⊑ T × (min R ₁∘ Λ T) ○ T ˘ ⊑ S)
  ⇐⟨ (λ next-line → (proj₁ $ min-universal-⇒ ⊑-refl) , next-line) ⟩
    (min R ₁∘ Λ T) ○ T ˘ ⊑ S
  ⇐⟨ ⊑-trans $ ○-monotonic-l $
        /-universal-⇐ $ proj₂ $ min-universal-⇒ ⊑-refl ⟩
    (R / (T ˘)) ○ T ˘ ⊑ S
  ⇐⟨ ⊑-trans $ /-universal-⇒ ⊑-refl ⟩
    R ⊑ S
  ⇐∎

max-monotonic : {A B : Set} {R S : A ← A} {T : A ← B} →
  R ⊑ S → max R ₁∘ Λ T ⊑ max S ₁∘ Λ T
max-monotonic = min-monotonic ∘ ˘-monotonic-⇐

corefl-propagation-⊑ : {A B : Set} {R : B ← B} {S : B ← A} {C : A ← A} →
  C ⊑ idR → (min R ₁∘ Λ S) ○ C ⊑ (min R ₁∘ Λ (S ○ C)) ○ C
corefl-propagation-⊑ {A} {B} {R} {S} {C} C⊑idR b a (a' , a'Ca , bSa' , ∀b'-b'Sa'⇒bRb')
  with C⊑idR a' a a'Ca
corefl-propagation-⊑ {A} {B} {R} {S} {C} C⊑idR b a (.a , aCa , bSa , ∀b'-b'Sa⇒bRb')
  | refl = a , aCa , (a , aCa , bSa) , see-below
  where see-below : (b' : B) → Σ A (λ a' → C a' a × S b' a') → R b b'
        see-below b' (a' , a'Ca , b'Sa') with C⊑idR a' a a'Ca
        see-below b' (.a , aCa , b'Sa) | refl = ∀b'-b'Sa⇒bRb' b' b'Sa

corefl-propagation-⊒ : {A B : Set} {R : B ← B} {S : B ← A} {C : A ← A} →
  C ⊑ idR → (min R ₁∘ Λ S) ○ C ⊒ (min R ₁∘ Λ (S ○ C)) ○ C
corefl-propagation-⊒ C⊑idR b a (a' , a'Ca , (a'' , a''Ca' , bSa'') , ∀b'-xCa'∧b'Sx⇒bRb')
  with C⊑idR a' a a'Ca | C⊑idR a'' a' a''Ca'
corefl-propagation-⊒ C⊑idR b a (.a , aCa , (.a , aCa₂ , bSa) , ∀b'-xCa∧b'Sx⇒bRb')
  | refl | refl = a , aCa , bSa , λ b' b'Sa → ∀b'-xCa∧b'Sx⇒bRb' b' (a , aCa , b'Sa)

minΛ-cong-⊒ : {A B : Set} {R : B ← B} {S T : B ← A} →
  (S ≑ T) → min R ₁∘ Λ S ⊒ min R ₁∘ Λ T
minΛ-cong-⊒ {R = R} {S} {T} (S⊑T , S⊒T) =
 (⇐-begin
    min R ₁∘ Λ T ⊑ min R ₁∘ Λ S
  ⇐⟨ min-universal-⇐ ⟩
    (min R ₁∘ Λ T ⊑ S × (min R ₁∘ Λ T) ○ S ˘ ⊑ R)
  ⇐⟨ map-× (⊑-trans $ proj₁ $ min-universal-⇒ ⊑-refl)
            (⊑-trans $ ○-monotonic-l $ /-universal-⇐ $ proj₂ $ min-universal-⇒ ⊑-refl) ⟩
    (T ⊑ S × (R / (T ˘)) ○ S ˘ ⊑ R)
  ⇐⟨ (λ next-line → S⊒T , next-line) ⟩
    (R / (T ˘)) ○ S ˘ ⊑ R
  ⇐⟨ ⊑-trans $ ○-monotonic-l $ /-anti-monotonic $ ˘-monotonic-⇐ S⊑T ⟩
    (R / (S ˘)) ○ S ˘ ⊑ R
  ⇐⟨ ⊑-trans $ /-universal-⇒ ⊑-refl ⟩
    R ⊑ R
  ⇐∎) ⊑-refl

thin : {A : Set} → (A ← A) → (ℙ A ← ℙ A)
thin Q = (∈ ﹨ ∈) ⊓ ((∋ ○ Q) / ∋)

-- thin-universal-⇐ :
--    ⊑ thin Q ₁∘ Λ S ⇔ (X ⊑ ∈ ﹨ S  ×  X ○ (S ˘) ⊑ ∋ ○ Q)

thin-universal-⇐ : {A B : Set} →
   {Q : A ← A} {S : A ← B} → (X : ℙ A ← B) →
     X ⊑ thin Q ₁∘ Λ S → (X ⊑ ∈ ﹨ S  ×  X ○ (S ˘) ⊑ ∋ ○ Q)
thin-universal-⇐ {A = A} {B} {Q = Q}{S} X =
   ⇒-begin
     X ⊑ thin Q ₁∘ Λ S
   ⇒⟨  ⇒-refl  ⟩
     X ⊑ ((∈ ﹨ ∈) ⊓ ((∋ ○ Q) / ∋)) ₁∘ Λ S
   ⇒⟨  ⊒-trans (⊓-Λ-distr-⊑ (∈ ﹨ ∈) ((∋ ○ Q) / ∋))   ⟩
     X ⊑ ((∈ ﹨ ∈) ₁∘ Λ S) ⊓ (((∋ ○ Q) / ∋) ₁∘ Λ S)
   ⇒⟨  ⊑-⊓ X ((∈ ﹨ ∈) ₁∘ Λ S) (((∋ ○ Q) / ∋) ₁∘ Λ S)   ⟩
     (X ⊑ (∈ ﹨ ∈) ₁∘ Λ S  ×  X ⊑ ((∋ ○ Q) / ∋) ₁∘ Λ S)
   ⇒⟨  ⇒-refl  ⟩
     (X ⊑ ∈ ﹨ S  ×  X ⊑ ((∋ ○ Q) / ∋) ₁∘ Λ S)
   ⇒⟨  ⇒-refl   ⟩
     (X ⊑ ∈ ﹨ S  ×  X ⊑ (∋ ○ Q) / (S ˘))
   ⇒⟨  map-× (λ x → x) univ ⟩
     (X ⊑ ∈ ﹨ S  ×  X ○ (S ˘) ⊑ ∋ ○ Q)
   ⇒∎
  where /-universal-⇒' : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k}
                        → {R : C ← B ⊣ (l ⊔ℓ j ⊔ℓ i)} {S : B ← A ⊣ (l ⊔ℓ j ⊔ℓ i)}
                          {T : C ← A ⊣ (l ⊔ℓ j ⊔ℓ i)}
                        → R ⊑ T / S →  R ○ S ⊑ T
        /-universal-⇒' R⊑T/S c a (b , bSa , cRb) = R⊑T/S c b cRb a bSa
          -- Same as /-universal-⇒ in Relations.Factor, with a more
          -- polymorphic type.

        univ : X ⊑ (∋ ○ Q) / (S ˘) → X ○ S ˘ ⊑ ∋ ○ Q
        univ = /-universal-⇒' {i = zero} {zero} {suc zero} {zero}
                {A = A} {B = B} {C = A → Set} {R = X} {S = S ˘} {T = ∋ ○ Q}
