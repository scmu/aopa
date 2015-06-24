module Relations.Coproduct where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Data.Sum      using (_⊎_)
open import Function using (_∘_; id)

open import Sets
open import Relations

open import AlgebraicReasoning.Relations
     using (⊑-begin_; _⊑⟨_⟩_; _⊑∎)


[,]-universal-l-⊑ : ∀ {i} {A B C : Set i} {R : C ← A} {S : C ← B}
                  → [ R , S ] ○ fun inj₁ ⊑ R
[,]-universal-l-⊑ c a (.(inj₁ a) , refl , inj₁ (.a , refl , cRa)) = cRa
[,]-universal-l-⊑ c a (.(inj₁ a) , refl , inj₂ (_ , () , _))

[,]-universal-l-⊒ : ∀ {i} {A B C : Set i} {R : C ← A} {S : C ← B}
                  → [ R , S ] ○ fun inj₁ ⊒ R
[,]-universal-l-⊒ c a cRa = (inj₁ a , refl , inj₁ (a , refl , cRa))

[,]-universal-r-⊑ : ∀ {i} {A B C : Set i} {R : C ← A} {S : C ← B}
                  → [ R , S ] ○ fun inj₂ ⊑ S
[,]-universal-r-⊑ c b (.(inj₂ b) , refl , inj₁ (_ , () , _))
[,]-universal-r-⊑ c b (.(inj₂ b) , refl , inj₂ (.b , refl , cSb)) = cSb

[,]-universal-r-⊒ : ∀ {i} {A B C : Set i} {R : C ← A} {S : C ← B}
                  → [ R , S ] ○ fun inj₂ ⊒ S
[,]-universal-r-⊒ c b cSb = (inj₂ b , refl , inj₂ (b , refl , cSb))


[,]-monotonic : ∀ {i} {A B C : Set i}
                  {R T : C ← A} {S U : C ← B}
                → R ⊑ T → S ⊑ U → [ R , S ] ⊑ [ T , U ]
[,]-monotonic {R = R} {T} {S} {U} R⊑T S⊑U =
   ⊑-begin
     [ R , S ]
   ⊑⟨ ⊑-refl ⟩
     (R ○ (fun inj₁ ˘)) ⊔ (S ○ (fun inj₂ ˘))
   ⊑⟨ ⊔-monotonic (○-monotonic-l R⊑T) (○-monotonic-l S⊑U) ⟩
     (T ○ (fun inj₁ ˘)) ⊔ (U ○ (fun inj₂ ˘))
   ⊑⟨ ⊑-refl ⟩
     [ T , U ]
   ⊑∎
-}
