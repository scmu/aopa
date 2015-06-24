module Examples.MSS.List+ where

open import Sets using (_≡_; refl; sym; cong)
open import Function
open import Relations.Function
open import AlgebraicReasoning.Equality
open import AlgebraicReasoning.ExtensionalEquality

data List⁺ (A : Set) : Set where
  [_]⁺ : A → List⁺ A
  _∷⁺_ : A → List⁺ A → List⁺ A

infixr 50 _∷⁺_ 

foldr⁺ : {A B : Set} → (A → B → B) → (A → B) → List⁺ A → B
foldr⁺ f g [ a ]⁺   = g a
foldr⁺ f g (a ∷⁺ x) = f a (foldr⁺ f g x)

map⁺ : {A B : Set} → (A → B) → List⁺ A → List⁺ B
map⁺ f = foldr⁺ (λ a x → f a ∷⁺ x) ([_]⁺ ∘ f)

_++⁺_ : {A : Set} → List⁺ A → List⁺ A → List⁺ A
x ++⁺ y = foldr⁺ _∷⁺_ (λ a → a ∷⁺ y) x

concat⁺ : {A : Set} → List⁺ (List⁺ A) → List⁺ A
concat⁺ = foldr⁺ _++⁺_ id 

foldr⁺-fusion : {A B C : Set} →  
  (h : B → C) → {f : A → B → B} → {g : A → C → C} → {k : A → B} → {l : A → C} →
   (∀ a b → h (f a b) ≡ g a (h b)) →
      (h ∘ k ≐ l) →
         h ∘ foldr⁺ f k  ≐ foldr⁺ g l
foldr⁺-fusion h {f} {g} {k} {l} _ q [ a ]⁺   = q a
foldr⁺-fusion h {f} {g} {k} {l} p q (a ∷⁺ x) =
     ≡-begin 
         h (foldr⁺ f k (a ∷⁺ x))
     ≡⟨ refl ⟩ 
         h (f a (foldr⁺ f k x)) 
     ≡⟨ p a (foldr⁺ f k x)  ⟩ 
         g a (h (foldr⁺ f k x)) 
     ≡⟨ cong (g a) (foldr⁺-fusion h p q x) ⟩ 
         g a (foldr⁺ g l x) 
     ≡⟨ refl ⟩ 
         foldr⁺ g l (a ∷⁺ x) 
     ≡∎

foldr⁺-fusion' : {A B C : Set} →  
  (h : B → C) → {f : A → B → B} → {g : A → C → C} → {k : A → B} →
   (∀ a b → h (f a b) ≡ g a (h b)) →
        h ∘ foldr⁺ f k ≐ foldr⁺ g (h ∘ k)
foldr⁺-fusion' h {f} {g} {k} p x = 
   foldr⁺-fusion h {f} {g} {k} {h ∘ k} p (λ _ → refl) x

idIsFold⁺ : {A : Set} → (x : List⁺ A) → 
               (id x ≡ foldr⁺ _∷⁺_ [_]⁺ x)
idIsFold⁺ [ a ]⁺ = refl 
idIsFold⁺ (a ∷⁺ x) = 
     ≡-begin
         a ∷⁺ x 
     ≡⟨ cong (_∷⁺_ a) (idIsFold⁺ x) ⟩ 
         a ∷⁺ foldr⁺ _∷⁺_ [_]⁺ x
     ≡⟨ refl ⟩ 
         foldr⁺ _∷⁺_ [_]⁺ (a ∷⁺ x)
     ≡∎

map⁺-compose : {A B C : Set} → {g : B → C} → {f : A → B} → 
                 (map⁺ (g ∘ f) ≐ (map⁺ g ∘ map⁺ f))
map⁺-compose {A} {B} {C} {g} {f} = 
     ≐-begin
         map⁺ (g ∘ f)
     ≐⟨ (λ x → cong (map⁺ (g ∘ f)) (idIsFold⁺ x)) ⟩ 
         map⁺ (g ∘ f) ∘ foldr⁺ _∷⁺_ [_]⁺ 
     ≐⟨ foldr⁺-fusion' (map⁺ (g ∘ f)) (λ _ _ → refl)  ⟩ 
         foldr⁺ (λ a y → g (f a) ∷⁺ y) ([_]⁺ ∘ g ∘ f)
     ≐⟨ ≐-sym (foldr⁺-fusion' (map⁺ g) (λ _ _ → refl)) ⟩ 
         map⁺ g ∘ foldr⁺ (λ a y → f a ∷⁺ y) ([_]⁺ ∘ f)
     ≐⟨ ≐-refl ⟩ 
         map⁺ g ∘ map⁺ f
     ≐∎
 
map⁺-cat⁺ : {A B : Set} → {f : A → B} → (x : List⁺ A) → {y : List⁺ A} →
      map⁺ f (x ++⁺ y) ≡ (map⁺ f x ++⁺ map⁺ f y)
map⁺-cat⁺ {A} {B} {f} x {y} = 
     ≡-begin
        map⁺ f (x ++⁺ y) 
     ≡⟨ refl ⟩ 
        map⁺ f (foldr⁺ _∷⁺_ (λ a → a ∷⁺ y) x)
     ≡⟨ foldr⁺-fusion' (map⁺ f) (λ _ _ → refl) x ⟩ 
        foldr⁺ (λ a z → f a ∷⁺ z) (λ a → f a ∷⁺ map⁺ f y) x
     ≡⟨ sym (foldr⁺-fusion' (λ z → z ++⁺ map⁺ f y) (λ _ _ → refl) x)  ⟩ 
        foldr⁺ (λ a z → f a ∷⁺ z) ([_]⁺ ∘ f) x ++⁺ (map⁺ f y) 
     ≡⟨ refl ⟩ 
        map⁺ f x ++⁺ map⁺ f y 
     ≡∎

concat⁺-map⁺ : {A B : Set} → {f : A → B} → 
         (concat⁺ ∘ map⁺ (map⁺ f) ≐ map⁺ f ∘ concat⁺)
concat⁺-map⁺ {A} {B} {f}  = 
     ≐-begin
          concat⁺ ∘ map⁺ (map⁺ f)
     ≐⟨ ≐-refl ⟩ 
          concat⁺ ∘ foldr⁺ (λ x ys → map⁺ f x ∷⁺ ys) ([_]⁺ ∘ map⁺ f)
     ≐⟨ foldr⁺-fusion' concat⁺ (λ _ _ → refl) ⟩ 
         foldr⁺ (λ x xs → map⁺ f x ++⁺ xs) (map⁺ f)
     ≐⟨ ≐-sym (foldr⁺-fusion' (map⁺ f) (λ z w → map⁺-cat⁺ z))  ⟩ 
         map⁺ f ∘ concat⁺
     ≐∎

foldr⁺-eq : {A B : Set} → {f g : A → B → B} → {h k : A → B} →
             (∀ a → ∀ b → f a b ≡ g a b) →
              h ≐ k → 
               foldr⁺ f h ≐ foldr⁺ g k
foldr⁺-eq {A} {B} {f} {g} {h} {k} f≡g h≡k =
     ≐-begin
         foldr⁺ f h
     ≐⟨ (λ x → cong (foldr⁺ f h) (idIsFold⁺ x)) ⟩ 
         foldr⁺ f h ∘ foldr⁺ _∷⁺_ [_]⁺ 
     ≐⟨ foldr⁺-fusion (foldr⁺ f h) (λ a x → f≡g a (foldr⁺ f h x)) h≡k  ⟩ 
         foldr⁺ g k 
     ≐∎

map⁺-eq : {A B : Set} → {f g : A → B} →
           f ≐ g → map⁺ f ≐ map⁺ g
map⁺-eq {A} {B} {f} {g} f≐g = 
     ≐-begin
         map⁺ f
     ≐⟨ ≐-refl ⟩ 
         foldr⁺ (λ a y → f a ∷⁺ y) ([_]⁺ ∘ f)
     ≐⟨ foldr⁺-eq (λ a y → cong (λ b → b ∷⁺ y) (f≐g a)) (λ a → cong [_]⁺ (f≐g a)) ⟩ 
         foldr⁺ (λ a y → g a ∷⁺ y) ([_]⁺ ∘ g)
     ≐⟨ ≐-refl ⟩ 
         map⁺ g
     ≐∎
