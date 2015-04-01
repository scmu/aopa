module Relations.Function where

open import Data.Sum      using (_⊎_)
open import Data.Product  using (_×_; _,_; proj₁ ; proj₂)
  renaming (map to map-×)
open import Function using (_∘_; id)

open import Sets
open import Relations

open import AlgebraicReasoning.Equality
open import AlgebraicReasoning.Implications

-- Functions are simple and entire

fun-simple : ∀ {i} {A B : Set i} {f : A → B} 
             → fun f ○ (fun f)˘ ⊑ idR
fun-simple {f = f} b' b (a , fa≡b , fa≡b') = 
   ≡-begin
       b 
   ≡⟨ sym fa≡b ⟩
       f a
   ≡⟨ fa≡b' ⟩
       b'
   ≡∎

fun-entire : ∀ {i} {A B : Set i} {f : A → B} 
             → idR ⊑ (fun f) ˘ ○ fun f
fun-entire {f = f} a' a a≡a' = 
    (f a , refl , cong f (sym a≡a'))

-- Shunting rules

fR⊑S⇒R⊑f˘S : ∀ {i j} {A : Set i} {B C : Set j} 
             → {f : B → C} {R : B ← A} {S : C ← A}
             → fun f ○ R ⊑ S →  R ⊑ (fun f) ˘ ○ S
fR⊑S⇒R⊑f˘S {f = f} {R} {S} =
   ⇒-begin
       fun f ○ R ⊑ S
   ⇒⟨  ○-monotonic-r  ⟩
       (fun f) ˘ ○ fun f ○ R ⊑ (fun f) ˘ ○ S 
   ⇒⟨  ⊑-trans ○-assocr  ⟩
       ((fun f) ˘ ○ fun f) ○ R ⊑ (fun f) ˘ ○ S 
   ⇒⟨  ⊑-trans (○-monotonic-l fun-entire)  ⟩
      idR ○ R ⊑ (fun f) ˘ ○ S
   ⇒⟨  ⊑-trans id-elim-l  ⟩
       R ⊑ (fun f) ˘ ○ S
   ⇒∎

R⊑f˘S⇒fR⊑S : ∀ {i j} {A : Set i} {B C : Set j} {f : B → C} →
     {R : B ← A} → {S : C ← A} →
         R ⊑ (fun f) ˘ ○ S → fun f ○ R ⊑ S
R⊑f˘S⇒fR⊑S {f = f} {R} {S} =
   ⇒-begin
       R ⊑ (fun f) ˘ ○ S
   ⇒⟨  ○-monotonic-r  ⟩
       fun f ○ R ⊑ fun f ○ (fun f) ˘ ○ S
   ⇒⟨  ⊒-trans ○-assocl  ⟩
       fun f ○ R ⊑ (fun f ○ (fun f) ˘) ○ S
   ⇒⟨  ⊒-trans (○-monotonic-l fun-simple)  ⟩
       fun f ○ R ⊑ idR ○ S
   ⇒⟨  ⊒-trans id-intro-l  ⟩
       fun f ○ R ⊑ S
   ⇒∎   

R⊑fS⇒f˘R⊑S : ∀ {i j} {A B : Set i} {C : Set j} 
             → {f : A → B} {R : C ← A} {S : C ← B}
             → R ⊑ S ○ fun f → R ○ (fun f)˘ ⊑ S
R⊑fS⇒f˘R⊑S {f = f} {R} {S} = 
   ⇒-begin
       R ⊑ S ○ fun f
   ⇒⟨ ○-monotonic-l  ⟩
       R ○ (fun f)˘ ⊑ (S ○ fun f) ○ (fun f)˘
   ⇒⟨ ⊒-trans ○-assocr  ⟩
       R ○ (fun f)˘ ⊑ S ○ (fun f ○ (fun f)˘)
   ⇒⟨ ⊒-trans (○-monotonic-r fun-simple) ⟩
       R ○ (fun f)˘ ⊑ S ○ idR
   ⇒⟨ ⊒-trans id-intro-r ⟩
       R ○ (fun f)˘ ⊑ S 
   ⇒∎

R○f˘⊑S⇒R⊑S○f : ∀ {i j} {A : Set i} {B C : Set j}
                → {f : C → B}{R : A ← C}{S : A ← B} 
                → R ○ (fun f) ˘ ⊑ S → R ⊑ S ○ fun f
R○f˘⊑S⇒R⊑S○f {f = f} {R} {S} =
   ⇒-begin
       R ○ (fun f) ˘ ⊑ S
   ⇒⟨  ○-monotonic-l  ⟩
       (R ○ (fun f) ˘) ○ fun f ⊑ S ○ fun f
   ⇒⟨  ⊑-trans ○-assocl   ⟩
       R ○ (fun f) ˘ ○ fun f ⊑ S ○ fun f
   ⇒⟨  ⊑-trans (○-monotonic-r fun-entire)  ⟩
       R ○ idR ⊑ S ○ fun f
   ⇒⟨  ⊑-trans id-elim-r  ⟩
       R ⊑ S ○ fun f
   ⇒∎

-- Functions and products

fun⊑⨉ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
        → {f : A → B} {g : C → D}
        → fun (map-× f g) ⊑ (fun f ⨉ fun g) 
fun⊑⨉ (a , c) (b , d) f⨉gac≡bd = 
   (cong proj₁ f⨉gac≡bd , cong proj₂ f⨉gac≡bd)

⨉⊑fun : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
        → {f : A → B} {g : C → D}
        → (fun f ⨉ fun g) ⊑ fun (map-× f g)
⨉⊑fun {f = f}{g = g} (b , d) (a , c) (fa≡b , gc≡d) = 
   ≡-begin
     (f a , g c)
   ≡⟨ cong (λ b → b , g c) fa≡b ⟩
     (b , g c) 
   ≡⟨ cong (λ d → b , d) gc≡d ⟩ 
     (b , d) 
   ≡∎

fun○-⊑ : ∀ {i j} {A : Set i} {B C : Set j}
         → {g : B → C} {f : A → B}
         → fun g ○ fun f ⊑ fun (g ∘ f)
fun○-⊑ {g = g}{f = f} c a (b , fa≡b , gb≡c) = 
   subst (λ x → g (f a) ≡ x) gb≡c
     (subst (λ x → g (f a) ≡ g x) fa≡b refl)

fun○-⊒ : ∀ {i j} {A : Set i} {B C : Set j}
         → {g : B → C} {f : A → B}
         → fun g ○ fun f ⊒ fun (g ∘ f)
fun○-⊒ {f = f} c a gfa≡c = (f a , refl , gfa≡c)
