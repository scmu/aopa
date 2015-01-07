module Relations.CompChain where

open import Function using (id)
open import Data.Product  using (Σ; _×_; _,_)

open import Sets
open import Relations

data _⇦_ : Set → Set → Set1 where
  _‥ : {A B : Set} → B ← A → B ⇦ A
  _●_ : {A B C : Set} → (C ← B) → (B ⇦ A) → C ⇦ A

infixr 5 _●_

collapse : {A B : Set} → B ⇦ A → B ← A
collapse (R ‥) = R
collapse (R ● Rs) = R ○ collapse Rs

comp : {A B C : Set} → C ⇦ B → B ← A → C ← A
comp (R ‥)    S = R ○ S
comp (R ● Rs) S = R ○ comp Rs S

private
  ⇦-comp : {A B C : Set}(Rs : C ⇦ B){S : B ← A} →
         ∀ {a b c} → S b a → collapse Rs c b → comp Rs S c a
  ⇦-comp (R ‥) {S}{a}{b}{c} bSa cRb = (b , bSa , cRb) 
  ⇦-comp (R ● Rs) {S}{a}{b}{c} bSa (d , dRsb , cRd) = 
      (d , (⇦-comp Rs {S}{a}{b}{d} bSa dRsb , cRd))

  ⇦-extr : {A B C : Set}(Rs : C ⇦ B){S : B ← A} → 
      ∀ {a c} →  
        comp Rs S c a → 
          Σ B (\b →  S b a × collapse Rs c b)
  ⇦-extr (R ‥) {S}{a}{c} (b , bSa , cRb) = (b , bSa , cRb) 
  ⇦-extr (R ● Rs) {S}{a}{c} (d , dRsSa , cRd)
      with ⇦-extr Rs {S}{a}{d} dRsSa 
  ... | (b , bSa , dRsb) = (b , bSa , d , dRsb , cRd) 

⇦-mono-l : {A B C : Set} (Rs Ss : C ⇦ B) → {T : B ← A} → 
      collapse Rs ⊑ collapse Ss →
            comp Rs T ⊑ comp Ss T
⇦-mono-l Rs Ss Rs⊑Ss c a cRsTa   with ⇦-extr Rs cRsTa
... | (b , bTa , cRsb) =  ⇦-comp Ss bTa (Rs⊑Ss c b cRsb)

⇦-mono-r : {A B C : Set} (Rs : C ⇦ B) → {S T : B ← A} →
      S ⊑ T → comp Rs S ⊑ comp Rs T
⇦-mono-r Rs S⊑T c a cRsTa with ⇦-extr Rs cRsTa
... | (b , bSa , cRsb) = ⇦-comp Rs (S⊑T b a bSa) cRsb

⇦-mono : {A B C D : Set} → (Rs : D ⇦ C) → (Ss Ts : C ⇦ B) → 
          collapse Ss ⊑ collapse Ts → {Us : B ← A} →
              comp Rs (comp Ss Us) ⊑ comp Rs (comp Ts Us)
⇦-mono Rs Ss Ts Ss⊑Ts = ⇦-mono-r Rs (⇦-mono-l Ss Ts Ss⊑Ts) 
