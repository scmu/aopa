module Examples.Optimisation.ActSelPJ where
open import Relations using (_←_; _⊑_; _○_; fun; idR; _⨉_; _⊔_)
open import Data.Product using (_×_; _,_; ∃; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Sets          using  (_≡_; ≡-refl; ≡-subst; ≡-sym; ≡-cong)

_monotonicOn_ : {A B : Set} -> (S : A ← (B × A)) -> (⊴ : A ← A) -> Set
S monotonicOn ⊴ = S ○ (idR ⨉ ⊴)   ⊑   ⊴ ○ S


module Currying {Y : Set} (P : Y -> Set) (Q : Set) where
  curry : (∃ (\y ->   P y) -> Q) -> 
          ((y : Y) -> P y  -> Q)
  curry f y py = f (y , py) 
  
  uncurry : ((y : Y) -> P y  -> Q) ->
            (∃ (\y ->   P y) -> Q)
  uncurry f (y , py) = f y py 

module SimlifyMonotonicity{A B : Set}(S : A ← (B × A))(⊴ : A ← A) where
  open import Relation.Binary.PropositionalEquality1 
  open import AlgebraicReasoning.Relations

  step1 : (S monotonicOn ⊴) ≡₁
              ((ba : B × A)     (a : A) ->
               ∃ (\ba' -> ((idR ⨉ ⊴) ba ba') × (S ba' a)) ->
               ∃ (\a'' -> (S ba a''          ×  ⊴ a'' a)))
  step1 = refl


  step2 :     ((ba : B × A)     (a : A) ->
               ∃ (\ba' -> ((idR ⨉ ⊴) ba ba') × (S ba' a)) ->
               ∃ (\a'' -> (S ba a''          ×  ⊴ a'' a)))
          ->  ((ba : B × A)     (a : A) (ba' : B × A) ->
                          ((idR ⨉ ⊴) ba ba') × (S ba' a) ->
               ∃ (\a'' -> (S ba a''          ×  ⊴ a'' a)))
  step2 g ba a = curry (g ba a)  
    where open Currying (\ba' -> ((idR ⨉ ⊴) ba ba') × (S ba' a)) 
                        (∃ (\a'' -> (S ba a'' ×  ⊴ a'' a)))


open import Data.List using (List; _∷_)
open import Data.List.Fold using (nil; cons)

open import Relations.Coreflexive using (_¿)

postulate Act : Set
postulate comp : (Act × List Act) -> Set
C = comp ¿ 
-- postulate C : (Act × List Act) ← (Act × List Act)
postulate ⊴ : List Act ← List Act
outr : {A B : Set} -> B ← (A × B)
outr = fun proj₂

A = Act
B = List A
-- Not needed: postulate ⊴-refl : {b : B} -> ⊴ b b

S : B ← (A × B)
S = outr ⊔ (cons ○ C)

open import Relation.Binary.PropositionalEquality1
simp3 :((ab : A × B)     (b : B) (ab' : A × B) ->
          ((idR ⨉ ⊴) ab ab') × ((outr ab' b) ⊎ ((cons ○ C) ab' b)) ->
         ∃ (\b'' -> (S ab b''          ×  ⊴ b'' b)))
     ≡₁
       ((ab : A × B)     (b : B) (ab' : A × B) ->
                    ((idR ⨉ ⊴) ab ab') × (S ab' b) ->
         ∃ (\b'' -> (S ab b''          ×  ⊴ b'' b)))
simp3 = refl 

simp4 :
       ((a : A)  -> (qs  : B) -> let ab = a , qs in
        (b : B) 
        (a' : A) -> (qs' : B) -> let ab' = a' , qs' in
          ((a ≡ a') × (⊴ qs qs')) × ((qs' ≡ b) ⊎ ((cons ○ C) ab' b)) ->
         ∃ (\b'' -> (((qs ≡ b'') ⊎ ((cons ○ C) ab b''))  ×  ⊴ b'' b)))
     ->
       ((ab : A × B)     (b : B) (ab' : A × B) ->
          ((idR ⨉ ⊴) ab ab') × ((outr ab' b) ⊎ ((cons ○ C) ab' b)) ->
         ∃ (\b'' -> (S ab b'' ×  ⊴ b'' b)))
        
simp4 f (a , qs) b (a' , qs') = f a qs b a' qs' 

simp5 :
       ((a : A) (qs  : B) (b : B) (qs' : B) -> 
          (⊴ qs qs') × ((qs' ≡ b) ⊎ ((cons ○ C) (a , qs') b)) ->
         ∃ (\b'' ->  (((qs ≡ b'') ⊎ ((cons ○ C) (a , qs) b''))  ×  ⊴ b'' b)))
     ->
       ((a : A)  -> (qs  : B) -> let ab = a , qs in
        (b : B) 
        (a' : A) -> (qs' : B) -> let ab' = a' , qs' in
          ((a ≡ a') × (⊴ qs qs')) × ((qs' ≡ b) ⊎ ((cons ○ C) ab' b)) ->
         ∃ (\b'' -> (((qs ≡ b'') ⊎ ((cons ○ C) ab b''))  ×  ⊴ b'' b)))
        
simp5 f a qs b .a qs' ((≡-refl , ⊴qsqs') , rest)
  = f a qs b qs' (⊴qsqs' , rest)

simp6 : -- a:=a, qs:=ys, qs':=xs, swap around argument order
       (forall ys b a xs -> 
          (⊴ ys xs) × ((xs ≡ b) ⊎ ((cons ○ C) (a , xs) b)) ->
         ∃ (\b'' ->  (((ys ≡ b'') ⊎ ((cons ○ C) (a , ys) b''))  ×  ⊴ b'' b)))
     ->
       ((a : A) (qs  : B) (b : B) (qs' : B) -> 
          (⊴ qs qs') × ((qs' ≡ b) ⊎ ((cons ○ C) (a , qs') b)) ->
         ∃ (\b'' ->  (((qs ≡ b'') ⊎ ((cons ○ C) (a , qs) b''))  ×  ⊴ b'' b)))

simp6 f a qs b qs' = f qs b a qs'

simp7 : -- Here we need that C is coreflexive
       (forall ys zs a xs -> 
          (⊴ ys xs) × ((xs ≡ zs) ⊎ (zs ≡ a ∷ xs  ×  comp (a , xs))) ->
         ∃ (\b'' ->  (((ys ≡ b'') ⊎ ((cons ○ C) (a , ys) b''))  ×  ⊴ b'' zs)))
     ->
       (forall ys b a xs -> 
          (⊴ ys xs) × ((xs ≡ b) ⊎ ((cons ○ C) (a , xs) b)) ->
         ∃ (\b'' ->  (((ys ≡ b'') ⊎ ((cons ○ C) (a , ys) b''))  ×  ⊴ b'' b)))
        
simp7 f ys zs a xs (⊴ysxs , inj₁ xs≡zs) = f ys zs a xs (⊴ysxs , inj₁ xs≡zs)
simp7 f ys .(a ∷ xs) .a .xs (⊴ysxs , inj₂ ((a , xs) , (≡-refl , p) , ≡-refl))  = f ys (a ∷ xs) a xs (⊴ysxs , inj₂ (≡-refl , p))  

simp8 : 
       (forall ys zs a xs -> 
          (⊴ ys xs) × ((xs ≡ zs) ⊎ (zs ≡ a ∷ xs  ×  comp (a , xs))) ->

         ((⊴ ys zs) ⊎ (⊴ (a ∷ ys) zs  ×  comp (a , ys)))
       ->
         ∃ (\b'' ->  (((ys ≡ b'') ⊎ ((cons ○ C) (a , ys) b''))  ×  ⊴ b'' zs)))

simp8 ys zs a xs p (inj₁ ⊴yszs)    = ys , inj₁ ≡-refl , ⊴yszs   
simp8 ys zs a xs p (inj₂ (lt , c)) = a ∷ ys ,  inj₂ ((a , ys) , (≡-refl , c) , ≡-refl) , lt   


-- PJ: OK, now I've got it!
