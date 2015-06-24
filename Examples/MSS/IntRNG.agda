module Examples.MSS.IntRNG where

open import Data.Bool
open import Data.Nat using (ℕ; suc; zero)
                  renaming ( _<_  to _<'_ )
open import Data.Integer
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


-- module ChainR = Logic.ChainReasoning.Poly.Homogenous _≡_ (\x -> refl) (\x y z -> trans)
--open ChainR

_↑_ : ℤ → ℤ → ℤ
a ↑ b with b ≤? a
a ↑ b | yes p = a
a ↑ b | no ¬p = b

{-
lemmaT : {A : Set}{cond : Bool}{x y : A} ->
          cond ≡ true -> if cond then x else y ≡ x
lemmaT refl = refl

lemmaF : {A : Set}{cond : Bool}{x y : A} ->
          cond ≡ false -> if cond then x else y ≡ y
lemmaF refl = refl

dec : (b : Bool) -> (b ≡ true) \/ (b ≡ false)
dec true = \/-IL refl
dec false = \/-IR refl
-}

-- JK: unavoidable partiality?

postulate
 ↑assoc : (a b c : ℤ) → ((a ↑ b) ↑ c) ≡ (a ↑ (b ↑ c))
{-            
 ↑assoc a b c with dec (a < b) | dec (a < c) | dec (b < c)
... | \/-IL a<b | \/-IL a<c | \/-IL b<c =
  chain> (a ↑ b) ↑ c
     === b ↑ c by cong (\x -> x ↑ c) (lemmaT a<b)
     === c by (lemmaT b<c)
     === a ↑ (b ↑ c) by sym
         ( chain> a ↑ (b ↑ c)
              === a ↑ c by cong (\x -> a ↑ x) (lemmaT b<c)
              === c by lemmaT a<c )
... | \/-IL a<b | \/-IL a<c | \/-IR b≮c =
  chain> (a ↑ b) ↑ c
     === b ↑ c by cong (\x -> x ↑ c) (lemmaT a<b)
     === b by (lemmaF b≮c)
     === a ↑ (b ↑ c) by sym
         ( chain> a ↑ (b ↑ c)
              === a ↑ b by cong (\x -> a ↑ x) (lemmaF b≮c)
              === b by lemmaT a<b )
-- ... | \/-IL a<b | \/-IR a<c | \/-IL b<c = ⊥
... | \/-IL a<b | \/-IR a≮c | \/-IR b≮c =
  chain> (a ↑ b) ↑ c
     === b ↑ c by cong (\x -> x ↑ c) (lemmaT a<b)
     === b by (lemmaF b≮c)
     === a ↑ (b ↑ c) by sym
         ( chain> a ↑ (b ↑ c)
              === a ↑ b by cong (\x -> a ↑ x) (lemmaF b≮c)
              === b by lemmaT a<b )
... | \/-IR a≮b | \/-IL a<c | \/-IL b<c =
  chain> (a ↑ b) ↑ c
     === a ↑ c by cong (\x -> x ↑ c) (lemmaF a≮b)
     === c by (lemmaT a<c)
     === a ↑ (b ↑ c) by sym
         ( chain> a ↑ (b ↑ c)
              === a ↑ c by cong (\x -> a ↑ x) (lemmaT b<c)
              === c by lemmaT a<c )
-- ... | \/-IR a<b | \/-IL a<c | \/-IR b<c = ⊥
... | \/-IR a≮b | \/-IR a≮c | \/-IL b<c =
  chain> (a ↑ b) ↑ c
     === a ↑ c by cong (\x -> x ↑ c) (lemmaF a≮b)
     === a by (lemmaF a≮c)
     === a ↑ (b ↑ c) by sym
         ( chain> a ↑ (b ↑ c)
              === a ↑ c by cong (\x -> a ↑ x) (lemmaT b<c)
              === a by lemmaF a≮c )
... | \/-IR a≮b | \/-IR a≮c | \/-IR b≮c =
  chain> (a ↑ b) ↑ c
     === a ↑ c by cong (\x -> x ↑ c) (lemmaF a≮b)
     === a by (lemmaF a≮c)
     === a ↑ (b ↑ c) by sym
         ( chain> a ↑ (b ↑ c)
              === a ↑ b by cong (\x -> a ↑ x) (lemmaF b≮c)
              === a by lemmaF a≮b )
-}


0+a≡a : {a : ℤ} → (+ 0) + a ≡ a
0+a≡a { -[1+ n ]} = refl
0+a≡a {+ n} = refl

postulate
 +distr↑ : (a b c : ℤ) →
           (a + (b ↑ c)) ≡ ((a + b) ↑ (a + c))

{-
+distr↑ (pos 0) b c =
    chain> pos 0 + (b ↑ c)
       === b ↑ c               by 0+a≡a 
       === ((pos 0 + b) ↑ c)   by cong (\d -> d ↑ c) (sym 0+a≡a)
       === ((pos 0 + b) ↑ (pos 0 + c))  by cong (\d -> (pos 0 + b) ↑ d) (sym 0+a≡a)
-}
