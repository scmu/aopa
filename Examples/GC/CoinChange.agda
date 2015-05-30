module Examples.GC.CoinChange where

open import Level renaming (zero to lzero; _⊔_ to _⊔l_; suc to lsuc)
open import Sets
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃)
open import Data.Nat using (ℕ; _+_; _≤_; _≥_; zero; suc; s≤s; z≤n)
open import Function using (const; _∘_)
open import Relation.Binary

open import Relations
open import Relations.Shrink
open import Data.Generic

open import Examples.GC.Relations
open import Examples.GC.List

open import AlgebraicReasoning.Implications

data Coin : Set where
  1p : Coin
  2p : Coin
  5p : Coin
  10p : Coin

val : Coin  → ℕ
val 1p = 1
val 2p = 2
val 5p = 5
val 10p = 10

_≤c_ : Coin ← Coin
_≤c_ = fun val ˘ ○ _≤_ ○ fun val

_≥c_ : Coin ← Coin
_≥c_ = _≤c_ ˘

liftc : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
      → ((A × B) → C) → (Fst {i} {j} A × Snd {i} {j} B → C)
liftc f (fst x , snd y) = f (x , y)

liftC : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
      → (C ← (A × B) ⊣ lzero) → (C ← (Fst {i} {j} A × Snd {i} {j} B))
liftC R z (fst x , snd y) = R z (x , y)

sumc : ℕ ← List Coin
sumc =  ⦇ [ fun (const zero) ,
            fun (liftc plus) ○ bimapR _ (fun val) idR ] ⦈ 
  where plus : ℕ × ℕ → ℕ
        plus (m , n) = m + n

bound : Coin ← List Coin
bound = ⦇ [ fun (const 1p) ,
            liftC ((_≥c_ ○ fun proj₁) ⊓ (_≥c_ ○ fun proj₂)) ] ⦈

S : (ℕ × Coin) ← ⟦ ListF ⟧ Coin (ℕ × Coin)
S = [ ⟨ fun (const 0) , Π ⟩ {-fun (const (0 , 1p)) -} , liftC ⟨ plus , raise ⟩ ]
  where plus : ℕ ← (Coin × ℕ × Coin)
        plus m (c , n , b) = (c ≡ b) × (m ≡ val c + n)
        
        raise : Coin ← (Coin × ℕ × Coin)
        raise b' (c , n , b) = (b' ≥c c) × (c ≥c b)

sumbound : (ℕ × Coin) ← List Coin
sumbound = ⦇ S ⦈

Q : ⟦ ListF ⟧ Coin (ℕ × Coin) ← ⟦ ListF ⟧ Coin (ℕ × Coin)
Q (inj₁ tt) (inj₁ tt) = ⊤
Q (inj₁ tt) (inj₂ y) = ⊥
Q (inj₂ x) (inj₁ tt) = ⊥
Q (inj₂ (fst c , snd x)) (inj₂ (fst d , snd y)) = c ≥c d

-- some properties of ≤

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-step : ∀ {n m} → n ≤ m → n ≤ suc m
≤-step {zero} x = z≤n
≤-step {suc n} {zero} ()
≤-step {suc n} {suc m} (s≤s n≤m) = s≤s (≤-step n≤m)

≤-steps : ∀ {m} → (k : ℕ) → m ≤ k + m
≤-steps zero = ≤-refl
≤-steps (suc k) = ≤-step (≤-steps k)

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n _ = z≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

≤c-trans : ∀ {c d e} → c ≤c d → d ≤c e → c ≤c e
≤c-trans {c}{d}{e} (._ , (._ , refl , c≤d) , refl) (._ , (._ , refl , d≤e) , refl) = (val c , (val e , refl , ≤-trans c≤d d≤e) , refl)

1≱2 : 1 ≥ 2 → ⊥
1≱2 (s≤s ())

-- ordering between coins

1p≥1p : 1p ≥c 1p
1p≥1p = (1 , (1 , refl , s≤s z≤n) , refl)

2p≥1p : 2p ≥c 1p
2p≥1p = (1 , (2 , refl , s≤s z≤n) , refl)

2p≥2p : 2p ≥c 2p
2p≥2p = (2 , (2 , refl , ≤-refl) , refl)

5p≥1p : 5p ≥c 1p
5p≥1p = (1 , (5 , refl , s≤s z≤n) , refl)

5p≥2p : 5p ≥c 2p
5p≥2p = (2 , (5 , refl , s≤s (s≤s z≤n)) , refl)

10p≥1p : 10p ≥c 1p
10p≥1p = (1 , (10 , refl , s≤s z≤n) , refl)

10p≥2p : 10p ≥c 2p
10p≥2p = (2 , (10 , refl , s≤s (s≤s z≤n)) , refl)

10p≥5p : 10p ≥c 5p
10p≥5p = (5 , (10 , refl , s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) , refl)

1p≱2p : (1p ≥c 2p) → ⊥
1p≱2p (.2 , (.1 , refl , s≤s ()) , refl)

1p≱5p : (1p ≥c 5p) → ⊥
1p≱5p (.5 , (.1 , refl , s≤s ()) , refl)

2p≱5p : (2p ≥c 5p) → ⊥
2p≱5p (.5 , (.2 , refl , s≤s (s≤s ())) , refl)

1p≱10p : (1p ≥c 10p) → ⊥
1p≱10p (.10 , (.1 , refl , s≤s ()) , refl)

2p≱10p : (2p ≥c 10p) → ⊥
2p≱10p (.10 , (.2 , refl , s≤s (s≤s ())) , refl)

5p≱10p : (5p ≥c 10p) → ⊥
5p≱10p (.10 , (.5 , refl , s≤s (s≤s (s≤s (s≤s (s≤s ()))))) , refl)



extract : ∀ {c c' n cs} → sumbound (val c + n , c') (c ∷ cs) → sumbound (n , c) cs
extract (.(inj₁ tt) , () , inj₁ (tt , refl , _))
extract (.(inj₂ (fst 1p , snd (m , 1p))) , (refl , sb) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , refl) , raise)) = sb
extract (.(inj₂ (fst 2p , snd (m , 2p))) , (refl , sb) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , refl) , raise)) = sb
extract (.(inj₂ (fst 5p , snd (m , 5p))) , (refl , sb) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , refl) , raise)) = sb
extract (.(inj₂ (fst 10p , snd (m , 10p))) , (refl , sb) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , refl) , raise)) = sb

out-of-bound : ∀ {c d n cs} → (d ≥c c → ⊥) → sumbound (n , d) (c ∷ cs) → ⊥
out-of-bound c≰d (.(inj₁ tt) , () , inj₁ (tt , refl , _))
out-of-bound c≰d (.(inj₂ (fst c , snd (proj₁ , c))) , (refl , proj₃) , inj₂ ((fst c , snd (proj₁ , .c)) , refl , (refl , proj₅) , c≤d , proj₄)) = c≰d c≤d

out-of-sum : ∀ {c d n cs} → (n ≥ val c → ⊥) → sumbound (n , d) (c ∷ cs) → ⊥
out-of-sum n≱c (.(inj₁ tt) , () , inj₁ (tt , refl , _))
out-of-sum n≱c (.(inj₂ (fst 1p , snd (m , 1p))) , (refl , sb) , inj₂ ((fst 1p , snd (m , .1p)) , refl , (refl , refl) , raise)) = n≱c (s≤s Data.Nat.z≤n)
out-of-sum n≱c (.(inj₂ (fst 2p , snd (m , 2p))) , (refl , sb) , inj₂ ((fst 2p , snd (m , .2p)) , refl , (refl , refl) , raise)) = n≱c (s≤s (s≤s Data.Nat.z≤n))
out-of-sum n≱c (.(inj₂ (fst 5p , snd (m , 5p))) , (refl , sb) , inj₂ ((fst 5p , snd (m , .5p)) , refl , (refl , refl) , raise)) = n≱c (s≤s (s≤s (s≤s (s≤s (s≤s Data.Nat.z≤n)))))
out-of-sum n≱c (.(inj₂ (fst 10p , snd (m , 10p))) , (refl , sb) , inj₂ ((fst 10p , snd (m , .10p)) , refl , (refl , refl) , raise)) = n≱c (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s Data.Nat.z≤n))))))))))

lemma-1p : ∀ {n} → (m : ℕ) → (cs : List Coin) → m ≤ n → sumbound (n , 1p) cs → ∃ (λ ds → ds ⊴ cs × sumbound (m , 1p) ds)
lemma-1p zero cs m≤n sb = ([] , ⊴-nil , (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)))
lemma-1p (suc m) (In (inj₁ tt)) () (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))
lemma-1p (suc m) (In (inj₁ tt)) m≤n (.(inj₂ (fst x , snd x₁)) , () , inj₂ ((fst x , snd x₁) , refl , proj₆))
lemma-1p (suc m) (In (inj₂ (fst 1p , snd cs))) m≤n (.(inj₁ tt) , () , inj₁ (tt , refl , _))
lemma-1p (suc m) (In (inj₂ (fst 1p , snd cs))) (s≤s m≤n) (._ , (refl , sb) , inj₂ ((fst .1p , snd (n , .1p)) , refl , (refl , refl) , raise)) with lemma-1p m cs m≤n sb
... | (ds , leq , sb') = (1p ∷ ds , ⊴-cons leq , inj₂ (fst 1p , snd (m , 1p)) , (refl , sb') , inj₂ (_ , refl , ((refl , refl) , raise)))
lemma-1p (suc m) (In (inj₂ (fst 2p , snd cs))) m≤n sb with out-of-bound 1p≱2p sb
... | ()
lemma-1p (suc m) (In (inj₂ (fst 5p , snd cs))) m≤n sb with out-of-bound 1p≱5p sb
... | ()
lemma-1p (suc m) (In (inj₂ (fst 10p , snd cs))) m≤n sb with out-of-bound 1p≱10p sb
... | ()

lemma-nil : ∀ {n c} → 1 ≤ n → sumbound (n , c) [] → ⊥
lemma-nil () (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))
lemma-nil n≥1 (.(inj₂ proj₃) , () , inj₂ (proj₃ , refl , proj₅))

relax' : ∀ {n c d} → d ≥c c → (cs : List Coin) → sumbound (n , c) cs → sumbound (n , d) cs
relax' c≤d (In (inj₁ tt)) (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)) = (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))
relax' c≤d (In (inj₁ tt)) (.(inj₂ (fst x , proj₄)) , () , inj₂ ((fst x , proj₄) , refl , proj₆)) 
relax' c≤d (In (inj₂ (fst c' , snd cs))) (.(inj₁ tt) , () , inj₁ (tt , refl , _))
relax' {c = c} {d} c≤d (In (inj₂ (fst c' , snd cs))) (.(inj₂ (fst c' , snd (m , c'))) , (refl , sb) , inj₂ ((fst .c' , snd (m , .c')) , refl , (refl , refl) , c'≤c , c'≤c'))
   = (inj₂ (fst c' , snd (m , c')) , (refl , sb) , inj₂ (_ , refl , (refl , refl) , (≤c-trans {c'}{c}{d} c'≤c c≤d , c'≤c')))

relax : ∀ {m c d cs} → d ≥c c → ∃ (λ ds → ds ⊴ cs × sumbound (m , c) ds) → ∃ (λ ds → ds ⊴ cs × sumbound (m , d) ds)
relax c≤d (ds , leq , sb) = (ds , leq , (relax' c≤d _ sb))

tighten : ∀ {n c d} → (cs : List Coin) → sumbound (n , d) (c ∷ cs) → sumbound (n , c) (c ∷ cs)
tighten cs (.(inj₁ tt) , () , inj₁ (tt , refl , _))
tighten cs (.(inj₂ (fst c , snd (m , c))) , (refl , sb) , inj₂ ((fst c , snd (m , .c)) , refl , (refl , refl) , c≤d , c≤c))
   = (inj₂ (fst c , snd (m , c)) , (refl , sb) , inj₂ (_ , refl , (refl , refl) , c≤c , c≤c))

add-1p : ∀ {m c} → (cs : List Coin) → sumbound (m , 2p) cs → ∃ (λ ds → ds ⊴ (c ∷ cs) × sumbound (suc m , 2p) ds)
add-1p (In (inj₁ tt)) (.(inj₁ tt) , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt)) = relax {c = 1p} 2p≥1p (1p ∷ [] , ⊴-cons ⊴-refl' , inj₂ (fst 1p , snd (0 , 1p)) , (refl , (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , refl , Data.Unit.tt))) , inj₂ (_ , refl , (refl , refl) , (1p≥1p , 1p≥1p)))
add-1p (In (inj₁ tt)) (.(inj₂ proj₃) , () , inj₂ (proj₃ , refl , proj₅)) 
add-1p (In (inj₂ (fst c , snd cs))) (.(inj₁ tt) , () , inj₁ (tt , refl , proj₄))
add-1p (In (inj₂ (fst 1p , snd cs))) sb = relax {c = 1p} 2p≥1p (1p ∷ (1p ∷ cs) , ⊴-cons ⊴-refl' , inj₂ (fst 1p , snd (_ , 1p)) , (refl , tighten cs sb) , inj₂ ((fst 1p , snd (_ , 1p)) , refl , (refl , refl) , 1p≥1p , 1p≥1p))
add-1p (In (inj₂ (fst 2p , snd cs))) (.(inj₂ (fst 2p , snd (m , 2p))) , (refl , sb) , inj₂ ((fst .2p , snd (m , .2p)) , refl , (refl , refl) , 2p≥c , c≥c)) with add-1p {c = 2p} cs sb
... | (ds , leq , dsb) = (2p ∷ ds , ⊴-cons leq , inj₂ (fst 2p , snd (_ , 2p)) , (refl , dsb) , inj₂ (_ , refl , (refl , refl) , (2p≥2p , 2p≥2p)))
add-1p (In (inj₂ (fst 5p , snd cs))) (.(inj₂ (fst 5p , snd (m , 5p))) , (refl , sb) , inj₂ ((fst .5p , snd (m , .5p)) , refl , (refl , refl) , 2p≥c , c≥c)) with 2p≱5p 2p≥c
... | ()
add-1p (In (inj₂ (fst 10p , snd cs))) (.(inj₂ (fst 10p , snd (m , 10p))) , (refl , sb) , inj₂ ((fst .10p , snd (m , .10p)) , refl , (refl , refl) , 2p≥c , c≥c)) with 2p≱10p 2p≥c
... | ()


greedy-lemma : (c d : Coin) → (n m : ℕ) → (cs : List Coin) → c ≤c d → val c + n ≡ val d + m → sumbound (n , c) cs → ∃(λ ds → ds ⊴ cs × sumbound (m , d) ds)
greedy-lemma 1p 1p n .n cs c≤d refl sb = lemma-1p n cs ≤-refl sb
greedy-lemma 1p 2p ._ m cs c≤d refl sb = relax 2p≥1p (lemma-1p m cs (≤-steps 1) sb)
greedy-lemma 1p 5p ._ m cs c≤d refl sb = relax 5p≥1p (lemma-1p m cs (≤-steps 4) sb)
greedy-lemma 1p 10p ._ m cs c≤d refl sb = relax 10p≥1p (lemma-1p m cs (≤-steps 9) sb)
greedy-lemma 2p 1p n m cs c≤d eq sb with 1p≱2p c≤d
greedy-lemma 2p 1p n m cs c≤d eq sb | ()
greedy-lemma 2p 2p n .n cs c≤d refl sb = (cs , ⊴-refl' , sb)
greedy-lemma 2p 5p ._ m (In (inj₁ tt)) c≤d refl sb with lemma-nil (s≤s z≤n) sb
greedy-lemma 2p 5p ._ m (In (inj₁ tt)) c≤d refl sb | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 1p , snd cs))) c≤d refl sb = relax 5p≥1p (lemma-1p m (1p ∷ cs) (≤-steps 3) (tighten cs sb))
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd cs))) c≤d refl sb with extract sb
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl sb | sb' with lemma-nil (s≤s z≤n) sb'
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs)))))) c≤d refl sb | sb' with extract sb'
...| sb'' = (cs , ⊴-step (⊴-step ⊴-refl') , (relax' 5p≥1p cs sb''))
greedy-lemma 2p 5p ._ zero (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' with out-of-sum 1≱2 sb'
greedy-lemma 2p 5p ._ zero (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 5p ._ (suc m) (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' with add-1p {c = 2p} cs (extract sb')
... | (ds , leq , dsb) = (ds , ⊴-step leq , relax' 5p≥2p ds dsb)
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl sb | sb' with out-of-bound 2p≱5p sb'
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl sb | sb' with out-of-bound 2p≱10p sb'
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb with out-of-bound 2p≱5p sb
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb | ()
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 10p , snd cs))) c≤d refl sb with out-of-bound 2p≱10p sb
greedy-lemma 2p 5p ._ m (In (inj₂ (fst 10p , snd cs))) c≤d refl sb | ()
greedy-lemma 2p 10p ._ m (In (inj₁ tt)) c≤d refl sb with lemma-nil (s≤s z≤n) sb
greedy-lemma 2p 10p ._ m (In (inj₁ tt)) c≤d refl sb | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 1p , snd cs))) c≤d refl sb = relax 10p≥1p (lemma-1p m (1p ∷ cs) (≤-steps 8) (tighten cs sb))
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd cs))) c≤d refl sb with extract sb
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl sb | sb' with lemma-nil (s≤s z≤n) sb'
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs)))))) c≤d refl sb | sb' with lemma-1p m (1p ∷ cs) (≤-steps 6) (tighten cs sb')
... | (ds , leq , dsb) = (ds , ⊴-step leq , relax' 10p≥1p ds dsb)
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' with extract sb'
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt)))))))) c≤d refl sb | sb' | sb'' with lemma-nil (s≤s z≤n) sb''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt)))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs))))))))) c≤d refl sb | sb' | sb'' with lemma-1p m (1p ∷ cs) (≤-steps 4) (tighten cs sb'')
... | (ds , leq , dsb) = (ds , ⊴-step (⊴-step leq) , relax' 10p≥1p ds dsb)
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs))))))))) c≤d refl sb | sb' | sb'' with extract sb''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt))))))))))) c≤d refl sb | sb' | sb'' | sb''' with lemma-nil (s≤s z≤n) sb'''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt))))))))))) c≤d refl sb | sb' | sb'' | sb''' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' with lemma-1p m (1p ∷ cs) (≤-steps 2) (tighten cs sb''')
... | (ds , leq , dsb) = (ds , ⊴-step (⊴-step (⊴-step leq)) , relax' 10p≥1p ds dsb)
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb'''
    = (cs , ⊴-step (⊴-step (⊴-step (⊴-step ⊴-refl'))) , relax' 10p≥2p cs (extract sb'''))
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' with out-of-bound 2p≱5p sb'''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' with out-of-bound 2p≱10p sb'''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))))))))) c≤d refl sb | sb' | sb'' | sb''' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-bound 2p≱5p sb''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-bound 2p≱10p sb''
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl sb | sb' with out-of-bound 2p≱5p sb'
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl sb | sb' with out-of-bound 2p≱10p sb'
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl sb | sb' | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb with out-of-bound 2p≱5p sb
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb | ()
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 10p , snd cs))) c≤d refl sb with out-of-bound 2p≱10p sb
greedy-lemma 2p 10p ._ m (In (inj₂ (fst 10p , snd cs))) c≤d refl sb | ()
greedy-lemma 5p 1p n m cs c≤d eq sb with 1p≱5p c≤d
greedy-lemma 5p 1p n m cs c≤d eq sb | ()
greedy-lemma 5p 2p n m cs c≤d eq sb with 2p≱5p c≤d
greedy-lemma 5p 2p n m cs c≤d eq sb | ()
greedy-lemma 5p 5p n .n cs c≤d refl sb = (cs , ⊴-refl' , sb)
greedy-lemma 5p 10p ._ m (In (inj₁ tt)) c≤d refl sb with lemma-nil (s≤s z≤n) sb
greedy-lemma 5p 10p ._ m (In (inj₁ tt)) c≤d refl sb | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 1p , snd cs))) c≤d refl sb = relax 10p≥1p (lemma-1p m (1p ∷ cs) (≤-steps 5) (tighten cs sb))
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd cs))) c≤d refl sb with extract sb
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl _ | sb with lemma-nil (s≤s Data.Nat.z≤n) sb
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₁ tt))))) c≤d refl _ | sb | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs)))))) c≤d refl _ | sb with lemma-1p m (1p ∷ cs) (≤-steps 3) (tighten cs sb)
... | (ds , leq , dsb) = (ds , ⊴-step leq , relax' 10p≥1p ds dsb)
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs)))))) c≤d refl sb | sb' with extract sb'
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt)))))))) c≤d refl sb | sb' | sb'' with lemma-nil (s≤s z≤n) sb''
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₁ tt)))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 1p , snd cs))))))))) c≤d refl sb | sb' | sb'' with lemma-1p m (1p ∷ cs) (≤-steps 1) (tighten cs sb'')
... | (ds , leq , dsb) = (ds , ⊴-step (⊴-step leq) , relax' 10p≥1p ds dsb)
greedy-lemma 5p 10p ._ zero (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-sum 1≱2 sb''
greedy-lemma 5p 10p ._ zero (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 5p 10p ._ (suc m) (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd cs))))))))) c≤d refl sb | sb' | sb'' with add-1p {c = 2p} cs (extract sb'')
... | (ds , leq , dsb) = (ds , ⊴-step (⊴-step leq) , relax' 10p≥2p ds dsb)
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-bound 2p≱5p sb''
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs))))))))) c≤d refl sb | sb' | sb'' with out-of-bound 2p≱10p sb''
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs))))))))) c≤d refl sb | sb' | sb'' | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl _ | sb with out-of-bound 2p≱5p sb
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 5p , snd cs)))))) c≤d refl _ | sb | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl _ | sb with out-of-bound 2p≱10p sb
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 2p , snd (In (inj₂ (fst 10p , snd cs)))))) c≤d refl _ | sb | ()
greedy-lemma 5p 10p ._ m (In (inj₂ (fst 5p , snd cs))) c≤d refl sb with extract sb
... | sb' = (cs , ⊴-step ⊴-refl' , (relax' 10p≥5p cs sb'))
greedy-lemma 5p 10p n m (In (inj₂ (fst 10p , snd cs))) c≤d eq sb with out-of-bound 5p≱10p sb
greedy-lemma 5p 10p n m (In (inj₂ (fst 10p , snd cs))) c≤d eq sb | ()
greedy-lemma 10p 1p n m cs c≤d eq sb with 1p≱10p c≤d
greedy-lemma 10p 1p n m cs c≤d eq sb | ()
greedy-lemma 10p 2p n m cs c≤d eq sb with 2p≱10p c≤d
greedy-lemma 10p 2p n m cs c≤d eq sb | ()
greedy-lemma 10p 5p n m cs c≤d eq sb with 5p≱10p c≤d
greedy-lemma 10p 5p n m cs c≤d eq sb | ()
greedy-lemma 10p 10p n .n cs c≤d refl sb = (cs , ⊴-refl' , sb)


{-
  sumc xs = n ≡ xs ⊵ coin-change n
  coin-change ⊑ (sumc ˘) ↾ (_⊴_)
  coin-change ⊑ ⦇[ zero, plus ∘ (val × id) ]⦈ ˘ ↾ (_⊴_)

  coin-change = ⦇([ zero , plus ∘ (val × id) ] ˘ ↾ Q) ˘⦈ ˘
    where Q = (id + _≤c_ × id)
-}

{-
coin-change-der : foldR ListF ((([ zero , (plus ○ bimapR (arg₁ ⊗ arg₂) (fun val) idR) ] ˘) ↾ {!!}) ˘) ˘
                   ⊑ (sumc ˘) ↾ (_⊴_)
coin-change-der = {!!}
-}
