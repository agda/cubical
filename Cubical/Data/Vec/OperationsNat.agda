{-# OPTIONS --lossy-unification #-}
module Cubical.Data.Vec.OperationsNat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec.Base
open import Cubical.Data.Vec.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

private variable
  ℓ : Level


-----------------------------------------------------------------------------
-- Generating Vector

genδℕ-Vec : {A : Type ℓ} → (m k : ℕ) → (a b : A) → Vec A m
genδℕ-Vec zero k a b = []
genδℕ-Vec (suc m) k a b  with (discreteℕ k m)
... | yes p = a ∷ replicate b
... | no ¬p = b ∷ (genδℕ-Vec m k a b)

-- some results are easier / false without general a and b
δℕ-Vec : (m : ℕ) → (k : ℕ) → Vec ℕ m
δℕ-Vec m k = genδℕ-Vec m k 1 0

δℕ-Vec-n≤k→≡ : (m k : ℕ) → (m ≤ k) → δℕ-Vec m k ≡ replicate 0
δℕ-Vec-n≤k→≡ zero k r = refl
δℕ-Vec-n≤k→≡ (suc m) k r with (discreteℕ k m)
... | yes p = ⊥.rec (<→≢ r (sym p))
... | no ¬p = cong (λ X → 0 ∷ X) (δℕ-Vec-n≤k→≡ m k (≤-trans ≤-sucℕ r))

δℕ-Vec-k<n→≢ : (m k : ℕ) → (k < m) → (δℕ-Vec m k ≡ replicate 0 → ⊥)
δℕ-Vec-k<n→≢ zero k r = ⊥.rec (¬-<-zero r)
δℕ-Vec-k<n→≢ (suc m) k r q with (discreteℕ k m) | (≤-split r)
... | yes p | z = compute-eqℕ 1 0 (fst (VecPath.encode _ _ q))
... | no ¬p | inl x = δℕ-Vec-k<n→≢ m k (pred-≤-pred x) (snd (VecPath.encode _ _ q))
... | no ¬p | inr x = ¬p (injSuc x)

-----------------------------------------------------------------------------
-- Point wise add
_+n-vec_ : {m : ℕ} → Vec ℕ m → Vec ℕ m → Vec ℕ m
_+n-vec_ {.zero} [] [] = []
_+n-vec_ {.(suc _)} (k ∷ v) (l ∷ v') = (k +n l) ∷ (v +n-vec v')

+n-vec-lid : {m : ℕ} → (v : Vec ℕ m) → replicate 0 +n-vec v ≡ v
+n-vec-lid {.zero} [] = refl
+n-vec-lid {.(suc _)} (k ∷ v) = cong (_∷_ k) (+n-vec-lid v)

+n-vec-rid : {m : ℕ} → (v : Vec ℕ m) → v +n-vec replicate 0 ≡ v
+n-vec-rid {.zero} [] = refl
+n-vec-rid {.(suc _)} (k ∷ v) = cong₂ _∷_ (+-zero k) (+n-vec-rid v)

+n-vec-assoc : {m : ℕ} → (v v' v'' : Vec ℕ m) → v +n-vec (v' +n-vec v'') ≡ (v +n-vec v') +n-vec v''
+n-vec-assoc [] [] [] = refl
+n-vec-assoc (k ∷ v) (l ∷ v') (p ∷ v'') = cong₂ _∷_ (+-assoc k l p) (+n-vec-assoc v v' v'')

+n-vec-comm : {m : ℕ} → (v v' : Vec ℕ m) → v +n-vec v' ≡ v' +n-vec v
+n-vec-comm {.zero} [] [] = refl
+n-vec-comm {.(suc _)} (k ∷ v) (l ∷ v') = cong₂ _∷_ (+-comm k l) (+n-vec-comm v v')



-----------------------------------------------------------------------------
-- Equlity on Vec ℕ
+n-vecSplitReplicate0 : {m : ℕ} → (v v' : Vec ℕ m) → (v +n-vec v') ≡ replicate 0
                        → (v ≡ replicate 0) × (v' ≡ replicate 0)
+n-vecSplitReplicate0 [] [] p = refl , refl
+n-vecSplitReplicate0 (k ∷ v) (l ∷ v') p with VecPath.encode ((k +n l) ∷ (v +n-vec v')) (replicate 0) p
... | pkl , pvv' = (cong₂ _∷_ (fst (m+n≡0→m≡0×n≡0 pkl)) (fst (+n-vecSplitReplicate0 v v' pvv'))) ,
                   (cong₂ _∷_ (snd (m+n≡0→m≡0×n≡0 pkl)) (snd (+n-vecSplitReplicate0 v v' pvv')))


pred-vec-≢0 : {m : ℕ} → (v : Vec ℕ m) → (v ≡ replicate 0 → ⊥)
              → Σ[ k ∈ ℕ ] (Σ[ v' ∈ Vec ℕ m ] ( Σ[ r ∈ (k < m) ] v ≡ v' +n-vec (δℕ-Vec m k)))
pred-vec-≢0 {zero} [] ¬q = ⊥.rec (¬q refl)
pred-vec-≢0 {(suc m)} (l ∷ v) ¬q with (discreteℕ l 0)
-- case l ≡ 0
pred-vec-≢0 {(suc m)} (l ∷ v) ¬q | yes p with pred-vec-≢0 v (λ r → ¬q (cong₂ _∷_ p r))
... | k , v' , infkm , eqvv' = k , ((0 ∷ v') , ((≤-trans infkm ≤-sucℕ) , helper))
  where
  helper : _
  helper with (discreteℕ k m)
  ... | yes pp = ⊥.rec (<→≢ (fst infkm , +-suc _ _ ∙ cong suc (snd infkm)) (cong suc pp))
  ... | no ¬pp = cong₂ _∷_ p eqvv'
-- case l ≢ 0
pred-vec-≢0 {(suc m)} (l ∷ v) ¬q | no ¬p = m , ((predℕ l ∷ v) , (≤-refl , helper))
  where
  helper : _
  helper with (discreteℕ m m)
  ... | yes pp = cong₂ _∷_ (sym (+-suc _ _ ∙ +-zero _ ∙ sym (suc-predℕ l ¬p)))
                      (sym (+n-vec-rid v))
  ... | no ¬pp = ⊥.rec (¬pp refl)



-- split + concat vec results
sep-vec : (k l : ℕ) → Vec ℕ (k +n l) → (Vec ℕ k) ×  (Vec ℕ l )
sep-vec zero l v = [] , v
sep-vec (suc k) l (x ∷ v) = (x ∷ fst (sep-vec k l v)) , (snd (sep-vec k l v))

sep-vec-fst : (k l : ℕ) → (v : Vec ℕ k) → (v' : Vec ℕ l) → fst (sep-vec k l (v ++ v')) ≡ v
sep-vec-fst zero l [] v' = refl
sep-vec-fst (suc k) l (x ∷ v) v' = cong (λ X → x ∷ X) (sep-vec-fst k l v v')

sep-vec-snd : (k l : ℕ) → (v : Vec ℕ k) → (v' : Vec ℕ l) → snd (sep-vec k l (v ++ v')) ≡ v'
sep-vec-snd zero l [] v' = refl
sep-vec-snd (suc k) l (x ∷ v) v' = sep-vec-snd k l v v'

sep-vec-id : (k l : ℕ) → (v : Vec ℕ (k +n l)) → fst (sep-vec k l v) ++ snd (sep-vec k l v) ≡ v
sep-vec-id zero l v = refl
sep-vec-id (suc k) l (x ∷ v) = cong (λ X → x ∷ X) (sep-vec-id k l v)

rep-concat : (k l : ℕ) → {B : Type ℓ} → (b : B) →
             replicate {_} {k} {B} b ++ replicate {_} {l} {B} b ≡ replicate {_} {k +n l} {B} b
rep-concat zero l b = refl
rep-concat (suc k) l b = cong (λ X → b ∷ X) (rep-concat k l b)

+n-vec-concat : (k l : ℕ) → (v w : Vec ℕ k) → (v' w' : Vec ℕ l)
                → (v +n-vec w) ++ (v' +n-vec w') ≡ (v ++ v') +n-vec (w ++ w')
+n-vec-concat zero l [] [] v' w' = refl
+n-vec-concat (suc k) l (x ∷ v) (y ∷ w) v' w' = cong (λ X → x +n y ∷ X) (+n-vec-concat k l v w v' w')
