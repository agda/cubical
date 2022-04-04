{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Data.Vec.OperationsNat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat renaming(_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec.Base
open import Cubical.Data.Sigma

private variable
  ℓ : Level

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
