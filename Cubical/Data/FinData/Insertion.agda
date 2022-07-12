{-
  Insertion of elements into 'FinVec's.
-}
{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Insertion where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary
open import Cubical.Data.FinData

open import Cubical.Tactics.NatSolver.Reflection


private variable
  ℓ ℓ' : Level
  A : Type ℓ
  m n k l : ℕ

{- having the following function here, avoids cyclic dependencies -}
<-trans-suc : l < m → m < suc n → l < n
<-trans-suc {l = l} {m = m} {n = n} (c , p) (d , q) =
  (c + d) , (c + d + suc l   ≡⟨ step1 c d (suc l) ⟩
             d + (c + suc l) ≡⟨ cong (d +_) p ⟩
             d + m           ≡⟨ injSuc (sym (+-suc d m) ∙ q) ⟩
             n ∎)
     where
       step1 : ∀ x y z → x + y + z ≡ y + (x + z)
       step1 = solve

module _ {n : ℕ} {P : Fin n → Type ℓ'} (i : Fin n)
       (Plt : (l : Fin n) → (toℕ l < toℕ i) → P l)
       (P≡  : (l : Fin n) → (toℕ l ≡ toℕ i) → P l)
       (Pgt : (l : Fin n) → (toℕ i < toℕ l) → P l)
      where

  trichotomyElim : (l : Fin n) → P l
  trichotomyElim  l with toℕ l ≟ (toℕ i)
  ...               | lt l<i = Plt l l<i
  ...               | eq l≡i = P≡ l l≡i
  ...               | gt i<l = Pgt l i<l

  trichotomyElimβgt : (l : Fin n) (l<i : toℕ l < toℕ i)
                      → trichotomyElim l ≡ Plt l l<i
  trichotomyElimβgt l l<i with toℕ l ≟ (toℕ i)
  ...                     | lt l<i = subst (λ u → Plt l l<i ≡ Plt l u) (isProp≤ _ _) refl
  ...                     | eq l≡i = ⊥.rec (<→≢ l<i l≡i)
  ...                     | gt i<l = ⊥.rec (<-asym l<i (<-weaken i<l))

  trichotomyElimβlt : (l : Fin n) (i<l : toℕ i < toℕ l)
                      → trichotomyElim l ≡ Pgt l i<l
  trichotomyElimβlt l i<l with toℕ l ≟ (toℕ i)
  ...                     | lt l<i = ⊥.rec (<-asym i<l (<-weaken l<i))
  ...                     | eq l≡i = ⊥.rec (<→≢ i<l (sym l≡i))
  ...                     | gt i<l = subst (λ u → Pgt l i<l ≡ Pgt l u) (isProp≤ _ _) refl

  trichotomyElimβ≡ : (l : Fin n) (l≡i : toℕ l ≡ toℕ i)
                      → trichotomyElim l ≡ P≡ l l≡i
  trichotomyElimβ≡ l l≡i with toℕ l ≟ (toℕ i)
  ...                    | lt l<i = ⊥.rec (<→≢ l<i l≡i)
  ...                    | eq l≡i = subst (λ u → P≡ l l≡i ≡ P≡ l u) (isSetℕ _ _ _ _) refl
  ...                    | gt i<l = ⊥.rec (<→≢ i<l (sym l≡i))

module _ {A : Type ℓ} {n : ℕ} (l : Fin (ℕ.suc n)) where
  drop : FinVec A (ℕ.suc n) → FinVec A n
  drop v i with (toℕ l) ≟ (toℕ i)
  ...      | lt l<i = v (suc i)
  ...      | eq l≡i = v (suc i)
  ...      | gt i<l = v (toFin (toℕ i) (<-trans i<l (toℕ<n l)))

module _ {A : Type ℓ} {n : ℕ} (l : Fin (ℕ.suc n)) (a : A) where
  private
    l' = toℕ l
    l<n+1 : l' < (ℕ.suc n)
    l<n+1 = toℕ<n l
    strengthen : (k : Fin (ℕ.suc n)) → (toℕ k) < (toℕ l) → Fin n
    strengthen k k<l = toFin (toℕ k) (<-trans-suc k<l l<n+1)

  insert' : (a : A) → FinVec A n → FinVec A (ℕ.suc n)
  insert' a v = trichotomyElim l
    (λ k k<l → v (strengthen k k<l))
    (λ k k≡l → a)
    (λ k l<k → v (toFin (predℕ (toℕ k)) (<-trans-suc (<-predℕ {!!}) (toℕ<n k))))

  insert : FinVec A n → FinVec A (ℕ.suc n)
  insert v k with l' ≟ (toℕ k)
  ... | eq l≡k = a
  ... | gt k<l = v (strengthen k k<l)
  ... | lt l<k with k
  ...          | suc k-1 = v k-1
  ...          | zero = v (fromℕ' n zero (⊥.rec (¬-<-zero l<k)))
                 -- use 'v 0' in absurd case, so we know what to do,
                 -- when proving equalities about this case

  insertCompute : (v : FinVec A n) → (insert v) l ≡ a
  insertCompute v with l' ≟ (toℕ l)
  ... | lt l<l = ⊥.rec (¬m<m l<l)
  ... | eq l≡l = refl
  ... | gt l<l = ⊥.rec (¬m<m l<l)
{-
  insertIso : isSet A → Iso (FinVec A n) (Σ[ u ∈ (FinVec A (ℕ.suc n)) ] (u l) ≡ a)
  Iso.fun      (insertIso _)            v = (insert v) , (insertCompute v)
  Iso.inv      (insertIso _)      (u , _) = drop l u
  Iso.rightInv (insertIso isSetA) (u , p) = Σ≡Prop (λ u → isSetA _ _) q
         where q : insert (drop l u) ≡ u
               q i k with (toℕ l) ≟ (toℕ k)
               q i k | eq l≡k = (a    ≡⟨ sym p ⟩
                                 u l  ≡⟨ cong u (inj-toℕ l≡k) ⟩
                                 u k ∎) i
               ...   | gt k<l with toℕ l ≟ toℕ (strengthen k k<l)
               q i k | gt k<l | x = {!!}
               ...   | lt l<k with k
               ...            | zero = ⊥.rec (¬-<-zero l<k) i {- with (toℕ l) ≟ zero
               ...                   | lt l<0 = ⊥.rec (¬-<-zero l<k) i
               ...                   | eq l≡0 = ⊥.rec (¬-<-zero l<k) i
               ...                   | lt l>0 = u zero -}
               q i k | lt l<k | suc k-1 with (toℕ l) ≟ (toℕ k-1)
               ...                      | lt l<k-1 = u (suc k-1)
               ...                      | eq l≡k-1 = u (suc k-1)
               ...                      | gt k-1<l = u (inj-toℕ {!λ j → suc k-1!} i)
  Iso.leftInv  (insertIso _)         v  = {!!}
-- -}
