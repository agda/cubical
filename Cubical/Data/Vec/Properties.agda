module Cubical.Data.Vec.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec.Base
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ


-- This is really cool!
-- Compare with: https://github.com/agda/agda-stdlib/blob/master/src/Data/Vec/Properties/WithK.agda#L32
++-assoc : ∀ {m n k} (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) →
           PathP (λ i → Vec A (+-assoc m n k (~ i))) ((xs ++ ys) ++ zs) (xs ++ ys ++ zs)
++-assoc {m = zero} [] ys zs = refl
++-assoc {m = suc m} (x ∷ xs) ys zs i = x ∷ ++-assoc xs ys zs i


-- Equivalence between Fin n → A and Vec A n
FinVec→Vec : {n : ℕ} → FinVec A n → Vec A n
FinVec→Vec {n = zero}  xs = []
FinVec→Vec {n = suc _} xs = xs zero ∷ FinVec→Vec (λ x → xs (suc x))

Vec→FinVec : {n : ℕ} → Vec A n → FinVec A n
Vec→FinVec xs f = lookup f xs

FinVec→Vec→FinVec : {n : ℕ} (xs : FinVec A n) → Vec→FinVec (FinVec→Vec xs) ≡ xs
FinVec→Vec→FinVec {n = zero} xs = funExt λ f → ⊥.rec (¬Fin0 f)
FinVec→Vec→FinVec {n = suc n} xs = funExt goal
  where
  goal : (f : Fin (suc n))
       → Vec→FinVec (xs zero ∷ FinVec→Vec (λ x → xs (suc x))) f ≡ xs f
  goal zero = refl
  goal (suc f) i = FinVec→Vec→FinVec (λ x → xs (suc x)) i f

Vec→FinVec→Vec : {n : ℕ} (xs : Vec A n) → FinVec→Vec (Vec→FinVec xs) ≡ xs
Vec→FinVec→Vec {n = zero}  [] = refl
Vec→FinVec→Vec {n = suc n} (x ∷ xs) i = x ∷ Vec→FinVec→Vec xs i

FinVecIsoVec : (n : ℕ) → Iso (FinVec A n) (Vec A n)
FinVecIsoVec n = iso FinVec→Vec Vec→FinVec Vec→FinVec→Vec FinVec→Vec→FinVec

FinVec≃Vec : (n : ℕ) → FinVec A n ≃ Vec A n
FinVec≃Vec n = isoToEquiv (FinVecIsoVec n)

FinVec≡Vec : (n : ℕ) → FinVec A n ≡ Vec A n
FinVec≡Vec n = ua (FinVec≃Vec n)

isContrVec0 : isContr (Vec A 0)
isContrVec0 = [] , λ { [] → refl }

-- encode - decode Vec
module VecPath {A : Type ℓ}
  where

  code : {n : ℕ} → (v v' : Vec A n) → Type ℓ
  code [] [] = Unit*
  code (a ∷ v) (a' ∷ v') = (a ≡ a') × (v ≡ v')

  -- encode
  reflEncode : {n : ℕ} → (v : Vec A n) → code v v
  reflEncode [] = tt*
  reflEncode (a ∷ v) = refl , refl

  encode : {n : ℕ} → (v v' : Vec A n) → (v ≡ v') → code v v'
  encode v v' p = J (λ v' _ → code v v') (reflEncode v) p

  encodeRefl : {n : ℕ} → (v : Vec A n) → encode v v refl ≡ reflEncode v
  encodeRefl v = JRefl (λ v' _ → code v v') (reflEncode v)

  -- decode
  decode : {n : ℕ} → (v v' : Vec A n) → (r : code v v') → (v ≡ v')
  decode [] [] _ = refl
  decode (a ∷ v) (a' ∷ v') (p , q) = cong₂ _∷_ p q

  decodeRefl : {n : ℕ} → (v : Vec A n) → decode v v (reflEncode v) ≡ refl
  decodeRefl [] = refl
  decodeRefl (a ∷ v) = refl

  -- equiv
  ≡Vec≃codeVec : {n : ℕ} → (v v' : Vec A n) → (v ≡ v') ≃ (code v v')
  ≡Vec≃codeVec v v' = isoToEquiv is
    where
    is : Iso (v ≡ v') (code v v')
    fun is = encode v v'
    inv is = decode v v'
    rightInv is = sect v v'
      where
      sect : {n : ℕ} → (v v' : Vec A n) → (r : code v v')
             → encode v v' (decode v v' r) ≡ r
      sect [] [] tt* = encodeRefl []
      sect (a ∷ v) (a' ∷ v') (p , q) = J (λ a' p → encode (a ∷ v) (a' ∷ v') (decode (a ∷ v) (a' ∷ v') (p , q)) ≡ (p , q))
                                       (J (λ v' q → encode (a ∷ v) (a ∷ v') (decode (a ∷ v) (a ∷ v') (refl , q)) ≡ (refl , q))
                                       (encodeRefl (a ∷ v)) q) p
    leftInv is = retr v v'
      where
      retr : {n : ℕ} → (v v' : Vec A n) → (p : v ≡ v')
             → decode v v' (encode v v' p) ≡ p
      retr v v' p = J (λ v' p → decode v v' (encode v v' p) ≡ p)
                    (cong (decode v v) (encodeRefl v) ∙ decodeRefl v) p


  isOfHLevelVec : (h : HLevel) (n : ℕ)
                  → isOfHLevel (suc (suc h)) A → isOfHLevel (suc (suc h)) (Vec A n)
  isOfHLevelVec h zero ofLevelA [] [] = isOfHLevelRespectEquiv (suc h) (invEquiv (≡Vec≃codeVec [] []))
                                        (isOfHLevelUnit* (suc h))
  isOfHLevelVec h (suc n) ofLevelA (x ∷ v) (x' ∷ v') = isOfHLevelRespectEquiv (suc h) (invEquiv (≡Vec≃codeVec _ _))
                                                       (isOfHLevelΣ (suc h) (ofLevelA x x') (λ _ → isOfHLevelVec h n ofLevelA v v'))


  discreteA→discreteVecA : Discrete A → (n : ℕ) → Discrete (Vec A n)
  discreteA→discreteVecA DA zero [] [] = yes refl
  discreteA→discreteVecA DA (suc n) (a ∷ v) (a' ∷ v') with (DA a a') | (discreteA→discreteVecA DA n v v')
  ... | yes p | yes q = yes (invIsEq (snd (≡Vec≃codeVec (a ∷ v) (a' ∷ v'))) (p , q))
  ... | yes p | no ¬q = no (λ r → ¬q (snd (funIsEq (snd (≡Vec≃codeVec (a ∷ v) (a' ∷ v'))) r)))
  ... | no ¬p | yes q = no (λ r → ¬p (fst (funIsEq (snd (≡Vec≃codeVec (a ∷ v) (a' ∷ v'))) r)))
  ... | no ¬p | no ¬q = no (λ r → ¬q (snd (funIsEq (snd (≡Vec≃codeVec (a ∷ v) (a' ∷ v'))) r)))

  ≢-∷ : {m : ℕ} → (Discrete A) → (a : A) → (v : Vec A m) → (a' : A) → (v' : Vec A m) →
         (a ∷ v ≡ a' ∷ v' → ⊥.⊥) → (a ≡ a' → ⊥.⊥) ⊎ (v ≡ v' → ⊥.⊥)
  ≢-∷ {m} discreteA a v a' v' ¬r with (discreteA a a')
                        | (discreteA→discreteVecA discreteA m v v')
  ... | yes p | yes q = ⊥.rec (¬r (cong₂ _∷_ p q))
  ... | yes p | no ¬q = inr ¬q
  ... | no ¬p | y = inl ¬p
