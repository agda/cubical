module Cubical.Data.Vec.DepVec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Relation.Nullary

open Iso

private
  variable
    ℓ : Level

data depVec (G : (n : ℕ) → Type ℓ) : ℕ → Type ℓ where
  ⋆   : depVec G 0
  _□_ : {n : ℕ} → (a : G n) → (v : depVec G n) → depVec G (suc n)


module depVecPath (G : (n : ℕ) → Type ℓ)
  where

  code : {n : ℕ} → (v v' : depVec G n) → Type ℓ
  code ⋆ ⋆ = Unit*
  code (a □ v) (a' □ v') = (a ≡ a') × (v ≡ v')

  -- encode
  reflEncode : {n : ℕ} → (v : depVec G n) → code v v
  reflEncode ⋆ = tt*
  reflEncode (a □ v) = refl , refl

  encode : {n : ℕ} → (v v' : depVec G n) → (v ≡ v') → code v v'
  encode v v' p = J (λ v' _ → code v v') (reflEncode v) p

  encodeRefl : {n : ℕ} → (v : depVec G n) → encode v v refl ≡ reflEncode v
  encodeRefl v = JRefl (λ v' _ → code v v') (reflEncode v)

  -- decode
  decode : {n : ℕ} → (v v' : depVec G n) → (r : code v v') → (v ≡ v')
  decode ⋆ ⋆ _ = refl
  decode (a □ v) (a' □ v') (p , q) = cong₂ _□_ p q

  decodeRefl : {n : ℕ} → (v : depVec G n) → decode v v (reflEncode v) ≡ refl
  decodeRefl ⋆ = refl
  decodeRefl (a □ v) = refl

  -- equiv
  ≡Vec≃codeVec : {n : ℕ} → (v v' : depVec G n) → (v ≡ v') ≃ (code v v')
  ≡Vec≃codeVec v v' = isoToEquiv is
    where
    is : Iso (v ≡ v') (code v v')
    fun is = encode v v'
    inv is = decode v v'
    rightInv is = sect v v'
      where
      sect : {n : ℕ} → (v v' : depVec G n) → (r : code v v')
             → encode v v' (decode v v' r) ≡ r
      sect ⋆ ⋆ tt* = encodeRefl ⋆
      sect (a □ v) (a' □ v') (p , q) = J (λ a' p → encode (a □ v) (a' □ v') (decode (a □ v) (a' □ v') (p , q)) ≡ (p , q))
                                       (J (λ v' q → encode (a □ v) (a □ v') (decode (a □ v) (a □ v') (refl , q)) ≡ (refl , q))
                                       (encodeRefl (a □ v)) q) p
    leftInv is = retr v v'
      where
      retr : {n : ℕ} → (v v' : depVec G n) → (p : v ≡ v')
             → decode v v' (encode v v' p) ≡ p
      retr v v' p = J (λ v' p → decode v v' (encode v v' p) ≡ p)
                    (cong (decode v v) (encodeRefl v) ∙ decodeRefl v) p
