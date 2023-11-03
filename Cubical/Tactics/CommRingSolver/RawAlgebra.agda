{-# OPTIONS --safe #-}
module Cubical.Tactics.CommRingSolver.RawAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int
  renaming
  ( _+_ to _+ℤ_
  ; _·_ to _·ℤ_
  ; -_ to -ℤ_
  ; _-_ to _-ℤ_
  ; +Assoc to +ℤAssoc
  ; +Comm to +ℤComm
  ; -DistL· to -ℤDistL·ℤ
  ; ·DistR+ to ·ℤDistR+
  ; ·DistL+ to ·ℤDistL+)
  hiding
  ( ·IdL
  ; ·IdR)

open import Cubical.Tactics.CommRingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Tactics.CommRingSolver.IntAsRawRing
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

private
  variable
    ℓ ℓ' : Level

record RawAlgebra (R : RawRing ℓ) (ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor rawalgebra

  field
    Carrier : Type ℓ'
    scalar  : ⟨ R ⟩ᵣ → Carrier
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

  infixl 8 _·_
  infixl 7 -_
  infixl 6 _+_

⟨_⟩ : {R : RawRing ℓ} → RawAlgebra R ℓ' → Type ℓ'
⟨_⟩ = RawAlgebra.Carrier

{-
  Mapping to integer scalars and its (homorphism) properties.
-}
module _ (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Cubical.Algebra.Ring.RingTheory (CommRing→Ring R)

  scalarℕ : ℕ → (fst R)
  scalarℕ ℕ.zero = 0r
  scalarℕ (ℕ.suc ℕ.zero) = 1r
  scalarℕ (ℕ.suc (ℕ.suc n)) = 1r + scalarℕ (ℕ.suc n)

  scalar : ℤ → (fst R)
  scalar (pos k)  = scalarℕ k
  scalar (negsuc k)  = - scalarℕ (ℕ.suc k)

  -DistScalar : (k : ℤ)
                → scalar (-ℤ k) ≡ - (scalar k)
  -DistScalar (pos ℕ.zero) = sym 0Selfinverse
  -DistScalar (pos (ℕ.suc n)) = refl
  -DistScalar (negsuc n) = sym (-Idempotent _)

  lemmaSuc : (k : ℤ)
          → scalar (sucℤ k) ≡ 1r + scalar k
  lemmaSuc (pos ℕ.zero) = sym (+IdR _)
  lemmaSuc (pos (ℕ.suc ℕ.zero)) = refl
  lemmaSuc (pos (ℕ.suc (ℕ.suc n))) = refl
  lemmaSuc (negsuc ℕ.zero) = sym (+InvR _)
  lemmaSuc (negsuc (ℕ.suc n)) =
    scalar (negsuc n)                        ≡⟨ sym (+IdL (scalar (negsuc n))) ⟩
    0r + scalar (negsuc n)                  ≡[ i ]⟨ +InvR 1r (~ i) + scalar (negsuc n) ⟩
    (1r - 1r) + scalar (negsuc n)           ≡⟨ sym (+Assoc _ _ _) ⟩
    1r + (- 1r + - scalar (pos (ℕ.suc n))) ≡[ i ]⟨ 1r + -Dist 1r (scalar (pos (ℕ.suc n))) i ⟩
    1r + -(1r + scalar (pos (ℕ.suc n)))    ≡⟨ refl ⟩
    1r + -(scalar (pos (ℕ.suc (ℕ.suc n)))) ≡⟨ refl ⟩
    1r + scalar (negsuc (ℕ.suc n)) ∎

  lemmaPred : (k : ℤ)
          → scalar (predℤ k) ≡ - 1r + scalar k
  lemmaPred k = sym(
    - 1r + scalar k                      ≡[ i ]⟨ - 1r + scalar (sucPred k (~ i)) ⟩
    - 1r + scalar (sucℤ (predℤ k))   ≡[ i ]⟨ - 1r + lemmaSuc (predℤ k) i ⟩
    - 1r + (1r + scalar (predℤ k))     ≡⟨ +Assoc _ _ _ ⟩
    (- 1r + 1r) + scalar (predℤ k)     ≡[ i ]⟨ +InvL 1r i + scalar (predℤ k) ⟩
    0r + scalar (predℤ k)              ≡⟨ +IdL _ ⟩
    scalar (predℤ k)  ∎)

  +HomScalar : (k l : ℤ)
               → scalar (k +ℤ l) ≡ (scalar k) + (scalar l)
  +HomScalar (pos ℕ.zero) l =
             scalar (0 +ℤ l)       ≡[ i ]⟨ scalar (sym (pos0+ l) i) ⟩
             scalar l              ≡⟨ sym (+IdL _) ⟩
             0r + scalar l         ≡⟨ refl  ⟩
             scalar 0 + scalar l   ∎

  +HomScalar (pos (ℕ.suc ℕ.zero)) l =
    scalar (1 +ℤ l)                         ≡[ i ]⟨ scalar (+ℤComm 1 l i) ⟩
    scalar (l  +ℤ 1)                        ≡⟨ refl ⟩
    scalar (sucℤ l)                       ≡⟨ lemmaSuc l ⟩
    1r + scalar l                           ≡⟨ refl ⟩
    scalar (pos (ℕ.suc ℕ.zero)) + scalar l ∎

  +HomScalar (pos (ℕ.suc (ℕ.suc n))) l =
    scalar (pos (ℕ.suc (ℕ.suc n)) +ℤ l)        ≡⟨ refl ⟩
    scalar ((pos (ℕ.suc n) +ℤ 1) +ℤ l)         ≡[ i ]⟨ scalar ((+ℤComm (pos (ℕ.suc n)) 1 i) +ℤ l) ⟩
    scalar ((1 +ℤ (pos (ℕ.suc n))) +ℤ l)       ≡[ i ]⟨ scalar (+ℤAssoc 1 (pos (ℕ.suc n)) l (~ i)) ⟩
    scalar (1 +ℤ (pos (ℕ.suc n) +ℤ l))         ≡⟨ +HomScalar (pos (ℕ.suc ℕ.zero)) (pos (ℕ.suc n) +ℤ l) ⟩
    scalar 1 + scalar (pos (ℕ.suc n) +ℤ l)     ≡⟨ refl ⟩
    1r + (scalar (pos (ℕ.suc n) +ℤ l))         ≡[ i ]⟨ 1r + +HomScalar (pos (ℕ.suc n)) l i ⟩
    1r + (scalar (pos (ℕ.suc n)) + scalar l)   ≡⟨ +Assoc _ _ _ ⟩
    (1r + scalar (pos (ℕ.suc n))) + scalar l   ≡⟨ refl ⟩
    scalar (pos (ℕ.suc (ℕ.suc n))) + scalar l ∎

  +HomScalar (negsuc ℕ.zero) l =
    scalar (-1 +ℤ l)                  ≡[ i ]⟨ scalar (+ℤComm -1 l i) ⟩
    scalar (l +ℤ -1)                  ≡⟨ refl ⟩
    scalar (predℤ l)                ≡⟨ lemmaPred l ⟩
    - 1r + scalar l                    ≡⟨ refl ⟩
    scalar -1 + scalar l ∎

  +HomScalar (negsuc (ℕ.suc n)) l =
    scalar (negsuc (ℕ.suc n) +ℤ l)               ≡⟨ refl ⟩
    scalar ((negsuc n +ℤ -1) +ℤ l)               ≡[ i ]⟨ scalar (+ℤComm (negsuc n) -1 i +ℤ l) ⟩
    scalar ((-1 +ℤ negsuc n) +ℤ l)               ≡[ i ]⟨ scalar (+ℤAssoc -1 (negsuc n) l (~ i)) ⟩
    scalar (-1 +ℤ (negsuc n +ℤ l))               ≡⟨ +HomScalar -1 (negsuc n +ℤ l) ⟩
    - 1r + scalar (negsuc n +ℤ l)                 ≡[ i ]⟨ - 1r + +HomScalar (negsuc n) l i ⟩
    - 1r + (scalar (negsuc n) + scalar l)         ≡⟨ +Assoc (- 1r) _ _ ⟩
    (- 1r + (scalar (negsuc n))) + scalar l       ≡⟨ refl ⟩
    (- 1r + - scalar (pos (ℕ.suc n))) + scalar l ≡[ i ]⟨ -Dist 1r (scalar (pos (ℕ.suc n))) i + scalar l ⟩
    (- (1r + scalar (pos (ℕ.suc n)))) + scalar l ≡⟨ refl ⟩
    scalar (negsuc (ℕ.suc n)) + scalar l ∎


  lemma1 : (n : ℕ)
          → 1r + scalar (pos n) ≡ scalar (pos (ℕ.suc n))
  lemma1 ℕ.zero = +IdR _
  lemma1 (ℕ.suc k) = refl

  lemma-1 : (n : ℕ)
          → - 1r + scalar (negsuc n) ≡ scalar (negsuc (ℕ.suc n))
  lemma-1 ℕ.zero = -Dist _ _
  lemma-1 (ℕ.suc k) =
    - 1r + scalar (negsuc (ℕ.suc k))        ≡⟨ refl ⟩
    - 1r + - scalar (pos (ℕ.suc (ℕ.suc k))) ≡⟨ -Dist _ _ ⟩
    - (1r + scalar (pos (ℕ.suc (ℕ.suc k)))) ≡⟨ refl ⟩
    scalar (negsuc (ℕ.suc (ℕ.suc k))) ∎

  ·HomScalar : (k l : ℤ)
             → scalar (k ·ℤ l) ≡ scalar k · scalar l
  ·HomScalar (pos ℕ.zero) l =  0r ≡⟨ sym (0LeftAnnihilates (scalar l)) ⟩ 0r · scalar l ∎
  ·HomScalar (pos (ℕ.suc n)) l =
    scalar (l +ℤ (pos n ·ℤ l))                  ≡⟨ +HomScalar l (pos n ·ℤ l) ⟩
    scalar l + scalar (pos n ·ℤ l)              ≡[ i ]⟨ scalar l + ·HomScalar (pos n) l i ⟩
    scalar l + (scalar (pos n) · scalar l)      ≡[ i ]⟨ ·IdL (scalar l) (~ i) + (scalar (pos n) · scalar l) ⟩
    1r · scalar l + (scalar (pos n) · scalar l) ≡⟨ sym (·DistL+ 1r _ _) ⟩
    (1r + scalar (pos n)) · scalar l            ≡[ i ]⟨ lemma1 n i · scalar l ⟩
    scalar (pos (ℕ.suc n)) · scalar l ∎

  ·HomScalar (negsuc ℕ.zero) l =
    scalar (-ℤ l)                     ≡⟨ -DistScalar l ⟩
    - scalar l                        ≡[ i ]⟨ - (·IdL (scalar l) (~ i)) ⟩
    - (1r · scalar l)                 ≡⟨ sym (-DistL· _ _) ⟩
    - 1r · scalar l                   ≡⟨ refl ⟩
    scalar (negsuc ℕ.zero) · scalar l ∎

  ·HomScalar (negsuc (ℕ.suc n)) l =
    scalar ((-ℤ l) +ℤ (negsuc n ·ℤ l))             ≡⟨ +HomScalar (-ℤ l) (negsuc n ·ℤ l) ⟩
    scalar (-ℤ l) + scalar (negsuc n ·ℤ l)         ≡[ i ]⟨ -DistScalar l i + scalar (negsuc n ·ℤ l) ⟩
    - scalar l + scalar (negsuc n ·ℤ l)            ≡[ i ]⟨ - scalar l + ·HomScalar (negsuc n) l i ⟩
    - scalar l + scalar (negsuc n) · scalar l      ≡[ i ]⟨ (- ·IdL (scalar l) (~ i))
                                                           + scalar (negsuc n) · scalar l ⟩
    - (1r · scalar l) + scalar (negsuc n) · scalar l ≡[ i ]⟨ -DistL· 1r (scalar l) (~ i)
                                                            + scalar (negsuc n) · scalar l ⟩
    - 1r · scalar l + scalar (negsuc n) · scalar l ≡⟨ sym (·DistL+ _ _ _) ⟩
    (- 1r + scalar (negsuc n)) · scalar l          ≡[ i ]⟨ lemma-1 n i · scalar l ⟩
    scalar (negsuc (ℕ.suc n)) · scalar l ∎

CommRing→RawℤAlgebra : CommRing ℓ → RawAlgebra ℤAsRawRing ℓ
CommRing→RawℤAlgebra (R , commringstr 0r 1r _+_ _·_ -_ isCommRing) =
  rawalgebra R (scalar ((R , commringstr 0r 1r _+_ _·_ -_ isCommRing))) 0r 1r _+_ _·_ -_
