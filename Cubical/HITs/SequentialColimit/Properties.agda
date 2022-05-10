{-

This file contains:
  - Eliminators of direct limit, especially an index-shifting version;
  - Connectivity of inclusion maps.

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.SequentialColimit.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat hiding (elim)
open import Cubical.HITs.SequentialColimit.Base
open import Cubical.Homotopy.Connected

private
  variable
    ℓ ℓ' : Level

module _
  (X : Sequence ℓ) where

  open Sequence

  private
    inl∞ : (n : ℕ) → X .space n → Lim→ X
    inl∞ n = inl {n = n}

  record ElimData (P : Lim→ X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      finl  : {k : ℕ}(x : X .space k) → P (inl x)
      fpush : {k : ℕ}(x : X .space k) → PathP (λ i → P (push x i)) (finl x) (finl (X .map x))

  record ElimShiftData (n : ℕ)(P : Lim→ X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      finl  : {k : ℕ}(x : X .space (k + n)) → P (inl x)
      fpush : {k : ℕ}(x : X .space (k + n)) → PathP (λ i → P (push x i)) (finl x) (finl (X .map x))

  open ElimData
  open ElimShiftData

  ElimData→ElimShiftData : (n : ℕ)(P : Lim→ X → Type ℓ')
    → ElimData P → ElimShiftData n P
  ElimData→ElimShiftData n P datum .finl  = datum .finl
  ElimData→ElimShiftData n P datum .fpush = datum .fpush

  -- Preliminary lemmas
  -- The difficulty is mainly due to natural numbers having no strict +-commutativity

  private
    alg-path : (a b : ℕ) → a + (1 + b) ≡ 1 + (a + b)
    alg-path a b = +-assoc a 1 b ∙ (λ i → +-comm a 1 i + b)

  module _
    (P : Lim→ X → Type ℓ')
    (datum : ElimShiftData 0 P) where

    +-zero-0 : refl ≡ +-zero 0
    +-zero-0 i j = isSet→SquareP (λ i j → isSetℕ) refl refl refl (+-zero 0) j i

    finl'-filler : (k : ℕ) → (i : I) → (x : X .space (+-zero k i)) → P (inl x)
    finl'-filler k i = transport-filler (λ i → (x : X .space (+-zero k i)) → P (inl x)) (datum .finl) i

    finl' : (k : ℕ) → (x : X .space k) → P (inl x)
    finl' k = finl'-filler k i1

    finl'-0-eq : datum .finl ≡ finl' 0
    finl'-0-eq = sym (transportRefl _)
      ∙ (λ j → transport (λ i → (x : X .space (+-zero-0 j i)) → P (inl x)) (datum .finl {k = 0}))

    fpush' : (k : ℕ)
      → (x : X .space k)
      → PathP (λ i → P (push x i)) (finl' k x) (finl' (1 + k) (X .map x))
    fpush' k = transport
      (λ i → (x : X .space (+-zero k i)) →
        PathP (λ i → P (push x i)) (finl'-filler k i x) (finl'-filler (1 + k) i (X .map x))) (datum .fpush)

    ElimShiftData0→ElimData : ElimData P
    ElimShiftData0→ElimData .finl  = finl'  _
    ElimShiftData0→ElimData .fpush = fpush' _

  module _
    (n : ℕ)(P : Lim→ X → Type ℓ')
    (datum : ElimShiftData (1 + n) P) where

    alg-path-0 : (b : ℕ) → refl ≡ alg-path 0 b
    alg-path-0 b i j = isSet→SquareP (λ i j → isSetℕ) refl refl refl (alg-path 0 b) j i

    finl-n-filler : (k : ℕ) → (i : I) → ((x : X .space (alg-path k n i)) → P (inl x))
    finl-n-filler k i = transport-filler (λ i → (x : X .space (alg-path k n i)) → P (inl x)) (datum .finl) i

    finl-n : (k : ℕ) → (x : X .space ((1 + k) + n)) → P (inl x)
    finl-n k = finl-n-filler k i1

    fpush-n : (k : ℕ)
      → (x : X .space ((1 + k) + n))
      → PathP (λ i → P (push x i)) (finl-n k x) (finl-n (1 + k) (X .map x))
    fpush-n k =
      transport
        (λ i → (x : X .space (alg-path k n i)) →
          PathP (λ i → P (push x i)) (finl-n-filler k i x) (finl-n-filler (1 + k) i (X .map x))) (datum .fpush)

    finl-0-filler : (x : X .space n) → (i : I) → P (push x i)
    finl-0-filler x i = transport-filler (λ i → P (push x (~ i))) (datum .finl {k = 0} (X .map x)) (~ i)

    finl-0 : (x : X .space n) → P (inl x)
    finl-0 x = finl-0-filler x i0

    finl-0-eq : datum .finl {k = 0} ≡ finl-n 0
    finl-0-eq = sym (transportRefl _)
      ∙ (λ j → transport (λ i → (x : X .space (alg-path-0 n j i)) → P (inl x)) (datum .finl {k = 0}))

    fpush-0 :
        (x : X .space n)
      → PathP (λ i → P (push x i)) (finl-0 x) (finl-n 0 (X .map x))
    fpush-0 x i =
      hcomp (λ j → λ
          { (i = i0) → finl-0 x
          ; (i = i1) → finl-0-eq j (X .map x) })
        (finl-0-filler x i)

    elimShiftDataSuc : ElimShiftData n P
    elimShiftDataSuc .finl  {k = 0} = finl-0
    elimShiftDataSuc .finl  {k = suc k} = finl-n k
    elimShiftDataSuc .fpush {k = 0} = fpush-0
    elimShiftDataSuc .fpush {k = suc k} = fpush-n k

  -- The eliminators

  elim :
      (P : Lim→ X → Type ℓ')
    → ElimData P
    → (x : Lim→ X) → P x
  elim P datum (inl x) = datum .finl x
  elim P datum (push x i) = datum .fpush x i

  elimShift : (n : ℕ)
    → (P : Lim→ X → Type ℓ')
    → ElimShiftData n P
    → (x : Lim→ X) → P x
  elimShift 0 _ datum = elim _ (ElimShiftData0→ElimData _ datum)
  elimShift (suc n) _ datum = elimShift n _ (elimShiftDataSuc _ _ datum)

  elimShiftβ : (n : ℕ)(k : ℕ)
    → (P : Lim→ X → Type ℓ')
    → (datum : ElimShiftData n P)
    → elimShift _ _ datum ∘ inl∞ (k + n) ≡ datum .finl
  elimShiftβ 0 0 _ datum = sym (finl'-0-eq _ datum)
  elimShiftβ 0 (suc k) P datum =
    transport (λ i → elimShift _ _ datum ∘ inl∞ (+-zero (suc k) (~ i))
      ≡ finl'-filler P datum (suc k) (~ i)) refl
  elimShiftβ (suc n) 0 _ datum =
      elimShiftβ n _ _ (elimShiftDataSuc _ _ datum)
    ∙ sym (finl-0-eq _ _ datum)
  elimShiftβ (suc n) (suc k) P datum =
    transport (λ i → elimShift _ _ datum ∘ inl∞ (alg-path (suc k) n (~ i))
      ≡ finl-n-filler n P datum (suc k) (~ i))
      (elimShiftβ n (suc (suc k)) P (elimShiftDataSuc _ _ datum))

  -- Lemma to lift sections

  open Iso

  private
    transpSec :
      (n : ℕ)(Y : Lim→ X → Type ℓ')
      (sec : (x : X .space n) → Y (inl x))
      → (x : X .space n) → Y (inl (X .map x))
    transpSec n Y sec x = transport (λ i → Y (push x i)) (sec x)

    module _
      (d : ℕ)(n : ℕ)
      (conn : isConnectedFun d (X .map {n = n}))
      (Y : Lim→ X → TypeOfHLevel ℓ' d) where

      module _
        (sec : (x : X .space n) → Y (inl (X .map x)) .fst) where

        lift-iso = elim.isIsoPrecompose _ d (Y ∘ inl) conn

        liftSec' : (x : X .space (1 + n)) → Y (inl x) .fst
        liftSec' = lift-iso .inv sec

        liftSecPath' : (x : X .space n) → sec x ≡ liftSec' (X .map x)
        liftSecPath' x i = lift-iso .rightInv sec (~ i) x

      module _
        (sec : (x : X .space n) → Y (inl x) .fst) where

        liftSec : (x : X .space (1 + n)) → Y (inl x) .fst
        liftSec = liftSec' (transpSec n (λ x → Y x .fst) sec)

        liftSecPath :
          (x : X .space n)
          → PathP (λ i → Y (push x i) .fst) (sec x) (liftSec (X .map x))
        liftSecPath x i =
          hcomp (λ j → λ
            { (i = i0) → sec x
            ; (i = i1) → liftSecPath'
                (transpSec n (λ x → Y x .fst) sec) x j })
          (transport-filler (λ i → Y (push x i) .fst) (sec x) i)

  module _
    (d : ℕ)(n : ℕ)
    (conn : (k : ℕ) → isConnectedFun d (X .map {n = k + n})) where

    private
      module _
        (Y : Lim→ X → TypeOfHLevel ℓ' d) where

        lifting : (k : ℕ)(sec : (x : X .space n) → Y (inl x) .fst)
          → (x : X .space (k + n)) → Y (inl x) .fst
        lifting 0 sec = sec
        lifting (suc k) sec = liftSec d _ (conn _) Y (lifting k sec)

        liftingPath : (k : ℕ)(sec : (x : X .space n) → Y (inl x) .fst)
          → (x : X .space (k + n))
          → PathP (λ i → Y (push x i) .fst) (lifting k sec x) (lifting (1 + k) sec (X .map x))
        liftingPath k sec = liftSecPath d _ (conn _) Y (lifting k sec)

        liftingData : ((x : X .space n) → Y (inl x) .fst) → ElimShiftData n (λ x → Y x .fst)
        liftingData sec .finl  = lifting _ sec
        liftingData sec .fpush = liftingPath _ sec

        hasSectionInl∘ : hasSection (λ (sec : (x : Lim→ X) → Y x .fst) → sec ∘ inl {n = n})
        hasSectionInl∘ .fst sec = elimShift  _ _   (liftingData sec)
        hasSectionInl∘ .snd sec = elimShiftβ _ _ _ (liftingData sec)

    -- Connectivity of inclusion map

    isConnectedInl∞ : isConnectedFun d (inl∞ n)
    isConnectedInl∞ = elim.isConnectedPrecompose _ _ hasSectionInl∘
