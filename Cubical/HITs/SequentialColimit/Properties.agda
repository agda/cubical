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
    incl∞ : (n : ℕ) → X .obj n → SeqColim X
    incl∞ n = incl {n = n}

  record ElimData (P : SeqColim X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      inclP : {k : ℕ} (x : X .obj k) → P (incl x)
      pushP : {k : ℕ} (x : X .obj k) → PathP (λ i → P (push x i)) (inclP x) (inclP (X .map x))

  record ElimDataShifted (n : ℕ)(P : SeqColim X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      inclP : {k : ℕ} (x : X .obj (k + n)) → P (incl x)
      pushP : {k : ℕ} (x : X .obj (k + n)) → PathP (λ i → P (push x i)) (inclP x) (inclP (X .map x))

  open ElimData
  open ElimDataShifted

  ElimData→ElimDataShifted : (n : ℕ)(P : SeqColim X → Type ℓ')
    → ElimData P → ElimDataShifted n P
  ElimData→ElimDataShifted n P datum .inclP = datum .inclP
  ElimData→ElimDataShifted n P datum .pushP = datum .pushP

  -- Preliminary lemmas
  -- The difficulty is mainly due to natural numbers having no strict +-commutativity

  private
    alg-path : (a b : ℕ) → a + (1 + b) ≡ 1 + (a + b)
    alg-path a b = +-assoc a 1 b ∙ (λ i → +-comm a 1 i + b)

  module _
    (P : SeqColim X → Type ℓ')
    (datum : ElimDataShifted 0 P) where

    +-zero-0 : refl ≡ +-zero 0
    +-zero-0 i j = isSet→SquareP (λ i j → isSetℕ) refl refl refl (+-zero 0) j i

    inclP'-filler : (k : ℕ) → (i : I) → (x : X .obj (+-zero k i)) → P (incl x)
    inclP'-filler k i = transport-filler (λ i → (x : X .obj (+-zero k i)) → P (incl x)) (datum .inclP) i

    inclP' : (k : ℕ) → (x : X .obj k) → P (incl x)
    inclP' k = inclP'-filler k i1

    inclP'-0-eq : datum .inclP ≡ inclP' 0
    inclP'-0-eq = sym (transportRefl _)
      ∙ (λ j → transport (λ i → (x : X .obj (+-zero-0 j i)) → P (incl x)) (datum .inclP {k = 0}))

    pushP' : (k : ℕ)
      → (x : X .obj k)
      → PathP (λ i → P (push x i)) (inclP' k x) (inclP' (1 + k) (X .map x))
    pushP' k = transport
      (λ i → (x : X .obj (+-zero k i)) →
        PathP (λ i → P (push x i)) (inclP'-filler k i x) (inclP'-filler (1 + k) i (X .map x))) (datum .pushP)

    ElimDataShifted0→ElimData : ElimData P
    ElimDataShifted0→ElimData .inclP = inclP' _
    ElimDataShifted0→ElimData .pushP = pushP' _

  module _
    (n : ℕ)(P : SeqColim X → Type ℓ')
    (datum : ElimDataShifted (1 + n) P) where

    alg-path-0 : (b : ℕ) → refl ≡ alg-path 0 b
    alg-path-0 b i j = isSet→SquareP (λ i j → isSetℕ) refl refl refl (alg-path 0 b) j i

    inclP-n-filler : (k : ℕ) → (i : I) → ((x : X .obj (alg-path k n i)) → P (incl x))
    inclP-n-filler k i = transport-filler (λ i → (x : X .obj (alg-path k n i)) → P (incl x)) (datum .inclP) i

    inclP-n : (k : ℕ) → (x : X .obj ((1 + k) + n)) → P (incl x)
    inclP-n k = inclP-n-filler k i1

    pushP-n : (k : ℕ)
      → (x : X .obj ((1 + k) + n))
      → PathP (λ i → P (push x i)) (inclP-n k x) (inclP-n (1 + k) (X .map x))
    pushP-n k =
      transport
        (λ i → (x : X .obj (alg-path k n i)) →
          PathP (λ i → P (push x i)) (inclP-n-filler k i x) (inclP-n-filler (1 + k) i (X .map x))) (datum .pushP)

    inclP-0-filler : (x : X .obj n) → (i : I) → P (push x i)
    inclP-0-filler x i = transport-filler (λ i → P (push x (~ i))) (datum .inclP {k = 0} (X .map x)) (~ i)

    inclP-0 : (x : X .obj n) → P (incl x)
    inclP-0 x = inclP-0-filler x i0

    inclP-0-eq : datum .inclP {k = 0} ≡ inclP-n 0
    inclP-0-eq = sym (transportRefl _)
      ∙ (λ j → transport (λ i → (x : X .obj (alg-path-0 n j i)) → P (incl x)) (datum .inclP {k = 0}))

    pushP-0 :
        (x : X .obj n)
      → PathP (λ i → P (push x i)) (inclP-0 x) (inclP-n 0 (X .map x))
    pushP-0 x i =
      hcomp (λ j → λ
          { (i = i0) → inclP-0 x
          ; (i = i1) → inclP-0-eq j (X .map x) })
        (inclP-0-filler x i)

    elimShiftedSuc : ElimDataShifted n P
    elimShiftedSuc .inclP {k = 0}     = inclP-0
    elimShiftedSuc .inclP {k = suc k} = inclP-n k
    elimShiftedSuc .pushP {k = 0}     = pushP-0
    elimShiftedSuc .pushP {k = suc k} = pushP-n k

  -- The eliminators

  elim :
      (P : SeqColim X → Type ℓ')
    → ElimData P
    → (x : SeqColim X) → P x
  elim P datum (incl x)   = datum .inclP x
  elim P datum (push x i) = datum .pushP x i

  elimShifted : (n : ℕ)
    → (P : SeqColim X → Type ℓ')
    → ElimDataShifted n P
    → (x : SeqColim X) → P x
  elimShifted 0 _ datum = elim _ (ElimDataShifted0→ElimData _ datum)
  elimShifted (suc n) _ datum = elimShifted n _ (elimShiftedSuc _ _ datum)

  elimShiftedβ : (n : ℕ)(k : ℕ)
    → (P : SeqColim X → Type ℓ')
    → (datum : ElimDataShifted n P)
    → elimShifted _ _ datum ∘ incl∞ (k + n) ≡ datum .inclP
  elimShiftedβ 0 0 _ datum = sym (inclP'-0-eq _ datum)
  elimShiftedβ 0 (suc k) P datum =
    transport (λ i → elimShifted _ _ datum ∘ incl∞ (+-zero (suc k) (~ i))
      ≡ inclP'-filler P datum (suc k) (~ i)) refl
  elimShiftedβ (suc n) 0 _ datum =
      elimShiftedβ n _ _ (elimShiftedSuc _ _ datum)
    ∙ sym (inclP-0-eq _ _ datum)
  elimShiftedβ (suc n) (suc k) P datum =
    transport (λ i → elimShifted _ _ datum ∘ incl∞ (alg-path (suc k) n (~ i))
      ≡ inclP-n-filler n P datum (suc k) (~ i))
      (elimShiftedβ n (suc (suc k)) P (elimShiftedSuc _ _ datum))

  -- Lemma to lift sections

  open Iso

  private
    transpSec :
      (n : ℕ)(Y : SeqColim X → Type ℓ')
      (sec : (x : X .obj n) → Y (incl x))
      → (x : X .obj n) → Y (incl (X .map x))
    transpSec n Y sec x = transport (λ i → Y (push x i)) (sec x)

    module _
      (d : ℕ)(n : ℕ)
      (conn : isConnectedFun d (X .map {n = n}))
      (Y : SeqColim X → TypeOfHLevel ℓ' d) where

      module _
        (sec : (x : X .obj n) → Y (incl (X .map x)) .fst) where

        lift-iso = elim.isIsoPrecompose _ d (Y ∘ incl) conn

        liftSec' : (x : X .obj (1 + n)) → Y (incl x) .fst
        liftSec' = lift-iso .inv sec

        liftSecPath' : (x : X .obj n) → sec x ≡ liftSec' (X .map x)
        liftSecPath' x i = lift-iso .rightInv sec (~ i) x

      module _
        (sec : (x : X .obj n) → Y (incl x) .fst) where

        liftSec : (x : X .obj (1 + n)) → Y (incl x) .fst
        liftSec = liftSec' (transpSec n (λ x → Y x .fst) sec)

        liftSecPath :
          (x : X .obj n)
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
        (Y : SeqColim X → TypeOfHLevel ℓ' d) where

        lifting : (k : ℕ)(sec : (x : X .obj n) → Y (incl x) .fst)
          → (x : X .obj (k + n)) → Y (incl x) .fst
        lifting 0 sec = sec
        lifting (suc k) sec = liftSec d _ (conn _) Y (lifting k sec)

        liftingPath : (k : ℕ)(sec : (x : X .obj n) → Y (incl x) .fst)
          → (x : X .obj (k + n))
          → PathP (λ i → Y (push x i) .fst) (lifting k sec x) (lifting (1 + k) sec (X .map x))
        liftingPath k sec = liftSecPath d _ (conn _) Y (lifting k sec)

        liftingData : ((x : X .obj n) → Y (incl x) .fst) → ElimDataShifted n (λ x → Y x .fst)
        liftingData sec .inclP = lifting _ sec
        liftingData sec .pushP = liftingPath _ sec

        hasSectionIncl∘ : hasSection (λ (sec : (x : SeqColim X) → Y x .fst) → sec ∘ incl {n = n})
        hasSectionIncl∘ .fst sec = elimShifted  _ _   (liftingData sec)
        hasSectionIncl∘ .snd sec = elimShiftedβ _ _ _ (liftingData sec)

    -- Connectivity of inclusion map

    isConnectedIncl∞ : isConnectedFun d (incl∞ n)
    isConnectedIncl∞ = elim.isConnectedPrecompose _ _ hasSectionIncl∘
