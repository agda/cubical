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
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

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

open Sequence
open ElimDataShifted
-- Proof that colim Aₘ ≃ Aₙ for a converging sequence
-- A₀ → A₁ → ... → Aₙ ≃ Aₙ₊₁ ≃ ...
module _ {ℓ : Level} (seq : Sequence ℓ) (n : ℕ) (term : converges seq n)
  where
  shiftEq : ∀ {k} → seq .obj n ≃ (seq .obj (k + n))
  shiftEq {k = zero} = idEquiv _
  shiftEq {k = suc k} = compEquiv (shiftEq {k}) (_ , term k)

  shiftEqCoh : (k : ℕ) (x : _)
    → invEq shiftEq x
     ≡ invEq (compEquiv shiftEq (Sequence.map seq , term k)) (seq .Sequence.map x)
  shiftEqCoh zero x = sym (retEq (_ , term 0) x)
  shiftEqCoh (suc k) x =
    cong (invEq shiftEq) (sym (retEq (_ , term (suc k)) x))

  shiftEqShifted : ElimDataShifted seq n (λ _ → obj seq n)
  inclP shiftEqShifted = invEq shiftEq
  pushP shiftEqShifted = shiftEqCoh _

  -- induction principle for terminating sequences
  module _ {P : (k : ℕ) → seq .obj (k + n) → Type ℓ}
           (bs : (s : _) → P zero s)
           (indr : (k : ℕ) → ((y : _) → P k y) →  (x : _) → P (suc k) (Sequence.map seq x))
           where
    terminaates-seq-ind :  (k : ℕ) (x : _) → P k x
    terminaates-seq-ind zero = bs
    terminaates-seq-ind (suc k) x =
      subst (P (suc k)) (secEq (_ , term k) x)
            (indr k (terminaates-seq-ind k) (invEq (_ , term k) x))

    terminaates-seq-indβ : (k : ℕ) (s : ((y : seq .obj (k + n)) → P k y)) (x : _)
      → terminaates-seq-ind (suc k) (Sequence.map seq x)
       ≡ indr k (terminaates-seq-ind k) x
    terminaates-seq-indβ k s x =
        lem (Sequence.map seq , term k) x (P (suc k))
             (indr k (terminaates-seq-ind k))
      where
      lem : ∀ {ℓ ℓ'} {A B : Type ℓ} (e : A ≃ B) (x : A)
            (P : B → Type ℓ') (πP : (x : A) → P (fst e x))
        → subst P (secEq e (fst e x)) (πP (invEq e (fst e x))) ≡ πP x
      lem {ℓ' = ℓ'} {B = B} =
        EquivJ (λ A e → (x : A) (P : B → Type ℓ') (πP : (x : A) → P (fst e x))
                      → subst P (secEq e (fst e x)) (πP (invEq e (fst e x)))
                       ≡ πP x)
               λ b P πP → transportRefl _

  -- a special case
  module _
    (0case : (x : seq .obj n)
      → Path (SeqColim seq)
              (incl (elimShifted seq n (λ _ → obj seq n) shiftEqShifted (incl x)))
              (incl x)) where

    converges→ColimIso-main-lem : (k : ℕ) (x : seq .obj (k + n))
      → Path (SeqColim seq)
              (incl (elimShifted seq n (λ _ → obj seq n)
                                 shiftEqShifted (incl x)))
              (incl x)
    converges→ColimIso-main-lem =
      terminaates-seq-ind
        0case
        (λ k id x
        → cong incl
          (sym (cong (elimShifted seq n (λ _ → obj seq n) shiftEqShifted) (push x)))
             ∙∙ id x
             ∙∙ push x)

    converges→ColimIso-main-lemβ : (k : ℕ) (x : seq .obj (k + n))
        → converges→ColimIso-main-lem (suc k) (Sequence.map seq x)
         ≡ (cong incl
           (sym (cong (elimShifted seq n (λ _ → obj seq n)
                                    shiftEqShifted) (push x)))
             ∙∙ converges→ColimIso-main-lem k x
             ∙∙ push x)
    converges→ColimIso-main-lemβ k x =
      terminaates-seq-indβ
        0case
        (λ k id x
        → cong incl
          (sym (cong (elimShifted seq n (λ _ → obj seq n) shiftEqShifted) (push x)))
        ∙∙ id x
        ∙∙ push x)
        k (converges→ColimIso-main-lem k) x

-- main result
-- (todo: add more thy about colimits to get nicer proof)
converges→ColimIso : ∀ {ℓ} {seq : Sequence ℓ} (n : ℕ)
  → converges seq n
  → Iso (obj seq n) (SeqColim seq)
Iso.fun (converges→ColimIso {seq = seq} n e) = incl
Iso.inv (converges→ColimIso {seq = seq} n e) = elimShifted seq n _ (shiftEqShifted seq n e)
Iso.rightInv (converges→ColimIso {seq = seq} n e) = elimShifted seq n _
  (record { inclP = λ {k} → paths k
          ; pushP = λ {k} → cohs k})
  where
  zero-case : (x : seq .obj n)
    → Path (SeqColim seq)
            (incl (elimShifted seq n (λ _ → obj seq n) (shiftEqShifted seq n e) (incl x)))
            (incl x)
  zero-case x i = incl (elimShiftedβ seq n 0 (λ _ → obj seq n) (shiftEqShifted seq n e) i x)

  paths : (k : ℕ) → (x : seq .obj (k + n))
    → Path (SeqColim seq)
            (incl (elimShifted seq n (λ _ → obj seq n) (shiftEqShifted seq n e) (incl x)))
            (incl x)
  paths = converges→ColimIso-main-lem seq n e zero-case

  cohs : (k : ℕ) (x : seq .obj (k + n))
    → PathP (λ i → Path (SeqColim seq)
                          (incl (elimShifted seq n (λ _ → obj seq n)
                                  (shiftEqShifted seq n e)
                          (push x i)))
                          (push x i))
             (paths k x) (paths (suc k) (seq .Sequence.map x))
  cohs k x =
    doubleCompPath-filler
      (λ i → incl (elimShifted seq n (λ _ → obj seq n)
                     (shiftEqShifted seq n e) (push x (~ i))))
      (converges→ColimIso-main-lem seq n e zero-case k x)
      (push x)
    ▷ sym (converges→ColimIso-main-lemβ seq n e (zero-case) k x)
Iso.leftInv (converges→ColimIso {seq = seq} n e) a =
    funExt⁻ (elimShiftedβ seq n _ (λ _ → obj seq n)
             (shiftEqShifted seq n e)) a

-- different form
converges→isEquivIncl : ∀ {ℓ} {seq : Sequence ℓ} (n : ℕ)
  → converges seq n
  → isEquiv {A = obj seq n} {B = SeqColim seq} (incl {n = n})
converges→isEquivIncl n x = isoToEquiv (converges→ColimIso n x) .snd

-- elimination from colimit into prop
SeqColim→Prop : ∀ {ℓ ℓ'} {C : Sequence ℓ} {B : SeqColim C → Type ℓ'}
  → ((x : _) → isProp (B x))
  → (s : (n : ℕ) (x : obj C n) → B (incl x))
  → (x : _) → B x
SeqColim→Prop {C = C} pr ind (incl x) = ind _ x
SeqColim→Prop {C = C} {B = B} pr ind (push x i) =
  isProp→PathP {B = λ i → B (push x i)}
    (λ i → pr _)
    (ind _ x) (ind (suc _) (C .Sequence.map x)) i
