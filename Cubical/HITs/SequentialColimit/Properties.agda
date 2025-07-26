{-

This file contains:
  - Eliminators of direct limit, especially an index-shifting version;
  - Connectivity of inclusion maps.
  - Characterisation of colimits over finite sequences

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
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sequence
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sigma

open import Cubical.HITs.SequentialColimit.Base
open import Cubical.Homotopy.Connected

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  (X : Sequence ℓ) where

  open Sequence

  private
    incl∞ : (n : ℕ) → X .obj n → SeqColim X
    incl∞ n = incl {n = n}

  record ElimData (P : SeqColim X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor elimdata
    field
      inclP : {k : ℕ} (x : X .obj k) → P (incl x)
      pushP : {k : ℕ} (x : X .obj k) → PathP (λ i → P (push x i)) (inclP x) (inclP (X .map x))

  record ElimDataShifted (n : ℕ)(P : SeqColim X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor elimdata-shift
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
    terminates-seq-ind :  (k : ℕ) (x : _) → P k x
    terminates-seq-ind zero = bs
    terminates-seq-ind (suc k) x =
      subst (P (suc k)) (secEq (_ , term k) x)
            (indr k (terminates-seq-ind k) (invEq (_ , term k) x))

    terminates-seq-indβ : (k : ℕ) (s : ((y : seq .obj (k + n)) → P k y)) (x : _)
      → terminates-seq-ind (suc k) (Sequence.map seq x)
       ≡ indr k (terminates-seq-ind k) x
    terminates-seq-indβ k s x =
        lem (Sequence.map seq , term k) x (P (suc k))
             (indr k (terminates-seq-ind k))
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
      terminates-seq-ind
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
      terminates-seq-indβ
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
  (elimdata-shift (λ {k} → paths k) (λ {k} → cohs k))
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

realiseIdSequenceMap : {C : Sequence ℓ} → realiseSequenceMap (idSequenceMap C) ≡ idfun _
realiseIdSequenceMap {C = C} =
  funExt λ { (incl x) → refl
           ; (push {n = n} x i) j → rUnit (push {n = n} x) (~ j) i}

realiseCompSequenceMap : {C : Sequence ℓ} {D : Sequence ℓ'} {E : Sequence ℓ''}
  (g : SequenceMap D E) (f : SequenceMap C D)
  → realiseSequenceMap (composeSequenceMap g f)
   ≡ realiseSequenceMap g ∘ realiseSequenceMap f
realiseCompSequenceMap {C = C} {E = E} g f =
  funExt λ { (incl x) → refl
           ; (push {n = n} x i) j → main n x j i}
  where
  module _ (n : ℕ) (x : Sequence.obj C n) where
    g₁ = g .SequenceMap.map n
    g₊ =  g .SequenceMap.map (suc n)
    f₁ = f .SequenceMap.map n

    main : Path (Path (SeqColim E) _ _)
                (push {n = n} (g₁ (f₁ x))
                ∙ cong incl (SequenceMap.comm g n (f₁ x)
                           ∙ cong g₊ (SequenceMap.comm f n x)))
                (cong (realiseSequenceMap g)
                  (push (f₁ x) ∙ cong incl (SequenceMap.comm f n x)))
    main = cong (push (SequenceMap.map g n (f₁ x)) ∙_)
                      (cong-∙ incl (SequenceMap.comm g n (f₁ x))
                                   (cong g₊ (SequenceMap.comm f n x)))
      ∙ assoc (push (SequenceMap.map g n (f₁ x)))
               (cong incl (SequenceMap.comm g n (f₁ x)))
               (cong (incl ∘ g₊) (SequenceMap.comm f n x))
      ∙ sym (cong-∙ (realiseSequenceMap g)
                    (push (f₁ x)) (cong incl (SequenceMap.comm f n x)))

sequenceEquiv→ColimIso : {A B : Sequence ℓ}
  → SequenceEquiv A B → Iso (SeqColim A) (SeqColim B)
sequenceEquiv→ColimIso e = mainIso
  where
  main : {A : Sequence ℓ} (B : Sequence ℓ) (e : SequenceEquiv A B)
    → section (realiseSequenceMap (fst e))
               (realiseSequenceMap (fst (invSequenceEquiv e)))
     × retract (realiseSequenceMap (fst e))
               (realiseSequenceMap (fst (invSequenceEquiv e)))
  main {A = A} = SequenceEquivJ>
    ((λ x → (λ i → realiseIdSequenceMap {C = A} i
                    (realiseSequenceMap (fst (invIdSequenceEquiv {A = A} i)) x))
           ∙ funExt⁻ realiseIdSequenceMap x)
   , λ x → (λ i → realiseSequenceMap (fst (invIdSequenceEquiv {A = A} i))
                      (realiseIdSequenceMap {C = A} i x))
           ∙ funExt⁻ realiseIdSequenceMap x)

  mainIso : Iso _ _
  Iso.fun mainIso = realiseSequenceMap (fst e)
  Iso.inv mainIso = realiseSequenceMap (fst (invSequenceEquiv e))
  Iso.rightInv mainIso = main _ e .fst
  Iso.leftInv mainIso = main _ e .snd

sequenceIso→ColimIso : {A B : Sequence ℓ}
  → SequenceIso A B → Iso (SeqColim A) (SeqColim B)
sequenceIso→ColimIso e =
  sequenceEquiv→ColimIso (SequenceIso→SequenceEquiv e)

converges→funId : {seq1 : Sequence ℓ} {seq2 : Sequence ℓ'}
  (n m : ℕ)
  → converges seq1 n
  → converges seq2 m
  → (f : SeqColim seq1 → SeqColim seq2)
  → (g : SequenceMap seq1 seq2)
  → ((n : ℕ) (c : _) → f (incl {n = n} c) ≡ incl (SequenceMap.map g n c))
  → f ≡ realiseSequenceMap g
converges→funId {seq1 = seq1} {seq2} n m t1 t2 f g p =
  transport (λ i → help f (~ i) ≡ help (realiseSequenceMap g) (~ i))
    (funExt λ x → p _ x)
  where
  help : (f : _) → PathP (λ i → isoToPath (converges→ColimIso {seq = seq1} n t1) (~ i)
                    → SeqColim seq2)
               f (f ∘ incl)
  help f = toPathP (funExt λ x → (λ i → transportRefl (f (incl (transportRefl x i))) i))

-- colim (X₀ → ... → Xₙ) ≃ colim (X₁ → ... → Xₙ)
module _ (X : Sequence ℓ) where
  ShiftSeq : Sequence ℓ
  obj ShiftSeq m = obj X (suc m)
  map ShiftSeq = map X

  Iso-FinSeqColim→FinSeqColim↑ : (m : ℕ)
     → Iso (FinSeqColim (suc m) X) (FinSeqColim m ShiftSeq)
  Iso-FinSeqColim→FinSeqColim↑ m = iso (G m) (F m) (F→G→F m) (G→F→G m)
    where
    F : (m : ℕ) → FinSeqColim m ShiftSeq → FinSeqColim (suc m) X
    F m (fincl n x) = fincl (fsuc n) x
    F (suc m) (fpush (n , p) x i) = fpush (suc n , p) x i

    G : (m : ℕ) → FinSeqColim (suc m) X → FinSeqColim m ShiftSeq
    G m (fincl (zero , p) x) = fincl (zero , p) (map X x)
    G m (fincl (suc n , p) x) = fincl (n , p) x
    G m (fpush (zero , p) x i) = fincl (zero , p) (map X x)
    G (suc m) (fpush (suc n , p) x i) = fpush (n , p) x i

    F→G→F : (m : ℕ) → (x : FinSeqColim m ShiftSeq) → G m (F m x) ≡ x
    F→G→F m (fincl n x) = refl
    F→G→F (suc m) (fpush n x i) = refl

    G→F→G : (m : ℕ) → (x : FinSeqColim (suc m) X) → F m (G m x) ≡ x
    G→F→G m (fincl (zero , p) x) = sym (fpush (zero , p) x)
    G→F→G m (fincl (suc n , p) x) = refl
    G→F→G m (fpush (zero , p) x i) j = fpush (zero , p) x (~ j ∨ i)
    G→F→G (suc m) (fpush (suc n , p) x i) = refl

  Iso-FinSeqColim₀-Top : Iso (FinSeqColim 0 X) (obj X zero)
  Iso.fun Iso-FinSeqColim₀-Top (fincl (zero , p) x) = x
  Iso.inv Iso-FinSeqColim₀-Top a = fincl fzero a
  Iso.rightInv Iso-FinSeqColim₀-Top a = refl
  Iso.leftInv Iso-FinSeqColim₀-Top (fincl (zero , p) x) = refl

pre-Iso-FinSeqColim-Top : (X : Sequence ℓ) (m : ℕ)
  → Iso (FinSeqColim m X) (obj X m)
pre-Iso-FinSeqColim-Top X zero = Iso-FinSeqColim₀-Top X
pre-Iso-FinSeqColim-Top X (suc m) =
  compIso (Iso-FinSeqColim→FinSeqColim↑ X m)
          (pre-Iso-FinSeqColim-Top (ShiftSeq X) m)

characInverse : (X : Sequence ℓ) (m : ℕ) (a : obj X m)
  → Iso.inv (pre-Iso-FinSeqColim-Top X m) a ≡ fincl flast a
characInverse X zero a = refl
characInverse X (suc m) a =
  cong (Iso.inv (Iso-FinSeqColim→FinSeqColim↑ X m)) (characInverse _ m a)

-- main result
Iso-FinSeqColim-Top : (X : Sequence ℓ) (m : ℕ)
  → Iso (FinSeqColim m X) (obj X m)
Iso.fun (Iso-FinSeqColim-Top X m) = Iso.fun (pre-Iso-FinSeqColim-Top X m)
Iso.inv (Iso-FinSeqColim-Top X m) = fincl flast
Iso.rightInv (Iso-FinSeqColim-Top X m) r =
  cong (Iso.fun (pre-Iso-FinSeqColim-Top X m)) (sym (characInverse X m r))
  ∙ Iso.rightInv (pre-Iso-FinSeqColim-Top X m) r
Iso.leftInv (Iso-FinSeqColim-Top X m) r =
    sym (characInverse X m (Iso.fun (pre-Iso-FinSeqColim-Top X m) r))
  ∙ Iso.leftInv (pre-Iso-FinSeqColim-Top X m) r

  -- main corollary : given two maps (f g : SeqColim Xᵢ → B) and a
  -- family of homotopies hᵢ : (x : Xᵢ) → f (incl x) ≡ g (incl x) for
  -- i < n, we can improve hᵢ such that they are compatible with push

→FinSeqColimHomotopy : ∀ {ℓ ℓ'}
  {X : Sequence ℓ} {m : ℕ} {B : FinSeqColim m X → Type ℓ'}
  (f g : (x : FinSeqColim m X) → B x)
  (h : (x : obj X m) → f (fincl flast x)
                      ≡ g (fincl flast x))
  → f ≡ g
→FinSeqColimHomotopy {X = X} {m} f g h = funExt
  (transport (λ i → (x : isoToPath (invIso (Iso-FinSeqColim-Top X m)) i)
    → f (ua-unglue (isoToEquiv (invIso (Iso-FinSeqColim-Top X m))) i x)
     ≡ g (ua-unglue (isoToEquiv (invIso (Iso-FinSeqColim-Top X m))) i x)) h)


-- Shifting colimits
Iso-SeqColim→SeqColimSuc : (X : Sequence ℓ)
  → Iso (SeqColim X) (SeqColim (ShiftSeq X))
Iso-SeqColim→SeqColimSuc X = iso G F F→G→F G→F→G
  where
  F : SeqColim (ShiftSeq X) → SeqColim X
  F (incl {n = n} x) = incl {n = suc n} x
  F (push {n = n} x i) = push {n = suc n} x i

  G : SeqColim X → SeqColim (ShiftSeq X)
  G (incl {n = zero} x) = incl {n = zero} (map X x)
  G (incl {n = suc n} x) = incl {n = n} x
  G (push {n = zero} x i) = incl {n = zero} (map X x)
  G (push {n = suc n} x i) = push {n = n} x i

  F→G→F : (x : SeqColim (ShiftSeq X)) → G (F x) ≡ x
  F→G→F (incl x) = refl
  F→G→F (push x i) = refl

  G→F→G : (x : SeqColim X) → F (G x) ≡ x
  G→F→G (incl {n = zero} x) = sym (push {n = zero} x)
  G→F→G (incl {n = suc n} x) = refl
  G→F→G (push {n = zero} x i) j = push {n = zero} x (i ∨ ~ j)
  G→F→G (push {n = suc n} x i) = refl

ShiftSequence+ : (S : Sequence ℓ) (n : ℕ) → Sequence ℓ
Sequence.obj (ShiftSequence+ S n) m = Sequence.obj S (m + n)
Sequence.map (ShiftSequence+ S n) {n = m} = Sequence.map S

ShiftSequence+Rec : (S : Sequence ℓ) (n : ℕ) → Sequence ℓ
ShiftSequence+Rec S zero = S
ShiftSequence+Rec S (suc n) = ShiftSeq (ShiftSequence+Rec S n)

Iso-SeqColim→SeqColimShift : (S : Sequence ℓ) (n : ℕ)
  → Iso (SeqColim S) (SeqColim (ShiftSequence+Rec S n))
Iso-SeqColim→SeqColimShift S zero = idIso
Iso-SeqColim→SeqColimShift S (suc n) =
  compIso (Iso-SeqColim→SeqColimShift S n)
          (Iso-SeqColim→SeqColimSuc _)

ShiftSequenceIso : {A : Sequence ℓ} (n : ℕ)
  → SequenceIso (ShiftSequence+Rec A n) (ShiftSequence+ A n)
fst (ShiftSequenceIso {A = A} zero) m =
  pathToIso λ i → Sequence.obj A (+-comm zero m i)
fst (ShiftSequenceIso {A = A} (suc n)) m =
  compIso (fst (ShiftSequenceIso {A = A} n) (suc m))
          (pathToIso λ i → Sequence.obj A (+-suc m n (~ i)))
snd (ShiftSequenceIso {A = A} zero) m a =
  sym (substCommSlice (Sequence.obj A) (Sequence.obj A ∘ suc)
                        (λ _ → Sequence.map A)
                        (+-comm zero m) a)
  ∙ λ t → subst (Sequence.obj A)
             (lUnit (cong suc (+-comm zero m)) t)
             (Sequence.map A a)
snd (ShiftSequenceIso {A = A} (suc n)) m a =
    sym (substCommSlice (Sequence.obj A) (Sequence.obj A ∘ suc)
                        (λ _ → Sequence.map A)
                        (λ i → (+-suc m n (~ i)))
                        (Iso.fun (fst (ShiftSequenceIso n) (suc m)) a))
  ∙ cong (subst (λ x → Sequence.obj A (suc x)) (sym (+-suc m n)))
         (snd (ShiftSequenceIso {A = A} n) (suc m) a)

SeqColimIso : (S : Sequence ℓ) (n : ℕ)
  → Iso (SeqColim S) (SeqColim (ShiftSequence+ S n))
SeqColimIso S n =
  compIso (Iso-SeqColim→SeqColimShift S n)
    (sequenceEquiv→ColimIso
      (SequenceIso→SequenceEquiv (ShiftSequenceIso n)))
