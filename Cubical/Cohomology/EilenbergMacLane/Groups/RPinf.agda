{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.RPinf where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Gysin

open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Fin.Base

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup.Instances.IntMod

open RingStr renaming (_+_ to _+r_)
open PlusBis

open Iso

-- move to Cohomology GroupStr or somethign
EM-ℤ/2ˣ∙ : (n : ℕ) → EM ℤ/2 ˣ n
EM-ℤ/2ˣ∙ = 0ˣ (EM ℤ/2) 0ₖ

private
  nonConst→∙ : (b : EM ℤ/2 1) → Type _
  nonConst→∙ b =
    Σ[ F ∈ Susp∙ (embase ≡ b) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1 ]
      (¬ F ≡ const∙ _ _)

  Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool :
    Iso (Susp∙ (Ω (EM∙ ℤ/2 1) .fst)
         →∙ EM∙ ℤ/2 1)
        ((Bool , true) →∙ (Bool , true))
  Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool = compIso
    (invIso (ΩSuspAdjointIso {A = Ω (EM∙ ℤ/2 1)}))
    (compIso (post∘∙equiv (lem , refl)) (pre∘∙equiv (lem , refl)))
    where
    lem = isoToEquiv
      (compIso (invIso (Iso-EM-ΩEM+1 {G = ℤ/2} 0))
               (invIso (Bool≅ℤGroup/2 .fst)))

  Σ¬Iso : ∀ {ℓ} {B A : Type ℓ}
    → (e : A ≃ B)
    → {x : A}
    → Iso (Σ[ y ∈ A ] ¬ y ≡ x)
           (Σ[ y ∈ B ] ¬ y ≡ fst e x)
  Σ¬Iso {B = B} =
    EquivJ (λ A e → {x : A}
    → Iso (Σ[ y ∈ A ] ¬ y ≡ x)
           (Σ[ y ∈ B ] ¬ y ≡ fst e x)) idIso

  nonConst→∙Iso : Iso (nonConst→∙ embase) (Σ[ F ∈ Bool ] ¬ F ≡ true)
  nonConst→∙Iso =
    Σ¬Iso (isoToEquiv
           (compIso Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool
                    Iso-Bool→∙Bool-Bool))

  isProp-nonConst→∙ : (b : EM ℤ/2 1) → isProp (nonConst→∙ b)
  isProp-nonConst→∙ = EM→Prop _ 0 (λ _ → isPropIsProp)
           (isOfHLevelRetractFromIso 1 nonConst→∙Iso
             (isContr→isProp ((false , true≢false ∘ sym)
                         , λ { (false , p) → Σ≡Prop (λ _ → isProp¬ _) refl
                             ; (true , p) → ⊥.rec (p refl)})))

eRP∞∙ : Susp∙ (Ω (EM∙ ℤ/2 1) .fst) →∙ EM∙ ℤ/2 1
fst eRP∞∙ north = embase
fst eRP∞∙ south = embase
fst eRP∞∙ (merid a i) = a i
snd eRP∞∙ = refl

eRP∞-nonConst : nonConst→∙ embase
fst eRP∞-nonConst = eRP∞∙
snd eRP∞-nonConst p = true≢false true≡false
  where
  true≡false : true ≡ false
  true≡false i =
    Iso.fun (compIso Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool Iso-Bool→∙Bool-Bool)
      (p (~ i))

eRP∞ : (b : EM ℤ/2 1) → nonConst→∙ b
eRP∞ = EM→Prop ℤ/2 0 isProp-nonConst→∙ eRP∞-nonConst

module ThomRP∞ = Thom (EM∙ ℤ/2 1) (0ₖ 1 ≡_) refl
                      (isConnectedEM 1)
                      ℤ/2CommRing

open ThomRP∞
isContrE : isContr E
isContrE = isContrSingl _

module conRP∞ =
  con 0 (((compEquiv (isoToEquiv (invIso (Iso-EM-ΩEM+1 0)))
                   (isoToEquiv (invIso (fst Bool≅ℤGroup/2))))) , refl)
        (λ b → eRP∞ b .fst)
        (Iso.inv (congIso (compIso Iso-SuspΩEM₁→∙EM₁-Bool→∙Bool
                                   Iso-Bool→∙Bool-Bool)) λ i → false)

open conRP∞
ϕ-raw-contrRP∞ : (n : ℕ)
  → ((EM ℤ/2 1 → EM ℤ/2 n))
   ≃ (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (n +' 1))
ϕ-raw-contrRP∞ n = ϕ-raw-contr n isContrE

⌣RP∞ : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
  → EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (n +' 1)
fst (⌣RP∞ n f) x = (f x) ⌣[ ℤ/2Ring R]ₖ x
snd (⌣RP∞ n f) = ⌣ₖ-0ₖ _ _ (f (0ₖ 1))

⌣RP∞' : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
  → EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (1 +' n)
fst (⌣RP∞' n f) x = x ⌣[ ℤ/2Ring R]ₖ (f x)
snd (⌣RP∞' n f) = 0ₖ-⌣ₖ _ _ (f (0ₖ 1))

⌣RP∞≡⌣RP∞' : (n : ℕ) →
  PathP (λ i →
   (EM ℤ/2 1 → EM ℤ/2 n) →
    EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (+'-comm n 1 i))
  (⌣RP∞ n)
  (⌣RP∞' n)
⌣RP∞≡⌣RP∞' n = funExt λ f →
  →∙HomogeneousPathP refl (cong (EM∙ ℤ/2) (+'-comm n 1))
    (isHomogeneousEM _)
    (funExt λ x → lem f x)
  where
  lem : (f : EM ℤ/2 1 → EM ℤ/2 n)
        (x : EM ℤ/2 1)
    → PathP (λ i → EM ℤ/2 (+'-comm n 1 i))
             (f x ⌣[ ℤ/2Ring R]ₖ x) (x ⌣[ ℤ/2Ring R]ₖ f x)
  lem f x = toPathP (sym (⌣ₖ-commℤ/2 1 n x (f x)))

⌣RP∞IsEq : (n : ℕ) → isEquiv (⌣RP∞ n)
⌣RP∞IsEq n =
  subst isEquiv
    (funExt (λ f → →∙Homogeneous≡ (isHomogeneousEM _)
      (λ i x → f x ⌣[ ℤ/2Ring R]ₖ (eRP∞-lem x i))))
      (ϕ-raw-contrRP∞ n .snd)
  where
  help : (g : _) → (λ i → eRP∞ (emloop g i) .fst .fst south)
                  ≡ emloop g
  help g j i =
    hcomp (λ k → λ {(i = i0) → embase
                   ; (i = i1) → emloop g k
                   ; (j = i0) → eRP∞ (emloop g i) .fst .fst
                                  (merid (λ w → emloop g (i ∧ w)) k)
                   ; (j = i1) → emloop g (i ∧ k)})
          (eRP∞ (emloop g i) .fst .snd j)

  eRP∞-lem : (x : _) → eRP∞ x .fst .fst south ≡ x
  eRP∞-lem = EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
    λ { embase-raw → refl ; (emloop-raw g i) j → help g j i }

abstract
  ⌣RP∞'IsEq : (n : ℕ) → isEquiv (⌣RP∞' n)
  ⌣RP∞'IsEq n = transport (λ i → isEquiv (⌣RP∞≡⌣RP∞' n i)) (⌣RP∞IsEq n)

⌣RP∞Equiv : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
   ≃ (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (n +' 1))
fst (⌣RP∞Equiv n) = ⌣RP∞ n
snd (⌣RP∞Equiv n) = ⌣RP∞IsEq n

⌣RP∞'Equiv : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
   ≃ (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (1 +' n))
fst (⌣RP∞'Equiv n) = ⌣RP∞' n
snd (⌣RP∞'Equiv n) = ⌣RP∞'IsEq n

+'-suc₁ : (n : ℕ) → 1 +' n ≡ suc n
+'-suc₁ zero = refl
+'-suc₁ (suc n) = refl

⌣RP∞''Equiv : (n : ℕ)
  → (EM ℤ/2 1 → EM ℤ/2 n)
   ≃ (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (suc n))
⌣RP∞''Equiv n =
  compEquiv (⌣RP∞'Equiv n)
    (isoToEquiv (pre∘∙equiv
      ((pathToEquiv (cong (EM ℤ/2) (+'-suc₁ n)))
      , (subst-EM-0ₖ (+'-suc₁ n)))))

RP→Charac₀ : Iso (EM ℤ/2 1 → ℤ/2 .fst)
                  (ℤ/2 .fst)
Iso.fun RP→Charac₀ f = f embase
Iso.inv RP→Charac₀ a = λ _ → a
Iso.rightInv RP→Charac₀ a = refl
Iso.leftInv RP→Charac₀ f =
  funExt (EM→Prop _ 0 (λ _ → is-set (snd ℤ/2Ring) _ _) refl)

RP→EM-ℤ/2-CharacIso : (n : ℕ)
  → Iso (EM ℤ/2 1 → EM ℤ/2 n)
         ((EM ℤ/2) ˣ n)
RP→EM-ℤ/2-CharacIso zero = RP→Charac₀ -- RP→Charac₀
RP→EM-ℤ/2-CharacIso (suc n) =
  compIso (EM→-charac {A = EM∙ ℤ/2 1} (suc n))
          (prodIso
            (compIso help (RP→EM-ℤ/2-CharacIso n))
            idIso)
  where
  help : Iso (EM∙ ℤ/2 1 →∙ EM∙ ℤ/2 (suc n))
             (EM ℤ/2 1 → EM ℤ/2 n)
  help = equivToIso (invEquiv (⌣RP∞''Equiv n))

∥EM-ℤ/2ˣ∥₀-Iso : (n : ℕ) → Iso ∥ EM ℤ/2 ˣ n ∥₂ (fst ℤ/2)
∥EM-ℤ/2ˣ∥₀-Iso zero = setTruncIdempotentIso (is-set (snd ℤ/2Ring))
∥EM-ℤ/2ˣ∥₀-Iso (suc n) =
  compIso
    (compIso
      setTruncOfProdIso
      (compIso (Σ-cong-iso-snd λ _
        → equivToIso
            (isContr→≃Unit (∣ 0ₖ (suc n) ∣₂
              , ST.elim (λ _ → isSetPathImplicit)
                (EM→Prop _ _ (λ _ → squash₂ _ _) refl))))
        rUnit×Iso))
    (∥EM-ℤ/2ˣ∥₀-Iso n)

⌣RP∞''Equiv∙ : (n : ℕ)
  → ⌣RP∞''Equiv n .fst (λ _ → 0ₖ n) ≡ const∙ _ _
⌣RP∞''Equiv∙ n = →∙Homogeneous≡ (isHomogeneousEM _)
  (funExt λ x → cong (subst (EM ℤ/2) (+'-suc₁ n)) (⌣ₖ-0ₖ 1 n x)
              ∙ subst-EM∙ (+'-suc₁ n) .snd)

cohomRP∞Iso : (n : ℕ) → Iso (coHom n ℤ/2 (EM ℤ/2 1)) (ℤ/2 .fst)
cohomRP∞Iso n = compIso (setTruncIso (RP→EM-ℤ/2-CharacIso n)) (∥EM-ℤ/2ˣ∥₀-Iso n)

RP→EM-ℤ/2-CharacIso∙ : (n : ℕ)
  → Iso.fun (RP→EM-ℤ/2-CharacIso n) (λ _ → 0ₖ n) ≡ EM-ℤ/2ˣ∙ n
RP→EM-ℤ/2-CharacIso∙ zero = refl
RP→EM-ℤ/2-CharacIso∙ (suc n) =
  ΣPathP (((cong (fun (RP→EM-ℤ/2-CharacIso n))
   (funExt λ x
  → cong (λ f → invEq (⌣RP∞''Equiv n) f x)
            (→∙Homogeneous≡ (isHomogeneousEM _)
              (funExt (λ x → rCancelₖ (suc n) (0ₖ (suc n)))))
   ∙ funExt⁻ (sym (cong (invEq (⌣RP∞''Equiv n)) (⌣RP∞''Equiv∙ n))) x
   ∙ λ i → retEq (⌣RP∞''Equiv n) (λ _ → 0ₖ n) i x))
   ∙ RP→EM-ℤ/2-CharacIso∙ n)
   , refl)

HⁿRP∞≅ℤ/2 : (n : ℕ) → AbGroupIso (coHomGr n ℤ/2 (EM ℤ/2 1)) ℤ/2
fst (HⁿRP∞≅ℤ/2 n) = cohomRP∞Iso n
snd (HⁿRP∞≅ℤ/2 n) = pres0→GroupIsoℤ/2 (isoToEquiv (cohomRP∞Iso n)) (cohomRP∞Iso∙ n)
  where
  ∥EM-ℤ/2ˣ∥₀-Iso∙ : (n : ℕ) → Iso.fun (∥EM-ℤ/2ˣ∥₀-Iso n) ∣ EM-ℤ/2ˣ∙ n ∣₂ ≡ fzero
  ∥EM-ℤ/2ˣ∥₀-Iso∙ zero = refl
  ∥EM-ℤ/2ˣ∥₀-Iso∙ (suc n) = ∥EM-ℤ/2ˣ∥₀-Iso∙ n

  cohomRP∞Iso∙ : (n : ℕ) → cohomRP∞Iso n .fun (0ₕ n) ≡ fzero
  cohomRP∞Iso∙ n = cong (Iso.fun (∥EM-ℤ/2ˣ∥₀-Iso n) ∘ ∣_∣₂) (RP→EM-ℤ/2-CharacIso∙ n)
                 ∙ ∥EM-ℤ/2ˣ∥₀-Iso∙ n
