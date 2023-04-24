{-

The goal of this file is to prove the iso π₄S³≅ℤ/β
where β is a natural number (aka "the Brunerie number",
defined below).

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Homotopy.Group.Pi4S3.BrunerieNumber where

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.Group.Pi3S2
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Homotopy.BlakersMassey
open import Cubical.Homotopy.Whitehead
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso2
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Int
  renaming (ℤ to Z ; _·_ to _·Z_ ; _+_ to _+Z_)

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim ; map to pMap)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.GroupPath

open Iso
open Exact4

-- The Brunerie number (see Corollary 3.4.5 in Brunerie's PhD thesis)
Brunerie : ℕ
Brunerie =
  abs (HopfInvariant-π' 0  [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π')

-- First we need to define the following maps.
W : S₊ 3 → (S₊∙ 2 ⋁ S₊∙ 2)
W = joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1} ∘ Iso.inv (IsoSphereJoin 1 1)

fold∘W : S₊ 3 → S₊ 2
fold∘W = fold⋁ ∘ W

{-
We will now instantiate Blakers Massey to get a square:

         fold∘W
 S³ --------------> S²
 |\              ↗ |
 |  \         ↗    |
 |    \    ↗       |
 |      X           |  inr
 |    /             |
 |   /              |
 |  /               |
 v /                v
 1 -----------> coFib fold∘W
         inl

where X is the pullback of inl and inr and the map S³ → X is
surjective on π₃. This will give us a sequence
π₃ S³ --ᶠ→ π₃ S² → π₃ (coFib fold∘W) → π₂ X ≅ 0, where f is
the function induced by fold∘W. From this, we can deduce that
π₃ (coFib fold∘W) ≅ ℤ/ f(1) where f(1) is interpreted as an
integer via the isos π₃ S³ ≅ π₃ S² ≅ ℤ

(Recall that π₃(coFib fold∘W) ≅ π₄S³)

For clarity:
X, above will have two names (via a trivial iso) below:

TotalPushoutPath× (the version the falls out of BM)
P = fiber inr (Same name as in Brunerie's prop 4.3.4.)
-}


-- Before instantiating, we need to show that
-- any map S³ → S² is 0-connected
isConnectedS3→S2 : (f : S₊ 3 → S₊ 2) → isConnectedFun 2 f
isConnectedS3→S2 f p =
  trRec (isProp→isOfHLevelSuc 1 isPropIsContr)
    (J (λ p _ → isConnected 2 (fiber f p))
      (∣ north , refl ∣
     , (trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
         (uncurry
           (sphereElim 2
             (λ _ → isOfHLevelΠ 3
               λ _ → isOfHLevelPath 3
                 (isOfHLevelSuc 2 (isOfHLevelTrunc 2)) _ _)
           λ p → trRec (isOfHLevelTrunc 2 _ _)
             (λ r → cong ∣_∣ₕ (ΣPathP (refl , r)))
            (fun (PathIdTruncIso 1)
              (isContr→isProp
                (isConnectedPath 2 (sphereConnected 2)
                  (f north) (f north)) ∣ refl ∣ ∣ p ∣)))))))
    (fun (PathIdTruncIso 2)
      (isContr→isProp (sphereConnected 2) ∣ f north ∣ ∣ p ∣))

-- We get our square
module BM-inst =
  BlakersMassey□
   (λ _ → tt) fold∘W 3 1
   (λ _ → subst (isConnected 4)
            (isoToPath (invIso fiberUnitIso))
            (sphereConnected 3))
   (isConnectedS3→S2 fold∘W)

open BM-inst

-- The central types
coFib-fold∘W : Type
coFib-fold∘W = Pushout (λ _ → tt) fold∘W

coFib-fold∘W∙ : Pointed₀
coFib-fold∘W∙ = coFib-fold∘W , inl tt

TotalPushoutPath×∙ : Pointed ℓ-zero
fst TotalPushoutPath×∙ = Σ (Unit × S₊ 2) PushoutPath×
snd TotalPushoutPath×∙ = (tt , north) , push north

S³→TotalPushoutPath× : S₊ 3 → Σ (Unit × S₊ 2) PushoutPath×
S³→TotalPushoutPath× = toPullback

private
  inr' : S₊ 2 → coFib-fold∘W
  inr' = inr

  inr∙ : S₊∙ 2 →∙ coFib-fold∘W∙
  fst inr∙ = inr'
  snd inr∙ = sym (push north)

  fiberinr'Iso' : Iso (fiber inr' (inl tt))
                      (Σ (Unit × S₊ 2) PushoutPath×)
  fiberinr'Iso' =
    compIso (Σ-cong-iso-snd (λ x → symIso))
            (Σ-cong-iso-fst (invIso lUnit×Iso))

  fiberinr'Iso : Iso (fiber inr' (inl tt))
                     (Σ (Unit × S₊ 2) PushoutPath×)
  fun fiberinr'Iso (x , p) = (tt , x) , (sym p)
  inv fiberinr'Iso ((tt , x) , p) = x , (sym p)
  rightInv fiberinr'Iso _ = refl
  leftInv fiberinr'Iso _ = refl

  P : Pointed₀
  P = (fiber inr' (inl tt) , north , (sym (push north)))

π'P→π'TotalPath× : (n : ℕ)
  → GroupEquiv (π'Gr n TotalPushoutPath×∙) (π'Gr n P)
fst (fst (π'P→π'TotalPath× n)) =
  π'eqFun n ((invEquiv (isoToEquiv fiberinr'Iso)) , refl)
snd (fst (π'P→π'TotalPath× n)) = π'eqFunIsEquiv n _
snd (π'P→π'TotalPath× n) = π'eqFunIsHom n _

-- Time to invoke the long exact sequence of homotopy groups on
-- inr : S² → coFib-fold∘W
module LESinst = πLES {A = S₊∙ 2} {B = coFib-fold∘W∙} inr∙

-- We instantiate the sequence
-- π₃ P → π₃ S² → π₃ coFib-fold∘W∙ → π₂ P
P→S²→Pushout :
  Exact4 (πGr 2 P) (πGr 2 (S₊∙ 2)) (πGr 2 coFib-fold∘W∙) (πGr 1 P)
        (LESinst.fib→A 2)
        (LESinst.A→B 2)
        (LESinst.B→fib 1)
Exact4.ImG→H⊂KerH→L P→S²→Pushout = LESinst.Im-fib→A⊂Ker-A→B 2
Exact4.KerH→L⊂ImG→H P→S²→Pushout = LESinst.Ker-A→B⊂Im-fib→A 2
Exact4.ImH→L⊂KerL→R P→S²→Pushout = LESinst.Im-A→B⊂Ker-B→fib 1
Exact4.KerL→R⊂ImH→L P→S²→Pushout = LESinst.Ker-B→fib⊂Im-A→B 1

-- The goal now is to rewrite it as
-- π₃ S³ → π₃ S² → π₃ coFib-fold∘W∙ → Unit using the
-- "functions from spheres"-definition of πₙ.
-- Here, the first map is the one induced by fold∘W. We do this by:
-- (1) showing that π₂ P is trivial
-- (2) extending the sequence by appending surjections
-- π₃ S³ → π₃ TotalPushoutPath×∙ → π₃ P on the left.
-- (3) proving that this new composition is indeed the appropriate map

-- Step 1: π₂ P is trivial
π₂P≅0 : GroupEquiv (πGr 1 P) UnitGroup₀
π₂P≅0 = compGroupEquiv (πIso (isoToEquiv fiberinr'Iso , refl) 1)
         (GroupIso→GroupEquiv
           (contrGroupIsoUnit
             (isOfHLevelRetractFromIso 0 (invIso iso₂) isContrπ₂S³)))
  where
  iso₁ : Iso (hLevelTrunc 4 (S₊ 3))
             (hLevelTrunc 4 (Σ (Unit × S₊ 2) PushoutPath×))
  iso₁ = connectedTruncIso 4 S³→TotalPushoutPath× isConnected-toPullback

  iso₂ : Iso (π 2 (hLevelTrunc∙ 4 (S₊∙ 3)))
              (π 2 TotalPushoutPath×∙)
  iso₂ =
    (compIso (setTruncIso
      (equivToIso (_ ,
        (isEquivΩ^→ 2 (fun iso₁ , refl) (isoToIsEquiv iso₁)))))
     (invIso (πTruncIso 2)))

  isContrπ₂S³ : isContr (π 2 (hLevelTrunc∙ 4 (S₊∙ 3)))
  isContrπ₂S³ =
    subst (λ x → isContr (π 2 x))
      (λ i → ((sym (isContr→≡Unit (sphereConnected 3))) i)
            , transp (λ j → isContr→≡Unit
              (sphereConnected 3) (~ i ∧ j)) i ∣ north ∣)
      (∣ refl ∣₂ , sElim (λ _ → isSetPathImplicit)
                  λ p → cong ∣_∣₂
                          (isProp→isSet
                           (isOfHLevelPath 1 isPropUnit _ _) _ _ _ p))

-- Step 2. We transform our original sequence to one for the
-- the "maps from spheres" definition of πₙ and where π₂ P is
-- replaced by the trivial group:
-- π₃ P → π₃ S² → π₃ coFib-fold∘W∙ → 0
P→S²→Pushout→P' :
  Exact4 (π'Gr 2 P) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGroup₀
         (π'∘∙Hom 2 (fst , refl))
         (π'∘∙Hom 2 inr∙)
         (→UnitHom _)
P→S²→Pushout→P' =
  transportExact4
  (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 P)))))
  (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 (S₊∙ 2))))))
  (sym (GroupPath _ _ .fst ((GroupIso→GroupEquiv (π'Gr≅πGr 2 coFib-fold∘W∙)))))
  (sym (GroupPath _ _ .fst π₂P≅0))
  _ _ _ _ _
  P→S²→Pushout
  (ΣPathPProp (λ _ → isPropIsGroupHom _ _)
    λ i → fst (π∘∙fib→A-PathP 2 inr∙ i))
  (ΣPathPProp (λ _ → isPropIsGroupHom _ _)
    λ i → fst (π∘∙A→B-PathP 2 inr∙ i))

-- The two surjections in question
π₃S³→π₃P : GroupHom (π'Gr 2 (S₊∙ 3)) (π'Gr 2 TotalPushoutPath×∙)
π₃S³→π₃P = π'∘∙Hom 2 (S³→TotalPushoutPath× , refl)

TotalPushoutPath×∙→P : TotalPushoutPath×∙ →∙ P -- Surjective, and in particular on π₃
fst TotalPushoutPath×∙→P x = (snd (fst x)) , (sym (snd x))
snd TotalPushoutPath×∙→P = refl

-- This surjectivity is where Blakers-Massey is used
-- In particular, it uses isConnected-toPullback
isSurjective-π₃S³→π₃TotalPushoutPath× : isSurjective π₃S³→π₃P
isSurjective-π₃S³→π₃TotalPushoutPath× =
  transport (λ i → isSurjective (transportLem i))
              isSurjective-π₃S³→π₃TotalPushoutPath×'
  where
  π₃S³→π₃TotalPushoutPath× : GroupHom (πGr 2 (S₊∙ 3)) (πGr 2 TotalPushoutPath×∙)
  π₃S³→π₃TotalPushoutPath× = πHom 2 (S³→TotalPushoutPath× , refl)

  isSurjective-π₃S³→π₃TotalPushoutPath×' : isSurjective π₃S³→π₃TotalPushoutPath×
  isSurjective-π₃S³→π₃TotalPushoutPath×' =
    sElim (λ _ → isProp→isSet squash₁)
      λ p → trRec squash₁
        (λ s → ∣ ∣ fst s ∣₂ , (cong ∣_∣₂ (snd s)) ∣₁)
        (((isConnectedΩ^→ 3 3 (S³→TotalPushoutPath× , refl)
          isConnected-toPullback) p) .fst)

  transportLem : PathP (λ i → GroupHomπ≅π'PathP (S₊∙ 3) TotalPushoutPath×∙ 2 i)
                       π₃S³→π₃TotalPushoutPath× π₃S³→π₃P
  transportLem =
    toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
       (π'∘∙Hom'≡π'∘∙fun {A = S₊∙ 3} {B = TotalPushoutPath×∙}
         2 (S³→TotalPushoutPath× , refl)))

-- We get a sequence on the right form π₃S³ → π₃S² → π₃ Pushout → Unit
S³→S²→Pushout→Unit'' :
  Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGroup₀
        (compGroupHom π₃S³→π₃P
          (compGroupHom
            (π'∘∙Hom 2 TotalPushoutPath×∙→P) (π'∘∙Hom 2 (fst , refl))))
        (π'∘∙Hom 2 inr∙)
        (→UnitHom (π'Gr 2 coFib-fold∘W∙))
S³→S²→Pushout→Unit'' =
  extendExact4Surjective _ _ _ _ _ _ _ _ _
    isSurjective-π₃S³→π₃TotalPushoutPath×
    (extendExact4Surjective _ _ _ _ _ _ _ _ _
      ((sElim (λ _ → isProp→isSet squash₁)
      (λ f → ∣ ∣ (λ x → (tt , fst f x .fst) , sym (fst f x .snd))
      , ΣPathP ((ΣPathP (refl , cong fst (snd f)))
                       , λ j i → snd f j  .snd (~ i)) ∣₂
              , cong ∣_∣₂ (ΣPathP (refl , sym (rUnit _))) ∣₁)))
      P→S²→Pushout→P')

-- Step 3: We need to show that the map π₃S³ → π₃S² in the above sequence
-- indeed comes from fold∘W
tripleComp≡ :
    (compGroupHom π₃S³→π₃P
     (compGroupHom
      (π'∘∙Hom 2 TotalPushoutPath×∙→P) (π'∘∙Hom 2 (fst , refl))))
  ≡ π'∘∙Hom 2 (fold∘W , refl)
tripleComp≡ =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt (sElim (λ _ → isSetPathImplicit)
     λ f → cong ∣_∣₂ (ΣPathP (refl , (cong (_∙ refl)
     (λ j → cong fst (rUnit (cong (fst TotalPushoutPath×∙→P)
               (rUnit (cong S³→TotalPushoutPath× (snd f)) (~ j))) (~ j))))))))

-- We finally get the correct sequence
S³→S²→Pushout→Unit :
  Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGroup₀
        (π'∘∙Hom 2 (fold∘W , refl))
        (π'∘∙Hom 2 inr∙)
        (→UnitHom (π'Gr 2 coFib-fold∘W∙))
S³→S²→Pushout→Unit =
  subst
   (λ F → Exact4 (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙) UnitGroup₀
            F (π'∘∙Hom 2 inr∙)
            (→UnitHom (π'Gr 2 coFib-fold∘W∙)))
            tripleComp≡
   S³→S²→Pushout→Unit''

-- We need to throw around some pushouts
module _ where
  Pushout-coFibW-fold⋁≃coFib-fold∘W :
    Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁ ≃ fst coFib-fold∘W∙
  Pushout-coFibW-fold⋁≃coFib-fold∘W = compEquiv
          (compEquiv pushoutSwitchEquiv
            (isoToEquiv (PushoutDistr.PushoutDistrIso fold⋁ W λ _ → tt)))
          pushoutSwitchEquiv

  coFibW≅coFibW' : Pushout W (λ _ → tt) ≃ cofibW S¹ S¹ base base
  coFibW≅coFibW' = pushoutEquiv W (λ _ → tt) joinTo⋁ (λ _ → tt)
           (isoToEquiv (invIso (IsoSphereJoin 1 1)))
           (idEquiv _)
           (idEquiv _)
           refl
           refl

  Pushout-coFibW-fold⋁≃Pushout⋁↪fold⋁ :
      Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁
    ≃ fst (Pushout⋁↪fold⋁∙ (S₊∙ 2))
  Pushout-coFibW-fold⋁≃Pushout⋁↪fold⋁ = pushoutEquiv inl _ ⋁↪ fold⋁
          (idEquiv _)
          (compEquiv coFibW≅coFibW'
            (isoToEquiv (invIso (Iso-Susp×Susp-cofibJoinTo⋁ S¹ S¹ base base))))
          (idEquiv _)
          (Susp×Susp→cofibW≡ S¹ S¹ base base)
          refl

  Pushout-coFibW-fold⋁≃Pushout⋁↪fold⋁∙ :
       (Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁ , inr north)
    ≃∙ (Pushout⋁↪fold⋁∙ (S₊∙ 2))
  fst Pushout-coFibW-fold⋁≃Pushout⋁↪fold⋁∙ =
    Pushout-coFibW-fold⋁≃Pushout⋁↪fold⋁
  snd Pushout-coFibW-fold⋁≃Pushout⋁↪fold⋁∙ =
    sym (push (inl north))

π₄S³≅π₃coFib-fold∘W∙ : GroupEquiv (π'Gr 3 (S₊∙ 3)) (π'Gr 2 coFib-fold∘W∙)
π₄S³≅π₃coFib-fold∘W∙ =
  compGroupEquiv
    (GroupIso→GroupEquiv
      (compGroupIso
        (π'Gr≅πGr 3 (S₊∙ 3))
        (compGroupIso
          π₄S³≅π₃PushS²
          (invGroupIso (π'Gr≅πGr 2 (Pushout⋁↪fold⋁∙ (S₊∙ 2)))))))
    (compGroupEquiv
      (invGroupEquiv (π'Iso 2 Pushout-coFibW-fold⋁≃Pushout⋁↪fold⋁∙))
      (π'Iso 2 (Pushout-coFibW-fold⋁≃coFib-fold∘W , sym (push north))))

-- We get the iso
-- For type checking reasons, let's first prove it for the abstract
-- definition of ℤ/_

-- To get everything on the same form as in Brunerie's thesis, we
-- first need the following:
fold∘W≡Whitehead :
        fst (π'∘∙Hom 2 (fold∘W , refl)) ∣ idfun∙ (S₊∙ 3) ∣₂
      ≡ ∣ [ idfun∙ (S₊∙ 2) ∣ idfun∙ (S₊∙ 2) ]₂ ∣₂
fold∘W≡Whitehead =
  pRec (squash₂ _ _)
    (cong ∣_∣₂)
    (indΠ₃S₂ _ _
      (funExt (λ x → funExt⁻ (sym (cong fst (id∨→∙id {A = S₊∙ 2}))) (W x))))
  where
  indΠ₃S₂ : ∀ {ℓ} {A : Pointed ℓ}
    → (f g : A →∙ S₊∙ 2)
      → fst f ≡ fst g → ∥ f ≡ g ∥₁
  indΠ₃S₂ {A = A} f g p =
    trRec squash₁
     (λ r → ∣ ΣPathP (p , r) ∣₁)
      (isConnectedPathP 1 {A = (λ i → p i (snd A) ≡ north)}
        (isConnectedPathSⁿ 1 (fst g (pt A)) north) (snd f) (snd g) .fst )

BrunerieIsoAbstract : GroupEquiv (π'Gr 3 (S₊∙ 3)) (abstractℤGroup/ Brunerie)
BrunerieIsoAbstract =
  compGroupEquiv π₄S³≅π₃coFib-fold∘W∙
    (invGroupEquiv
      (GroupEquiv-abstractℤ/abs-gen
        (π'Gr 2 (S₊∙ 3)) (π'Gr 2 (S₊∙ 2)) (π'Gr 2 coFib-fold∘W∙)
          (GroupIso→GroupEquiv (invGroupIso (πₙ'Sⁿ≅ℤ 2)))
          (invGroupEquiv hopfInvariantEquiv)
          (π'∘∙Hom 2 (fold∘W , refl))
          _
          S³→S²→Pushout→Unit Brunerie main))
  where
  mainPath :
    fst (π'∘∙Hom 2 (fold∘W , refl))
         (Iso.inv (fst (πₙ'Sⁿ≅ℤ 2)) 1)
     ≡ [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π'
  mainPath =
      cong (fst (π'∘∙Hom 2 (fold∘W , refl)))
           (cong (Iso.inv (fst (πₙ'Sⁿ≅ℤ 2))) (sym (πₙ'Sⁿ≅ℤ-idfun∙ 2))
           ∙ (Iso.leftInv (fst (πₙ'Sⁿ≅ℤ 2)) ∣ idfun∙ (S₊∙ 3) ∣₂))
    ∙ fold∘W≡Whitehead
    ∙ cong ∣_∣₂ (sym ([]≡[]₂ (idfun∙ (S₊∙ 2)) (idfun∙ (S₊∙ 2))))

  main : _ ≡ Brunerie
  main i = abs (HopfInvariant-π' 0 (mainPath i))

-- And, finally, we get the actual iso
-- (as in Corollary 3.4.5 in Brunerie's thesis)
BrunerieIso : GroupEquiv (π'Gr 3 (S₊∙ 3)) (ℤGroup/ Brunerie)
BrunerieIso =
  compGroupEquiv BrunerieIsoAbstract (abstractℤ/≅ℤ Brunerie)
