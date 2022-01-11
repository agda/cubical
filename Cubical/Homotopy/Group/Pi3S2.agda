{-# OPTIONS --safe --experimental-lossy-unification #-}
{-
This file contains:
1. The long exact sequence of loop spaces Ωⁿ (fib f) → Ωⁿ A → Ωⁿ B
2. The long exact sequence of homotopy groups πₙ(fib f) → πₙ A → πₙ B
3. Some lemmas relating the map in the sequence to maps
-}
module Cubical.Homotopy.Group.Pi3S2 where

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Group.PinSn

open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 hiding (decode ; encode)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open import Cubical.Algebra.Group.ZAction


open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.Homotopy.Freudenthal hiding (Code ; encode)
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)
open import Cubical.HITs.S2

open import Cubical.Homotopy.Hopf
open import Cubical.Algebra.Group.Exact
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Algebra.Group.Instances.Unit renaming (Unit to UnitGr)

TotalHopf→∙S² : (Σ (S₊ 2) S¹Hopf , north , base) →∙ S₊∙ 2
fst TotalHopf→∙S² = fst
snd TotalHopf→∙S² = refl

IsoTotalSpaceJoin' : Iso (Σ (S₊ 2) S¹Hopf) (S₊ 3)
IsoTotalSpaceJoin' = compIso hopfS¹.IsoTotalSpaceJoin (IsoSphereJoin 1 1)

IsoFiberTotalHopfS¹ : Iso (fiber (fst TotalHopf→∙S²) north) S¹
fun IsoFiberTotalHopfS¹ ((x , y) , z) = subst S¹Hopf z y
inv IsoFiberTotalHopfS¹ x = (north , x) , refl
rightInv IsoFiberTotalHopfS¹ x = refl
leftInv IsoFiberTotalHopfS¹ ((x , y) , z) =
  ΣPathP ((ΣPathP (sym z , (λ i → transp (λ j → S¹Hopf (z (~ i ∧ j))) i y)))
         , (λ j i → z (i ∨ ~ j)))

IsoFiberTotalHopfS¹∙≡ :
  (fiber (fst TotalHopf→∙S²) north , (north , base) , refl) ≡ S₊∙ 1
IsoFiberTotalHopfS¹∙≡ = ua∙ (isoToEquiv IsoFiberTotalHopfS¹) refl

private
  transportGroupEquiv : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) (f : A →∙ B)
    → isEquiv (fst (πLES.A→B f n))
    → isEquiv (fst (π∘∙ n f))
  transportGroupEquiv n f iseq = transport (λ i → isEquiv (fst (π∘∙A→B-PathP n f i))) iseq


π₃S²≅π₃TotalHopf : GroupEquiv (πGr 2 (Σ (S₊ 2) S¹Hopf , north , base))
                              (πGr 2 (S₊∙ 2))
fst (fst π₃S²≅π₃TotalHopf) = fst (πLES.A→B TotalHopf→∙S² 2)
snd (fst π₃S²≅π₃TotalHopf) =
  SES→isEquiv
    (isContr→≡UnitGroup
      (subst isContr (cong (π 3) (sym IsoFiberTotalHopfS¹∙≡))
        (∣ refl ∣₂ , (sElim (λ _ → isSetPathImplicit)
          (λ p → cong ∣_∣₂ (isOfHLevelSuc 3 isGroupoidS¹ _ _ _ _ _ _ refl p))))))
    (isContr→≡UnitGroup
      (subst isContr (cong (π 2) (sym IsoFiberTotalHopfS¹∙≡))
        (∣ refl ∣₂ , (sElim (λ _ → isSetPathImplicit) (λ p
                    → cong ∣_∣₂ (isGroupoidS¹ _ _ _ _ refl p))))))
    (πLES.fib→A TotalHopf→∙S² 2)
    (πLES.A→B TotalHopf→∙S² 2)
    (πLES.B→fib TotalHopf→∙S² 1)
    (πLES.Ker-A→B⊂Im-fib→A TotalHopf→∙S² 2)
    (πLES.Ker-B→fib⊂Im-A→B TotalHopf→∙S² 1)
snd π₃S²≅π₃TotalHopf = snd (πLES.A→B TotalHopf→∙S² 2)

π'₃S²≅π'₃TotalHopf : GroupEquiv (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base))
                                (π'Gr 2 (S₊∙ 2))
fst (fst π'₃S²≅π'₃TotalHopf) = fst (π∘∙ 2 TotalHopf→∙S²)
snd (fst π'₃S²≅π'₃TotalHopf) =
  transportGroupEquiv 2 TotalHopf→∙S² (π₃S²≅π₃TotalHopf .fst .snd)
snd π'₃S²≅π'₃TotalHopf = snd (π∘∙ 2 TotalHopf→∙S²)

-- Move to wherever ≃∙ is.
Equiv∙J : ∀ {ℓ ℓ'} {B : Pointed ℓ} (C : (A : Pointed ℓ) → A ≃∙ B → Type ℓ')
          → C B (idEquiv (fst B) , refl)
          → {A : _} (e : A ≃∙ B) → C A e
Equiv∙J {ℓ} {ℓ'} {B = B} C ind {A = A} =
  uncurry λ e p → help e (pt A) (pt B) p C ind
  where
  help : ∀ {A : Type ℓ} (e : A ≃ typ B) (a : A) (b : typ B)
       → (p : fst e a ≡ b)
       → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
       → C (fst B , b) (idEquiv (fst B) , refl)
       → C (A , a)  (e , p)
  help = EquivJ (λ A e → (a : A) (b : typ B)
       → (p : fst e a ≡ b)
       → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
       → C (fst B , b) (idEquiv (fst B) , refl)
       → C (A , a)  (e , p))
        λ a b → J (λ b p
          → (C : (A : Pointed ℓ) → A ≃∙ (fst B , b) → Type ℓ')
                → C (fst B , b)
      (idEquiv (fst B) , refl) →
      C (typ B , a) (idEquiv (typ B) , p))
         λ _ p → p

-- This stuff should probably be in Group.Base
π'fun : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → A ≃∙ B
      → (π' (suc n) A) → π' (suc n) B
π'fun n p = sMap ((fst (fst p) , snd p) ∘∙_)

π'fun-idEquiv : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
              → π'fun n (idEquiv (fst A) , (λ _ → pt A))
              ≡ idfun _
π'fun-idEquiv n =
  funExt (sElim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (∘∙-idʳ f))

π'funIsEquiv : 
  ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → (e : A ≃∙ B)
      → isEquiv (π'fun n e)
π'funIsEquiv {B = B} n =
  Equiv∙J (λ A e → isEquiv (π'fun n e))
    (subst isEquiv (sym (π'fun-idEquiv n))
      (idIsEquiv (π' (suc n) B)))

π'funIsHom : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → (e : A ≃∙ B)
      → IsGroupHom (π'Gr n A .snd) (π'fun n e)
                      (π'Gr n B .snd)
π'funIsHom {B = B} n =
  Equiv∙J (λ A e → IsGroupHom (π'Gr n A .snd) (π'fun n e) (π'Gr n B .snd))
    (subst (λ x → IsGroupHom (π'Gr n B .snd) x (π'Gr n B .snd))
      (sym (π'fun-idEquiv n))
      (makeIsGroupHom λ _ _ → refl))

π'Iso : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} (n : ℕ)
      → A ≃∙ B
      → GroupEquiv (π'Gr n A) (π'Gr n B)
fst (fst (π'Iso n e)) = π'fun n e
snd (fst (π'Iso n e)) = π'funIsEquiv n e
snd (π'Iso n e) = π'funIsHom n e

πS³≅πTotalHopf : (n : ℕ) → GroupEquiv (π'Gr n (S₊∙ 3)) (π'Gr n (Σ (S₊ 2) S¹Hopf , north , base))
πS³≅πTotalHopf n =
  π'Iso n ((isoToEquiv (invIso (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1))))
         , refl)

πS³≅πTotalHopf-gen : fst (fst (πS³≅πTotalHopf 2)) ∣ idfun∙ _ ∣₂
                   ≡ ∣ inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl ∣₂
πS³≅πTotalHopf-gen =
  cong ∣_∣₂ (∘∙-idʳ (inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl))

πTotalHopf-gen :
  gen₁-by (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base))
    ∣ inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl ∣₂
πTotalHopf-gen = 
  subst (gen₁-by (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base)))
        πS³≅πTotalHopf-gen
        (Iso-pres-gen₁ (π'Gr 2 (S₊∙ 3))
                       (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base))
                       ∣ idfun∙ _ ∣₂
                       (πₙ'Sⁿ-gen-by-idfun 2)
                       (GroupEquiv→GroupIso (πS³≅πTotalHopf 2)))

πTotalHopf≅πS²-gen :
    fst (fst π'₃S²≅π'₃TotalHopf) ∣ inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl ∣₂
  ≡ ∣ HopfMap' , refl ∣₂
πTotalHopf≅πS²-gen =
  cong ∣_∣₂ (ΣPathP (refl , (sym (rUnit refl))))

π₂S³-gen-by-HopfMap' : gen₁-by (π'Gr 2 (S₊∙ 2)) ∣ HopfMap' , refl ∣₂
π₂S³-gen-by-HopfMap' =
  subst (gen₁-by (π'Gr 2 (S₊∙ 2)))  πTotalHopf≅πS²-gen
    (Iso-pres-gen₁ (π'Gr 2 (Σ (S₊ 2) S¹Hopf , north , base)) (π'Gr 2 (S₊∙ 2))
      ∣ inv (compIso (hopfS¹.IsoTotalSpaceJoin) (IsoSphereJoin 1 1)) , refl ∣₂
      πTotalHopf-gen
      (GroupEquiv→GroupIso π'₃S²≅π'₃TotalHopf))

π₂S³-gen-by-HopfMap : gen₁-by (π'Gr 2 (S₊∙ 2)) ∣ HopfMap ∣₂
π₂S³-gen-by-HopfMap =
  subst (gen₁-by (π'Gr 2 (S₊∙ 2)))
        (cong ∣_∣₂ (sym hopfMap≡HopfMap'))
        π₂S³-gen-by-HopfMap'
