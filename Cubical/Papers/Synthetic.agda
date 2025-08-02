module Cubical.Papers.Synthetic where

-- Cubical synthetic homotopy theory
-- Mörtberg and Pujet, „Cubical synthetic homotopy theory“.
-- https://dl.acm.org/doi/abs/10.1145/3372885.3373825

-- 2.1
import Agda.Builtin.Cubical.Path              as Path
import Cubical.Foundations.Prelude            as Prelude
-- 2.2
import Agda.Primitive.Cubical                 as PrimitiveCubical
import Cubical.Data.Bool                      as Bool
import Cubical.Core.Primitives                as CorePrimitives
-- 2.3
import Cubical.HITs.S1                        as S1
-- 2.4
import Cubical.Foundations.Equiv              as Equiv
import Cubical.Core.Glue                      as CoreGlue
import Cubical.Foundations.Univalence         as Univalence
-- 3.
import Cubical.HITs.Torus                     as T2
-- 3.1
import Cubical.Data.Int                       as Int
import Cubical.Data.Int.Properties            as IntProp
import Cubical.Foundations.Isomorphism        as Isomorphism
-- 4.1
import Cubical.HITs.Susp                      as Suspension
import Cubical.HITs.Sn                        as Sn
import Agda.Builtin.Nat                       as BNat
import Agda.Builtin.Bool                      as BBool
import Cubical.Foundations.GroupoidLaws       as GroupoidLaws
import Cubical.HITs.S2                        as S2
import Cubical.HITs.S3                        as S3
-- 4.2
import Cubical.HITs.Pushout                   as Push
import Cubical.HITs.Pushout.Properties        as PushProp
-- 4.3
import Cubical.HITs.Join                      as Join
import Cubical.HITs.Join.Properties           as JoinProp
-- 5.
import Cubical.Homotopy.Hopf                  as Hopf

--------------------------------------------------------------------------------
-- 2.  Cubical Agda
-- 2.1 The Interval and Path Types
-- 2.2 Transport and Composition
-- 2.3 Higher Inductive Types
-- 2.4 Glue Types and Univalence
--------------------------------------------------------------------------------

-- 2.1 The Interval and Path Types
open Path using (PathP) public
open Prelude using (_≡_ ; refl ; funExt) public
open Prelude renaming (sym to _⁻¹) public

-- 2.2 Transport and Composition
open Prelude using (transport ; subst ; J ; JRefl) public
open PrimitiveCubical using (Partial) public
open Bool using (Bool ; true ; false) public

partialBool : ∀ i → Partial (i ∨ ~ i) Bool
partialBool i = λ {(i = i1) → true
                 ; (i = i0) → false}

open CorePrimitives using (inS ; outS ; hcomp) public
open Prelude using (_∙_) public

-- 2.3 Higher Inductive Types
open S1 using (S¹ ; base ; loop) public

double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

-- 2.4 Glue Types and Univalence
open Equiv using (idEquiv) public
open CoreGlue using (Glue) public
open Univalence using (ua) public

--------------------------------------------------------------------------------
-- 3.  The Circle and Torus
-- 3.1 The Loop Spaces of the Circle and Torus
--------------------------------------------------------------------------------

open T2 using ( Torus ; point ; line1 ; line2 ; square
              ; t2c ; c2t ; c2t-t2c ; t2c-c2t ; Torus≡S¹×S¹)

-- 3.1 The Loop Spaces of the Circle and Torus
open S1 using (ΩS¹) public
open T2 using (ΩTorus) public
open Int using (pos ; negsuc) renaming (ℤ to Int) public
open IntProp using (sucPathℤ) public
open S1 using (helix ; winding) public

-- Examples computing the winding numbers of the circle
_ : winding (loop ∙ loop ∙ loop) ≡ pos 3
_ = refl

_ : winding ((loop ⁻¹) ∙ loop ∙ (loop ⁻¹)) ≡ negsuc 0
_ = refl

open S1 renaming (intLoop to loopn) public
open S1 renaming (windingℤLoop to winding-loopn) public
open S1 using (encode ; decode ; decodeEncode ; ΩS¹≡ℤ) public
open Isomorphism using (isoToPath ; iso) public

-- Notation of the paper, current notation under ΩS¹≡Int
ΩS¹≡Int' : ΩS¹ ≡ Int
ΩS¹≡Int' = isoToPath (iso winding loopn
                      winding-loopn (decodeEncode base))

open T2 using (ΩTorus≡ℤ×ℤ ; windingTorus) public

-- Examples at the end of section 3.
_ : windingTorus (line1 ∙ line2) ≡ (pos 1 , pos 1)
_ = refl

_ : windingTorus ((line1 ⁻¹) ∙ line2 ∙ line1) ≡ (pos 0 , pos 1)
_ = refl

--------------------------------------------------------------------------------
-- 4.  Suspension, Spheres and Pushouts
-- 4.1 Suspension
-- 4.2 Pushouts and the 3 × 3 Lemma
-- 4.3 The Join and S³
--------------------------------------------------------------------------------

-- 4.1 Suspension
open Suspension using (Susp ; north ; south ; merid) public
open Sn using (S₊) public
open Suspension using ( SuspBool→S¹ ; S¹→SuspBool
                      ; SuspBool→S¹→SuspBool
                      ; S¹→SuspBool→S¹) public

-- Deprecated version of S₊
open BNat renaming (Nat to ℕ) hiding (_*_) public
open CorePrimitives renaming (Type to Set) public
open BBool using (Bool) public
-- At the time the paper was published, Set was used instead of Type
_-sphere : ℕ → Set
0 -sphere = Bool
(suc n) -sphere = Susp (n -sphere)

-- Lemma 4.1. The (1)-sphere is equal to the circle S1.

open BBool using (true ; false) public
-- Deprecated version of SuspBool→S¹
s2c : 1 -sphere → S¹
s2c north = base
s2c south = base
s2c (merid true i) = loop i
s2c (merid false i) = base -- (loop ⁻¹) i

-- Deprecated version of S¹→SuspBool
c2s : S¹ → 1 -sphere
c2s base = north
c2s (loop i) = (merid true ∙ (merid false ⁻¹)) i

open GroupoidLaws using (rUnit) public
-- Deprecated version of SuspBool→S¹→SuspBool
s2c-c2s : ∀ (p : S¹) → s2c (c2s p) ≡ p
s2c-c2s base = refl
s2c-c2s (loop i) j = rUnit loop (~ j) i

h1 : I → I → 1 -sphere
h1 i j = merid false (i ∧ j)

h2 : I → I → 1 -sphere
h2 i j = hcomp (λ k → λ { (i = i0) → north
                        ; (i = i1) → merid false (j ∨ ~ k)
                        ; (j = i1) → merid true i })
               (merid true i)

-- Deprecated version of S¹→SuspBool→S¹
c2s-s2c : ∀ (t : 1 -sphere) → c2s (s2c t) ≡ t
c2s-s2c north j = north
c2s-s2c south j = merid false j
c2s-s2c (merid true i) j = h2 i j
c2s-s2c (merid false i) j = merid false (i ∧ j)

-- Notation of the paper, current notation under S¹≡SuspBool
-- Proof of Lemma 4.1
1-sphere≡S¹ : 1 -sphere ≡ S¹
1-sphere≡S¹ = isoToPath (iso s2c c2s s2c-c2s c2s-s2c)

-- Definitions of S2 and S3
open S2 using (S²) public
open S3 using (S³) public

-- 4.2 Pushouts and the 3 × 3 Lemma
open Push using (Pushout) public
-- 3x3-span is implemented as a record
open PushProp using (3x3-span) public
open 3x3-span using (f□1) public
-- The rest of the definitions inside the 3x3-lemma
-- A□0-A○□ , A□○-A○□ ...
open 3x3-span using (3x3-lemma) public

-- 4.3 The Join and S³
open Join renaming (join to Join) using (S³≡joinS¹S¹) public
open JoinProp using (join-assoc) public

--------------------------------------------------------------------------------
-- 5.  The Hopf Fibration
--------------------------------------------------------------------------------

-- rot (denoted by _·_ here) in the paper is substituted by a rot and rotLoop in S1
open S1 using (_·_ ; rotLoop) public
open Hopf.S¹Hopf renaming ( HopfSuspS¹ to Hopf
                          ; JoinS¹S¹→TotalHopf to j2h
                          ; TotalHopf→JoinS¹S¹ to h2j)
                 using (HopfS²) public
open S1 renaming (rotInv-1 to lem-rot-inv) public
