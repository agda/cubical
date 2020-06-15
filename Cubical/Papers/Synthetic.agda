{-# OPTIONS --cubical --no-import-sorts --safe #-}
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
import Cubical.HITs.Hopf                      as Hopf

--------------------------------------------------------------------------------
-- 2.  Cubical Agda
-- 2.1 The Interval and Path Types
-- 2.2 Transport and Composition
-- 2.3 Higher Inductive Types
-- 2.4 Glue Types and Univalence
--------------------------------------------------------------------------------

-- 2.1 The Interval and Path Types
open Path using (PathP)
open Prelude using (_≡_ ; refl ; funExt)
open Prelude renaming (sym to _⁻¹)

-- 2.2 Transport and Composition
open Prelude using (transport ; subst ; J ; JRefl)
open PrimitiveCubical using (Partial)
open Bool using (Bool ; true ; false)

partialBool : ∀ i → Partial (i ∨ ~ i) Bool
partialBool i = λ {(i = i1) → true
								 ; (i = i0) → false}

open CorePrimitives using (inS ; outS ; hcomp)
open Prelude using (_∙_)

-- 2.3 Higher Inductive Types
open S1 using (S¹ ; base ; loop)

double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

-- 2.4 Glue Types and Univalence
open Equiv using (idEquiv)
open CoreGlue using (Glue)
open Univalence using (ua)

--------------------------------------------------------------------------------
-- 3.  The Circle and Torus
-- 3.1 The Loop Spaces of the Circle and Torus
--------------------------------------------------------------------------------

open T2 using (Torus ; point ; line1 ; line2 ; square
								; t2c ; c2t ; c2t-t2c ; t2c-c2t ; Torus≡S¹×S¹)

-- 3.1 The Loop Spaces of the Circle and Torus
open S1 using (ΩS¹)
open T2 using (ΩTorus)
open Int using (Int ; pos ; negsuc)
open IntProp using (sucPathInt)
open S1 using (helix ; winding)

-- Examples computing the winding numbers of the circle
_ : winding (loop ∙ loop ∙ loop) ≡ pos 3
_ = refl

_ : winding ((loop ⁻¹) ∙ loop ∙ (loop ⁻¹)) ≡ negsuc 0
_ = refl

open S1 renaming (intLoop to loopn)
open S1 renaming (windingIntLoop to winding-loopn)
open S1 using (encode ; decode ; decodeEncode ; ΩS¹≡Int)
open Isomorphism using (isoToPath ; iso)

-- Notation of the paper, current notation under ΩS¹≡Int
ΩS¹≡Int' : ΩS¹ ≡ Int
ΩS¹≡Int' = isoToPath (iso winding loopn
											winding-loopn (decodeEncode base))

open T2 using (ΩTorus≡Int×Int ; windingTorus)

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
open Suspension using (Susp ; north ; south ; merid)
open Sn using (S₊)
open Suspension using (SuspBool→S¹ ; S¹→SuspBool
											; SuspBool→S¹→SuspBool
											; S¹→SuspBool→S¹)

-- Deprecated version of S₊
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool using (Bool)
_-sphere : ℕ → Set
0 -sphere = Bool
(suc n) -sphere = Susp (n -sphere)

-- Lemma 4.1. The (1)-sphere is equal to the circle S1.

open import Agda.Builtin.Bool using (true ; false)
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

open GroupoidLaws using (rUnit)
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
open S2 using (S²)
open S3 using (S³)

-- 4.2 Pushouts and the 3 × 3 Lemma
open Push using (Pushout)
-- 3x3-span is implemented as a record
open PushProp using (3x3-span)
open 3x3-span using (f□1)
-- The rest of the definitions inside the 3x3-lemma
-- A□0-A○□ , A□○-A○□ ...
open 3x3-span using (3x3-lemma)

-- 4.3 The Join and S³
open Join renaming (join to Join) using (S³≡joinS¹S¹)
open JoinProp using (join-assoc)

--------------------------------------------------------------------------------
-- 5.  The Hopf Fibration
--------------------------------------------------------------------------------

-- rot in the paper is substituted by a rot and rotLoop in S1
open S1 using (rot ; rotLoop)
open Hopf renaming (HopfSuspS¹ to Hopf
									; JoinS¹S¹→TotalHopf to j2h
									; TotalHopf→JoinS¹S¹ to h2j)
					using (HopfS²)
open S1 renaming (rotInv-1 to lem-rot-inv)
