{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.BoolCommRing where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Bool

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup

open CommRingStr
open IsCommRing
open IsMonoid
open IsSemigroup
open IsRing
open IsAbGroup
open IsGroup

BoolCommRing : CommRing ℓ-zero
fst BoolCommRing = Bool
0r (snd BoolCommRing) = false
1r (snd BoolCommRing) = true
_+_ (snd BoolCommRing) = _⊕_
_·_ (snd BoolCommRing) = _and_
- snd BoolCommRing = idfun Bool
is-set (isSemigroup (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))))) = isSetBool
·Assoc (isSemigroup (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))))) false false _ = refl
·Assoc (isSemigroup (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))))) false true _ = refl
·Assoc (isSemigroup (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))))) true false _ = refl
·Assoc (isSemigroup (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))))) true true false = refl
·Assoc (isSemigroup (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))))) true true true = refl
·IdR (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing)))))) false = refl
·IdR (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing)))))) true = refl
·IdL (isMonoid (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing)))))) _ = refl
·InvR (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))) false = refl
·InvR (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))) true = refl
·InvL (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))) false = refl
·InvL (isGroup (+IsAbGroup (isRing (isCommRing (snd BoolCommRing))))) true = refl
+Comm (+IsAbGroup (isRing (isCommRing (snd BoolCommRing)))) false false = refl
+Comm (+IsAbGroup (isRing (isCommRing (snd BoolCommRing)))) false true = refl
+Comm (+IsAbGroup (isRing (isCommRing (snd BoolCommRing)))) true false = refl
+Comm (+IsAbGroup (isRing (isCommRing (snd BoolCommRing)))) true true = refl
is-set (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) = isSetBool
·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) false false false = refl
·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) false false true = refl
·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) false true false = refl
·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) false true true = refl
·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) true false false = refl
·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) true false true = refl
·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) true true false = refl
·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd BoolCommRing))))) true true true = refl
·IdR (·IsMonoid (isRing (isCommRing (snd BoolCommRing)))) false = refl
·IdR (·IsMonoid (isRing (isCommRing (snd BoolCommRing)))) true = refl
·IdL (·IsMonoid (isRing (isCommRing (snd BoolCommRing)))) false = refl
·IdL (·IsMonoid (isRing (isCommRing (snd BoolCommRing)))) true = refl
·DistR+ (isRing (isCommRing (snd BoolCommRing))) false false false = refl
·DistR+ (isRing (isCommRing (snd BoolCommRing))) false false true = refl
·DistR+ (isRing (isCommRing (snd BoolCommRing))) false true false = refl
·DistR+ (isRing (isCommRing (snd BoolCommRing))) false true true = refl
·DistR+ (isRing (isCommRing (snd BoolCommRing))) true false false = refl
·DistR+ (isRing (isCommRing (snd BoolCommRing))) true false true = refl
·DistR+ (isRing (isCommRing (snd BoolCommRing))) true true false = refl
·DistR+ (isRing (isCommRing (snd BoolCommRing))) true true true = refl

·DistL+ (isRing (isCommRing (snd BoolCommRing))) false false false = refl
·DistL+ (isRing (isCommRing (snd BoolCommRing))) false false true = refl
·DistL+ (isRing (isCommRing (snd BoolCommRing))) false true false = refl
·DistL+ (isRing (isCommRing (snd BoolCommRing))) false true true = refl
·DistL+ (isRing (isCommRing (snd BoolCommRing))) true false false = refl
·DistL+ (isRing (isCommRing (snd BoolCommRing))) true false true = refl
·DistL+ (isRing (isCommRing (snd BoolCommRing))) true true false = refl
·DistL+ (isRing (isCommRing (snd BoolCommRing))) true true true = refl
·Comm (isCommRing (snd BoolCommRing)) false false = refl
·Comm (isCommRing (snd BoolCommRing)) false true = refl
·Comm (isCommRing (snd BoolCommRing)) true false = refl
·Comm (isCommRing (snd BoolCommRing)) true true = refl
