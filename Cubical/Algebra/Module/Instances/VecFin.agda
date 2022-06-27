open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Module

module Cubical.Algebra.Module.Instances.VecFin {ℓ} (R : Ring ℓ) {n : ℕ} where

open module R' = RingStr (snd R) renaming (_+_ to _+r_; -_ to -r_)
open IsMonoid using (isSemigroup; ·IdR; ·IdL)
open LeftModuleStr
open IsLeftModule
open IsSemigroup using (is-set; ·Assoc)
open IsGroup using (isMonoid; ·InvR; ·InvL)
open IsAbGroup

FinVecLeftModule : LeftModule R ℓ
fst FinVecLeftModule = FinVec ⟨ R ⟩ n
0m (snd FinVecLeftModule) _ = 0r
_+_ (snd FinVecLeftModule) xs ys z = xs z +r ys z
-_ (snd FinVecLeftModule) xs z = -r xs z
_⋆_ (snd FinVecLeftModule) r xs z = r · xs z
is-set (isSemigroup (isMonoid (isGroup (+IsAbGroup (isLeftModule (snd FinVecLeftModule)))))) =
  isSet→ R'.is-set
·Assoc (isSemigroup (isMonoid (isGroup (+IsAbGroup (isLeftModule (snd FinVecLeftModule)))))) _ _ _ =
  funExt λ _ → R'.+Assoc _ _ _
·IdR (isMonoid (isGroup (+IsAbGroup (isLeftModule (snd FinVecLeftModule))))) _ = funExt λ _ → R'.+IdR _
·IdL (isMonoid (isGroup (+IsAbGroup (isLeftModule (snd FinVecLeftModule))))) _ = funExt λ _ → R'.+IdL _
·InvR (isGroup (+IsAbGroup (isLeftModule (snd FinVecLeftModule)))) _ = funExt λ _ → R'.+InvR _
·InvL (isGroup (+IsAbGroup (isLeftModule (snd FinVecLeftModule)))) _ = funExt λ _ → R'.+InvL _
+Comm (+IsAbGroup (isLeftModule (snd FinVecLeftModule))) _ _ = funExt λ _ → R'.+Comm _ _
⋆Assoc (isLeftModule (snd FinVecLeftModule)) _ _ _ = funExt λ _ → sym (R'.·Assoc _ _ _)
⋆DistR+ (isLeftModule (snd FinVecLeftModule)) _ _ _ = funExt λ _ → ·DistR+ _ _ _
⋆DistL+ (isLeftModule (snd FinVecLeftModule)) _ _ _ = funExt λ _ → ·DistL+ _ _ _
⋆IdL (isLeftModule (snd FinVecLeftModule)) _ = funExt λ _ → R'.·IdL _
