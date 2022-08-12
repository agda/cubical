{-# OPTIONS --safe #-}
module Cubical.Data.FinWeak.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinWeak.Base
import Cubical.Data.FinData as FD

open import Cubical.Relation.Nullary

open Iso

private variable
  n : ℕ

FinPureIsProp : isProp (FinPure n)
FinPureIsProp zero zero = refl
FinPureIsProp (suc p) (suc q) = cong suc (FinPureIsProp p q)

FinPure→FinData : FinPure n → FD.Fin n
FinPure→FinData zero    = FD.zero
FinPure→FinData (suc p) = FD.suc (FinPure→FinData p)

FinWeak→FinData : Fin n → FD.Fin n
FinWeak→FinData (pure p)   = FinPure→FinData p
FinWeak→FinData (weaken p) = FD.weakenFin (FinWeak→FinData p)

FinData→FinWeak : FD.Fin n → Fin n
FinData→FinWeak {one} FD.zero = pure zero
FinData→FinWeak {suc (suc _)} FD.zero = weaken (FinData→FinWeak FD.zero)
FinData→FinWeak (FD.suc p) = sucFin (FinData→FinWeak p)

finWeakSuc : (p : Fin n) → FinWeak→FinData (sucFin p) ≡ FD.suc (FinWeak→FinData p)
finWeakSuc (pure _)   = refl
finWeakSuc (weaken p) = cong FD.weakenFin (finWeakSuc p)

FinWeak→FinData→FinWeak : (p : FD.Fin n) → FinWeak→FinData (FinData→FinWeak p) ≡ p
FinWeak→FinData→FinWeak {one} FD.zero = refl
FinWeak→FinData→FinWeak {suc (suc _)} FD.zero = cong FD.weakenFin (FinWeak→FinData→FinWeak FD.zero)
FinWeak→FinData→FinWeak (FD.suc p) =
  FinWeak→FinData (sucFin (FinData→FinWeak p)) ≡⟨ finWeakSuc ((FinData→FinWeak p))        ⟩
  FD.suc (FinWeak→FinData (FinData→FinWeak p)) ≡⟨ cong FD.suc (FinWeak→FinData→FinWeak p) ⟩
  FD.suc p ∎

FinData→FinWeak→FinPure : (p : FinPure n) → FinData→FinWeak (FinPure→FinData p) ≡ pure p
FinData→FinWeak→FinPure zero    = refl
FinData→FinWeak→FinPure (suc p) = cong sucFin (FinData→FinWeak→FinPure p)

weakeningFinData→FinWeak : (p : FD.Fin n) → FinData→FinWeak (FD.weakenFin p) ≡ weaken (FinData→FinWeak p)
weakeningFinData→FinWeak FD.zero    = refl
weakeningFinData→FinWeak (FD.suc p) = cong sucFin (weakeningFinData→FinWeak p)

FinData→FinWeak→FinData : (p : Fin n) → FinData→FinWeak (FinWeak→FinData p) ≡ p
FinData→FinWeak→FinData (pure p)   = FinData→FinWeak→FinPure p
FinData→FinWeak→FinData (weaken p) =
  FinData→FinWeak (FD.weakenFin (FinWeak→FinData p)) ≡⟨ weakeningFinData→FinWeak ((FinWeak→FinData p)) ⟩
  weaken (FinData→FinWeak (FinWeak→FinData p))       ≡⟨ cong weaken (FinData→FinWeak→FinData p)        ⟩
  weaken p ∎

FinWeakIsoFinData : Iso (Fin n) (FD.Fin n)
fun FinWeakIsoFinData = FinWeak→FinData
inv FinWeakIsoFinData = FinData→FinWeak
rightInv FinWeakIsoFinData = FinWeak→FinData→FinWeak
leftInv FinWeakIsoFinData = FinData→FinWeak→FinData

FinWeak≡FinData : Fin n ≡ FD.Fin n
FinWeak≡FinData = isoToPath FinWeakIsoFinData
