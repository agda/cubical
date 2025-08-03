module Cubical.Algebra.Group.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Int
  renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_; -_ to -ℤ_ ; _·_ to _·ℤ_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Fin.Inductive.Base

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties


open GroupStr

ℤGroup : Group₀
fst ℤGroup = ℤ
1g (snd ℤGroup) = 0
_·_ (snd ℤGroup) = _+ℤ_
inv (snd ℤGroup) = -ℤ_
isGroup (snd ℤGroup) = isGroupℤ
  where
  abstract
    isGroupℤ : IsGroup (pos 0) (_+ℤ_) (-ℤ_)
    isGroupℤ = makeIsGroup isSetℤ
                           +Assoc (λ _ → refl) (+Comm 0)
                           -Cancel -Cancel'

ℤHom : (n : ℤ) → GroupHom ℤGroup ℤGroup
fst (ℤHom n) x = n ·ℤ x
snd (ℤHom n) =
  makeIsGroupHom λ x y → ·DistR+ n x y

negEquivℤ : GroupEquiv ℤGroup ℤGroup
fst negEquivℤ =
  isoToEquiv
    (iso (GroupStr.inv (snd ℤGroup))
         (GroupStr.inv (snd ℤGroup))
         (GroupTheory.invInv ℤGroup)
         (GroupTheory.invInv ℤGroup))
snd negEquivℤ =
  makeIsGroupHom -Dist+

sumFinGroupℤComm : (G : Group₀) (h : GroupIso G ℤGroup) {n : ℕ}
  (f : Fin n → fst G) → sumFinℤ {n = n} (λ a → Iso.fun (fst h) (f a))
  ≡ Iso.fun (fst h) (sumFinGroup G {n = n} f)
sumFinGroupℤComm G h {n = zero} f = sym (IsGroupHom.pres1 (snd h))
sumFinGroupℤComm G h {n = suc n} f =
    cong₂ _+ℤ_ (λ _ → Iso.fun (fst h) (f flast))
      (sumFinGroupℤComm G h {n = n} (f ∘ injectSuc {n = n}))
  ∙ sym (IsGroupHom.pres· (snd h) (f flast)
    (sumFinGroup G {n = n} (λ x → f (injectSuc {n = n} x))))
