{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Instances.IntMod where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Algebra.AbGroup

open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.ZAction

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

ℤAbGroup/_ : ℕ → AbGroup ℓ-zero
ℤAbGroup/ n = Group→AbGroup (ℤGroup/ n) (comm n)
  where
  comm : (n : ℕ) (x y : fst (ℤGroup/ n))
   → GroupStr._·_ (snd (ℤGroup/ n)) x y
    ≡ GroupStr._·_ (snd (ℤGroup/ n)) y x
  comm zero = +Comm
  comm (suc n) = +ₘ-comm

ℤ/2 : AbGroup ℓ-zero
ℤ/2 = ℤAbGroup/ 2

ℤ/2[2]≅ℤ/2 : AbGroupIso (ℤ/2 [ 2 ]ₜ) ℤ/2
Iso.fun (fst ℤ/2[2]≅ℤ/2) = fst
Iso.inv (fst ℤ/2[2]≅ℤ/2) x = x , cong (x +ₘ_) (+ₘ-rUnit x) ∙ x+x x
  where
  x+x : (x : ℤ/2 .fst) → x +ₘ x ≡ fzero
  x+x = ℤ/2-elim refl refl
Iso.rightInv (fst ℤ/2[2]≅ℤ/2) x = Σ≡Prop (λ _ → isProp≤) refl
Iso.leftInv (fst ℤ/2[2]≅ℤ/2) x = Σ≡Prop (λ _ → isSetFin _ _) refl
snd ℤ/2[2]≅ℤ/2 = makeIsGroupHom λ _ _ → refl

ℤ/2/2≅ℤ/2 : AbGroupIso (ℤ/2 /^ 2) ℤ/2
Iso.fun (fst ℤ/2/2≅ℤ/2) =
  SQ.rec isSetFin (λ x → x) lem
  where
  lem : _
  lem = ℤ/2-elim (ℤ/2-elim (λ _ → refl)
        (PT.rec (isSetFin  _ _)
          (uncurry (ℤ/2-elim
          (λ p → ⊥.rec (snotz (sym (cong fst p))))
           λ p → ⊥.rec (snotz (sym (cong fst p)))))))
        (ℤ/2-elim (PT.rec (isSetFin  _ _)
          (uncurry (ℤ/2-elim
          (λ p → ⊥.rec (snotz (sym (cong fst p))))
           λ p → ⊥.rec (snotz (sym (cong fst p))))))
          λ _ → refl)
Iso.inv (fst ℤ/2/2≅ℤ/2) = [_]
Iso.rightInv (fst ℤ/2/2≅ℤ/2) _ = refl
Iso.leftInv (fst ℤ/2/2≅ℤ/2) =
  SQ.elimProp (λ _ → squash/ _ _) λ _ → refl
snd ℤ/2/2≅ℤ/2 = makeIsGroupHom
  (SQ.elimProp (λ _ → isPropΠ λ _ → isSetFin _ _)
  λ a → SQ.elimProp (λ _ → isSetFin _ _) λ b → refl)

ℤTorsion : (n : ℕ) → isContr (fst (ℤAbGroup [ (suc n) ]ₜ))
fst (ℤTorsion n) = AbGroupStr.0g (snd (ℤAbGroup [ (suc n) ]ₜ))
snd (ℤTorsion n) (a , p) = Σ≡Prop (λ _ → isSetℤ _ _)
  (sym (help a (ℤ·≡· (pos (suc n)) a ∙ p)))
  where
  help : (a : ℤ) → a +ℤ pos n ·ℤ a ≡ 0 → a ≡ 0
  help (pos zero) p = refl
  help (pos (suc a)) p =
    ⊥.rec (snotz (injPos (pos+ (suc a) (n ·ℕ suc a)
                 ∙ cong (pos (suc a) +ℤ_) (pos·pos n (suc a)) ∙ p)))
  help (negsuc a) p = ⊥.rec
    (snotz (injPos (cong -ℤ_ (negsuc+ a (n ·ℕ suc a)
                 ∙ (cong (negsuc a +ℤ_)
                     (cong (-ℤ_) (pos·pos n (suc a)))
                 ∙ sym (cong (negsuc a +ℤ_) (pos·negsuc n a)) ∙ p)))))
