{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.Data.Int as Int
  renaming ( ℤ to ℤ ; _+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)
open import Cubical.Data.Nat
  renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open CommRingStr using (0r ; 1r ; _+_ ; _·_ ; -_ ; isCommRing)

ℤCommRing : CommRing ℓ-zero
fst ℤCommRing = ℤ
0r (snd ℤCommRing) = 0
1r (snd ℤCommRing) = 1
_+_ (snd ℤCommRing) = _+ℤ_
_·_ (snd ℤCommRing) = _·ℤ_
- snd ℤCommRing = -ℤ_
isCommRing (snd ℤCommRing) = isCommRingℤ
  where
  abstract
    isCommRingℤ : IsCommRing 0 1 _+ℤ_ _·ℤ_ -ℤ_
    isCommRingℤ = makeIsCommRing isSetℤ Int.+Assoc (λ _ → refl)
                                 -Cancel Int.+Comm Int.·Assoc
                                 Int.·IdR ·DistR+ Int.·Comm

ℤAbGroup : AbGroup ℓ-zero
ℤAbGroup = Group→AbGroup ℤGroup +Comm

ℤTorsion : (n : ℕ) → isContr (fst (ℤAbGroup [ (suc n) ]))
fst (ℤTorsion n) = AbGroupStr.0g (snd (ℤAbGroup [ (suc n) ]))
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
