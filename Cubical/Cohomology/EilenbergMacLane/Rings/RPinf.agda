{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Cohomology.EilenbergMacLane.Rings.RPinf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Groups.RPinf
open import Cubical.Cohomology.EilenbergMacLane.RingStructure

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.Connected

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Vec

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.RPn

open import Cubical.Algebra.GradedRing.DirectSumHIT
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.Monoid.Instances.Nat

open Iso
open PlusBis
open RingTheory

eRP∞^ : (n : ℕ) → coHom n ℤ/2 (EM ℤ/2 1)
eRP∞^ zero = 1ₕ {G'' = ℤ/2Ring}
eRP∞^ (suc n) =
  subst (λ k → coHom k ℤ/2 (EM ℤ/2 1)) (+'-suc₁ n)
         (_⌣_ {G'' = ℤ/2Ring} {n = 1} {n} ∣ idfun _ ∣₂ (eRP∞^ n))

isConnected₀EM : ∀ {ℓ} (G : AbGroup ℓ) (n : ℕ) → isContr ∥ EM G (suc n) ∥₂
isConnected₀EM G n =
  isOfHLevelRetractFromIso 0 setTruncTrunc2Iso
    (isConnectedSubtr 2 n
      (subst (λ x → isConnected x (EM G (suc n)))
        (+-comm 2 n)
        (isConnectedEM (suc n))))

EMOne : (n : ℕ) → EM ℤ/2 ˣ n
EMOne zero = fone
EMOne (suc n) = EMOne n , 0ₖ (suc n)

eRP∞^-isGen : (n : ℕ) → Iso.inv (HⁿRP∞≅ℤ/2 n .fst) fone ≡ eRP∞^ n
eRP∞^-isGen zero = refl
eRP∞^-isGen (suc n) =
   (cong₂ (λ v w → ST.rec isSetSetTrunc
          (λ x → ∣ inv (RP→EM-ℤ/2-CharacIso (suc n)) x ∣₂)
          (ST.rec2 isSetSetTrunc (λ a b → ∣ a , b ∣₂)
           v w))
           (inv-∥EM-ℤ/2ˣ∥₀-Iso-fone n)
           (isContr→isProp (isConnected₀EM ℤ/2 n) _ ∣ (0ₖ (suc n)) ∣₂)
  ∙ cong ∣_∣₂ (funExt (λ x → rUnitₖ (suc n) _
           ∙ cong (subst (EM ℤ/2) (+'-suc₁ n))
              (cong₂ (_⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {n})
                (sym (transportRefl x))
                (cong (inv (RP→EM-ℤ/2-CharacIso n) (EMOne n))
                  (sym (transportRefl x))))))
  ∙ sym (substCommSlice (λ k → EM ℤ/2 1 → EM ℤ/2 k)
                        (λ k → coHom k ℤ/2 (EM ℤ/2 1))
       (λ _ → ∣_∣₂) (+'-suc₁ n)
       (λ x → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {n} x
         (inv (RP→EM-ℤ/2-CharacIso n) (EMOne n) x))))
  ∙ cong (subst (λ k → coHom k ℤ/2 (EM ℤ/2 1)) (+'-suc₁ n))
         (cong (_⌣_ {G'' = ℤ/2Ring} {n = 1} {n} ∣ idfun _ ∣₂)
           (cong (ST.rec isSetSetTrunc (λ x → ∣ inv (RP→EM-ℤ/2-CharacIso n) x ∣₂))
             (sym (inv-∥EM-ℤ/2ˣ∥₀-Iso-fone n))
         ∙ eRP∞^-isGen n))
  where
  inv-∥EM-ℤ/2ˣ∥₀-Iso-fone : (n : ℕ)
    → inv (∥EM-ℤ/2ˣ∥₀-Iso n) fone ≡ ∣ EMOne n ∣₂
  inv-∥EM-ℤ/2ˣ∥₀-Iso-fone zero = refl
  inv-∥EM-ℤ/2ˣ∥₀-Iso-fone (suc n) =
    cong₂ (λ v w → prodRec isSetSetTrunc (λ a b → ∣ a , b ∣₂)
        (v , w)) (inv-∥EM-ℤ/2ˣ∥₀-Iso-fone n)
          (isContr→isProp (isConnected₀EM ℤ/2 n) _ ∣ (0ₖ (suc n)) ∣₂)

eRP∞^-comp : (n m : ℕ) → _⌣_ {G'' = ℤ/2Ring} (eRP∞^ n) (eRP∞^ m) ≡ eRP∞^ (n +' m)
eRP∞^-comp zero m = 1ₕ-⌣ m (eRP∞^ m)
eRP∞^-comp (suc n) m =
    transport⌣ _ (+'-suc₁ n) _ _
  ∙ sym (compSubstℕ (sym (+'-assoc 1 n m) ∙ +'-suc₁ (n +' m)) (+'-suc n m)
        (cong₂ _+'_ (+'-suc₁ n) refl))
  ∙ cong (subst (λ k → coHom k ℤ/2 (EM ℤ/2 1)) (+'-suc n m))
      (sym (compSubstℕ (sym (+'-assoc 1 n m)) (+'-suc₁ (n +' m))
           (sym (+'-assoc 1 n m) ∙ +'-suc₁ (n +' m)))
      ∙ cong (subst (λ k → coHom k ℤ/2 (EM ℤ/2 1)) (+'-suc₁ (n +' m)))
         ((cong (subst (λ k → coHom k ℤ/2 (EM ℤ/2 1)) (sym (+'-assoc 1 n m)))
            (assoc⌣ 1 n m ∣ idfun _ ∣₂ (eRP∞^ n) (eRP∞^ m))
         ∙ subst⁻Subst  (λ k → coHom k ℤ/2 (EM ℤ/2 1)) (+'-assoc 1 n m) _)
         ∙ cong₂ (_⌣_ {G'' = ℤ/2Ring} {n = 1} {n +' m}) refl (eRP∞^-comp n m)))
  ∙ sym (help _ (sym (+'-suc n m)))
  where
  term = _⌣_ {G'' = ℤ/2Ring} {n = 1 +' n} {m}
          (_⌣_ {G'' = ℤ/2Ring} {n = 1} {n} ∣ idfun _ ∣₂ (eRP∞^ n)) (eRP∞^ m)

  help : {w : ℕ} (k : ℕ) (p : w ≡ k)
    → eRP∞^ w ≡ subst (λ k → coHom k ℤ/2 (EM ℤ/2 1)) (sym p) (eRP∞^ k)
  help = J> sym (transportRefl _)

  transport⌣ : {w v : ℕ} (k : ℕ) (p : w ≡ k)
    (x : coHom w ℤ/2 (EM ℤ/2 1)) (y : coHom v ℤ/2 (EM ℤ/2 1))
    → _⌣_ {G'' = ℤ/2Ring} (subst (λ k → coHom k ℤ/2 (EM ℤ/2 (suc zero))) p x) y
     ≡ subst (λ k → coHom k ℤ/2 (EM ℤ/2 (suc zero)))
             (cong₂ _+'_ p refl) (_⌣_ {G'' = ℤ/2Ring} x y)
  transport⌣ = J> λ x y
    → cong₂ (_⌣_ {G'' = ℤ/2Ring}) (transportRefl x) refl
     ∙ sym (transportRefl _)

HⁿRP∞≅ℤ/2⌣ : (n m : ℕ) (a b : ℤ/2 .fst)
  → Iso.inv (HⁿRP∞≅ℤ/2 (n +' m) .fst) (a ·ₘ b)
  ≡ _⌣_ {G'' = ℤ/2Ring} (Iso.inv (HⁿRP∞≅ℤ/2 n .fst) a)
                         (Iso.inv (HⁿRP∞≅ℤ/2 m .fst) b)
HⁿRP∞≅ℤ/2⌣ n m =
  ℤ/2-elim (λ b
    → IsGroupHom.pres1 (invGroupIso (HⁿRP∞≅ℤ/2 (n +' m)) .snd)
      ∙ sym (0ₕ-⌣ {G'' = ℤ/2Ring} n m (inv (cohomRP∞Iso m) b))
      ∙ cong₂ (_⌣_ {G'' = ℤ/2Ring})
         (sym (IsGroupHom.pres1 (invGroupIso (HⁿRP∞≅ℤ/2 n) .snd))) refl)
    (ℤ/2-elim (IsGroupHom.pres1 (invGroupIso (HⁿRP∞≅ℤ/2 (n +' m)) .snd)
      ∙ sym (⌣-0ₕ {G'' = ℤ/2Ring} n m (inv (cohomRP∞Iso n) fone))
      ∙ cong₂ (_⌣_ {G'' = ℤ/2Ring}) refl
        (sym (IsGroupHom.pres1 (invGroupIso (HⁿRP∞≅ℤ/2 m) .snd))))
    (main n m))
  where
  main : (n m : ℕ) → (Iso.inv (HⁿRP∞≅ℤ/2 (n +' m) .fst) fone
       ≡ _⌣_ {G'' = ℤ/2Ring} (Iso.inv (HⁿRP∞≅ℤ/2 n .fst) fone)
                              (Iso.inv (HⁿRP∞≅ℤ/2 m .fst) fone))
  main n m = eRP∞^-isGen (n +' m) ∙∙ sym (eRP∞^-comp n m)
         ∙∙ sym (cong₂ (_⌣_ {G'' = ℤ/2Ring}) (eRP∞^-isGen n) (eRP∞^-isGen m))


-- open import Cubical.Agebra.Monoids.Instance.NatVec

module _ {ℓ : Level} (n : ℕ) where
  private
    RP∞ = EM ℤ/2 1

  ℤ₂[x] = Poly ℤ/2CommRing 1

  ℤ₂[X] = CommRing→Ring (PolyCommRing ℤ/2CommRing 1)

  open GradedRing-⊕HIT-index
    NatMonoid
    (Poly ℤ/2CommRing)
    (λ n → CommRing→AbGroup (PolyCommRing ℤ/2CommRing n) .snd)

  open RingStr (snd (H*R ℤ/2Ring RP∞))
    renaming
    ( 0r        to 0H*RP
    ; 1r        to 1H*RP
    ; _+_       to _+H*RP_
    ; -_        to -H*RP_
    ; _·_       to _cupS_
    ; +Assoc    to +H*RPAssoc
    ; +IdR      to +H*RPIdR
    ; +Comm     to +H*RPComm
    ; ·Assoc    to ·H*RPAssoc
    ; is-set    to isSetH*RP
    ; ·DistR+   to ·DistR+H*
    ; ·DistL+   to ·DistL+H*)

  open RingStr (snd ℤ₂[X])
    renaming
    ( 0r        to 0Z₂X
    ; 1r        to 1Z₂X
    ; _+_       to _+Z₂X_
    ; -_        to -Z₂X_
    ; _·_       to _·Z₂X_
    ; +Assoc    to +Z₂XAssoc
    ; +IdR      to +Z₂XIdR
    ; +Comm     to +Z₂XComm
    ; ·Assoc    to ·Z₂XAssoc
    ; is-set    to isSetZ₂X
    ; ·DistR+   to ·DistR+Z₂
    ; ·DistL+   to ·DistL+Z₂)

  ℤ/2≅HⁿRP∞ : (n : ℕ) → AbGroupEquiv ℤ/2 (coHomGr n ℤ/2 (EM ℤ/2 1))
  ℤ/2≅HⁿRP∞ n = invGroupEquiv (GroupIso→GroupEquiv (HⁿRP∞≅ℤ/2 n))

  ℤ/2≅HⁿRP∞pres0 : (n : ℕ) → ℤ/2≅HⁿRP∞ n .fst .fst fzero ≡ 0ₕ n
  ℤ/2≅HⁿRP∞pres0 n = IsGroupHom.pres1 (ℤ/2≅HⁿRP∞ n .snd)

  ℤ₂[X]→H*[RP∞,ℤ₂]-main : Vec ℕ 1 → ℤ/2 .fst → fst (H*R ℤ/2Ring RP∞)
  ℤ₂[X]→H*[RP∞,ℤ₂]-main (n ∷ []) g = base n (ℤ/2≅HⁿRP∞ n .fst .fst g)

  ℤ₂[X]→H*[RP∞,ℤ₂]-main-coh₁ : (r : Vec ℕ 1) →
      ℤ₂[X]→H*[RP∞,ℤ₂]-main r fzero ≡ neutral
  ℤ₂[X]→H*[RP∞,ℤ₂]-main-coh₁ (n ∷ []) =
      (λ i → base {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP∞}
                   {AGP = λ n → coHomGr n ℤ/2 RP∞ .snd} n (ℤ/2≅HⁿRP∞pres0 n i))
      ∙ base-neutral {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP∞}
                     {AGP = λ n → coHomGr n ℤ/2 RP∞ .snd} n

  ℤ₂[X]→H*[RP∞,ℤ₂]-fun : ℤ₂[x] → fst (H*R ℤ/2Ring RP∞)
  ℤ₂[X]→H*[RP∞,ℤ₂]-fun =
    DS-Rec-Set.f _ _ _ _ isSetH*RP
      neutral
      ℤ₂[X]→H*[RP∞,ℤ₂]-main
      _add_
      addAssoc
      addRid
      addComm
      ℤ₂[X]→H*[RP∞,ℤ₂]-main-coh₁
      λ {(n ∷ []) → λ a b → base-add n _ _
        ∙ (λ i → base {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP∞}
                   {AGP = λ n → coHomGr n ℤ/2 RP∞ .snd} n
                   (IsGroupHom.pres· (ℤ/2≅HⁿRP∞ n .snd) a b (~ i)))}

  open import Cubical.Foundations.Equiv.Properties
  open import Cubical.Foundations.Transport

  ℤ/2[X]→H*[RP∞,ℤ/2]-pres· : (x y : ℤ₂[x])
    → ℤ₂[X]→H*[RP∞,ℤ₂]-fun (RingStr._·_ (snd ℤ₂[X]) x y)
    ≡ (ℤ₂[X]→H*[RP∞,ℤ₂]-fun x cupS ℤ₂[X]→H*[RP∞,ℤ₂]-fun y)
  ℤ/2[X]→H*[RP∞,ℤ/2]-pres· =
    DS-Ind-Prop.f _ _ _ _
      (λ _ → isPropΠ λ _ → trunc _ _)
      (λ _ → refl)
      (λ v a →
      DS-Ind-Prop.f _ _ _ _
      (λ _ → trunc _ _)
      (cong (ℤ₂[X]→H*[RP∞,ℤ₂]-fun)
        (0RightAnnihilates ℤ₂[X] (base v a))
        ∙ sym (0RightAnnihilates (H*R ℤ/2Ring RP∞)
                (ℤ₂[X]→H*[RP∞,ℤ₂]-fun (base v a))))
      (λ w b → main v w a b)
      λ {x} {y} p q → cong ℤ₂[X]→H*[RP∞,ℤ₂]-fun (·DistR+Z₂ (base v a) x y)
                    ∙ cong₂ _add_ p q
                    ∙ sym (·DistR+H* (ℤ₂[X]→H*[RP∞,ℤ₂]-fun (base v a))
                            (ℤ₂[X]→H*[RP∞,ℤ₂]-fun x)
                            (ℤ₂[X]→H*[RP∞,ℤ₂]-fun y)))
      λ {x} {y} p q z
       → cong (ℤ₂[X]→H*[RP∞,ℤ₂]-fun)
           (·DistL+Z₂ x y z)
        ∙ cong₂ _add_ (p z) (q z)
    where
    main : (v w : Vec ℕ 1) (a b : ℤ/2 .fst)
      → ℤ₂[X]→H*[RP∞,ℤ₂]-fun (base v a ·Z₂X base w b)
       ≡ ℤ₂[X]→H*[RP∞,ℤ₂]-fun (base v a) cupS ℤ₂[X]→H*[RP∞,ℤ₂]-fun (base w b)
    main (n ∷ []) (m ∷ []) a b =
        (λ i → base {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP∞}
                    {AGP = λ n → coHomGr n ℤ/2 RP∞ .snd}
                    (+'≡+ n m (~ i))
                    (inv (cohomRP∞Iso (+'≡+ n m (~ i))) (a ·ₘ b)))
      ∙ λ i → base {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP∞}
                    {AGP = λ n → coHomGr n ℤ/2 RP∞ .snd} (n +' m)
                    (HⁿRP∞≅ℤ/2⌣ n m a b i)

  ℤ₂[X]→H*[RP∞,ℤ₂] : RingHom ℤ₂[X] (H*R ℤ/2Ring RP∞)
  fst ℤ₂[X]→H*[RP∞,ℤ₂] = ℤ₂[X]→H*[RP∞,ℤ₂]-fun
  snd ℤ₂[X]→H*[RP∞,ℤ₂] = makeIsRingHom refl (λ _ _ → refl) ℤ/2[X]→H*[RP∞,ℤ/2]-pres·

  H*[RP∞,ℤ₂]→ℤ₂[X] : H*R ℤ/2Ring RP∞ .fst → ℤ₂[X] .fst
  H*[RP∞,ℤ₂]→ℤ₂[X] = DS-Rec-Set.f _ _ _ _ trunc
    neutral
    (λ r x → base (r ∷ []) (invEq (ℤ/2≅HⁿRP∞ r .fst) x))
    (RingStr._+_ (snd ℤ₂[X]))
    (RingStr.+Assoc (snd ℤ₂[X]))
    (RingStr.+IdR (snd ℤ₂[X]))
    (RingStr.+Comm (snd ℤ₂[X]))
    (λ r → cong (base (r ∷ []))
      (IsGroupHom.pres1 (invGroupEquiv (ℤ/2≅HⁿRP∞ r) .snd))
      ∙ base-neutral _)
    λ r a b → base-add (r ∷ []) _ _
      ∙ cong (base (r ∷ []))
        (sym (IsGroupHom.pres· (invGroupEquiv (ℤ/2≅HⁿRP∞ r) .snd) a b))

  ℤ₂[X]→H*[RP∞,ℤ₂]→ℤ₂[X] : (x : _)
    → H*[RP∞,ℤ₂]→ℤ₂[X] (ℤ₂[X]→H*[RP∞,ℤ₂] .fst x) ≡ x
  ℤ₂[X]→H*[RP∞,ℤ₂]→ℤ₂[X] = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
    refl
    (λ{ (x ∷ []) a → cong (base (x ∷ [])) (retEq (ℤ/2≅HⁿRP∞ x .fst) a)})
    (λ p q → cong₂ _add_ p q)

  H*[RP∞,ℤ₂]→ℤ₂[X]→H*[RP∞,ℤ₂] : (x : _)
    → ℤ₂[X]→H*[RP∞,ℤ₂] .fst (H*[RP∞,ℤ₂]→ℤ₂[X] x) ≡ x
  H*[RP∞,ℤ₂]→ℤ₂[X]→H*[RP∞,ℤ₂] = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
    refl
    (λ{ x a → cong (base {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP∞}
                    {AGP = λ n → coHomGr n ℤ/2 RP∞ .snd} x)
                    (secEq (ℤ/2≅HⁿRP∞ x .fst) a)})
    λ p q → cong₂ (_add_ {Idx = ℕ} {P = λ n → coHom n ℤ/2 RP∞}
                          {AGP = λ n → coHomGr n ℤ/2 RP∞ .snd})
                   p q


  ℤ₂[X]≅H*[RP∞,ℤ₂] : RingEquiv ℤ₂[X] (H*R ℤ/2Ring RP∞)
  fst ℤ₂[X]≅H*[RP∞,ℤ₂] =
    isoToEquiv (iso (ℤ₂[X]→H*[RP∞,ℤ₂] .fst) H*[RP∞,ℤ₂]→ℤ₂[X]
                    H*[RP∞,ℤ₂]→ℤ₂[X]→H*[RP∞,ℤ₂] ℤ₂[X]→H*[RP∞,ℤ₂]→ℤ₂[X])
  snd ℤ₂[X]≅H*[RP∞,ℤ₂] = ℤ₂[X]→H*[RP∞,ℤ₂] .snd

  H*[RP∞,ℤ₂]≅ℤ₂[X] : RingEquiv (H*R ℤ/2Ring RP∞) ℤ₂[X]
  H*[RP∞,ℤ₂]≅ℤ₂[X] = RingEquivs.invRingEquiv ℤ₂[X]≅H*[RP∞,ℤ₂]
