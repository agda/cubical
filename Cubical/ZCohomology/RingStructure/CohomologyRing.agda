{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.RingStructure.CohomologyRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring

open import Cubical.Algebra.DirectSum.Base
open import Cubical.Algebra.AbGroup.Instances.DirectSum

open import Cubical.HITs.SetTruncation as ST

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

private variable
  ℓ ℓ' : Level

open Iso

-----------------------------------------------------------------------------
-- Definition Cohomology Ring


module intermediate-def where
  H*AbGr : (A : Type ℓ) → AbGroup ℓ
  H*AbGr A = ⊕-AbGr ℕ (λ n → coHom n A) (λ n → snd (coHomGroup n A))

  H* : (A : Type ℓ) → Type ℓ
  H* A = fst (H*AbGr A)

module CupRingProperties (A : Type ℓ) where
  open intermediate-def
  open AbGroupStr (snd (H*AbGr A))
  open AbGroupTheory (H*AbGr A)

  _cup_ : H* A → H* A → H* A
  _cup_ = DS-Rec-Set.f ℕ (λ n → coHom n A) (λ n → snd (coHomGroup n A))
          (H* A → H* A)
          (λ f g p q i j x → is-set (f x) (g x) (λ X → p X x) (λ X → q X x) i j)
          -- elements
          (λ x → 0g)
          (λ n a → DS-Rec-Set.f ℕ _ _ (H* A) is-set
                    -- elements
                    0g
                    (λ m b → base (n +' m) (a ⌣ b))
                    _+_
                    -- equations
                    assoc
                    rid
                    comm
                    (λ m → (cong (base (n +' m)) (⌣-0ₕ n m a)) ∙ (base-neutral (n +' m)))
                    λ m b c → base-add (n +' m) (a ⌣ b) (a ⌣ c) ∙ cong (base (n +' m)) (sym (leftDistr-⌣ n m a b c)))
          (λ U V y → (U y) + (V y))
          -- equations
          (λ xs ys zs i y → assoc (xs y) (ys y) (zs y) i)
          (λ xs i y       → rid (xs y) i)
          (λ xs ys i y    → comm (xs y) (ys y) i)
          (λ n → funExt(
                  DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
                  refl
                  (λ m b → cong (base (n +' m)) (0ₕ-⌣ n m b) ∙ base-neutral (n +' m))
                  λ {U V} ind-U ind-V → (cong₂ _+_ ind-U ind-V) ∙ (rid 0g)))
          λ n a b → funExt (
                     DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
                     (rid 0g)
                     (λ m c → (base-add (n +' m) (a ⌣ c) (b ⌣ c)) ∙ (cong (base (n +' m)) (sym (rightDistr-⌣ n m a b c))))
                     λ {U V} ind-U ind-V → comm-4 _ _ _ _ ∙ cong₂ _+_ ind-U ind-V)

  1H* : H* A
  1H* = base 0 1⌣

  cupAssoc : (x y z : H* A) → x cup (y cup z) ≡ (x cup y) cup z
  cupAssoc = DS-Ind-Prop.f ℕ _ _ _
              (λ x p q i y z j → is-set _ _ (p y z) (q y z) i j)
              (λ y z → refl)
              (λ n a → DS-Ind-Prop.f ℕ _ _ _
                        (λ y p q i z j → is-set _ _ (p z) (q z) i j)
                        (λ z → refl)
                        (λ m b → DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
                                  refl
                                  (λ k c → (cong (base (n +' (m +' k))) (assoc-⌣ n m k a b c))
                                             ∙ sym (constSubstCommSlice (λ n → coHom n A) (H* A) base (sym (+'-assoc n m k)) ((a ⌣ b) ⌣ c)))
                                  λ {U V} ind-U ind-V → cong₂ _+_ ind-U ind-V)
                        λ {U V} ind-U ind-V z → cong₂ _+_ (ind-U z) (ind-V z))
              λ {U V} ind-U ind-V y z → cong₂ _+_ (ind-U y z) (ind-V y z)

  cupIdR : (x : H* A) → x cup 1H* ≡ x
  cupIdR = DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
            refl
            (λ n a → (cong (base (n +' 0)) (lUnit⌣ n a)) ∙ sym (constSubstCommSlice (λ n → coHom n A) (H* A) base (sym (n+'0 n)) a))
            λ {U V} ind-U ind-V → (cong₂ _+_ ind-U ind-V)

  cupIdL : (x : H* A) → 1H* cup x ≡ x
  cupIdL = DS-Ind-Prop.f ℕ _ _ _ (λ _ → is-set _ _)
            refl
            (λ n a → cong (base n) (rUnit⌣ n a))
            (λ {U V} ind-U ind-V → cong₂ _+_ ind-U ind-V)

  cupDistR : (x y z : H* A) → x cup (y + z) ≡ (x cup y) + (x cup z)
  cupDistR = DS-Ind-Prop.f ℕ _ _ _
               (λ x p q i y z j → is-set _ _ (p y z) (q y z) i j)
               (λ y z → sym (rid 0g))
               (λ n a y z → refl)
               λ {U V} ind-U ind-V y z → cong₂ _+_ (ind-U y z) (ind-V y z) ∙ comm-4 (U cup y) (U cup z) (V cup y) (V cup z)

  cupDistL : (x y z : H* A) → (x + y) cup z ≡ (x cup z) + (y cup z)
  cupDistL = λ x y z → refl

-----------------------------------------------------------------------------
-- Graded Comutative Ring

  -- def + commutation with base
  -^-gen : (n m : ℕ) → (p : isEvenT n ⊎ isOddT n) → (q : isEvenT m ⊎ isOddT m)
          → H* A → H* A
  -^-gen n m (inl p)      q  x = x
  -^-gen n m (inr p) (inl q) x = x
  -^-gen n m (inr p) (inr q) x = - x

  -^_·_ : (n m : ℕ) → H* A → H* A
  -^_·_ n m x = -^-gen n m (evenOrOdd n) (evenOrOdd m) x

  -^-gen-base : {k : ℕ} → (n m : ℕ) → (p : isEvenT n ⊎ isOddT n) → (q : isEvenT m ⊎ isOddT m)
              (a : coHom k A) → -^-gen n m p q (base k a) ≡ base k (-ₕ^-gen n m p q a)
  -^-gen-base n m (inl p) q a = refl
  -^-gen-base n m (inr p) (inl q) a = refl
  -^-gen-base n m (inr p) (inr q) a = refl

  -^-base : {k : ℕ} → (n m : ℕ) → (a : coHom k A) → (-^ n · m) (base k a) ≡ base k ((-ₕ^ n · m) a)
  -^-base n m a = -^-gen-base n m (evenOrOdd n) (evenOrOdd m) a


module _ (A : Type ℓ) where
  open intermediate-def renaming (H* to H*')
  open CupRingProperties A
  open AbGroupStr (snd (H*AbGr A))
  open AbGroupTheory (H*AbGr A)

  H*R : Ring ℓ
  fst H*R = H*' A
  RingStr.0r (snd H*R) = 0g
  RingStr.1r (snd H*R) = 1H*
  RingStr._+_ (snd H*R) = _+_
  RingStr._·_ (snd H*R) = _cup_
  RingStr.- snd H*R = -_
  RingStr.isRing (snd H*R) = makeIsRing is-set
                                        assoc rid (λ x → fst (inverse x)) comm
                                        cupAssoc cupIdR cupIdL cupDistR cupDistL


  H* : Type ℓ
  H* = fst H*R

  gradCommRing : (n m : ℕ) → (a : coHom n A) → (b : coHom m A) →
                 (base n a) cup (base m b) ≡ (-^ n · m) ((base m b) cup (base n a))
  gradCommRing n m a b = base (n +' m) (a ⌣ b)
                                 ≡⟨ cong (base (n +' m)) (gradedComm-⌣ n m a b) ⟩
                        base (n +' m) ((-ₕ^ n · m) (subst (λ n₁ → coHom n₁ A) (+'-comm m n) (b ⌣ a)))
                                 ≡⟨ sym (-^-base n m (subst (λ k → coHom k A) (+'-comm m n) (b ⌣ a))) ⟩
                        (-^ n · m)  (base (n +' m) (subst (λ k → coHom k A) (+'-comm m n) (b ⌣ a)))
                                 ≡⟨ cong (-^ n · m) (sym (constSubstCommSlice (λ k → coHom k A) H* base (+'-comm m n) (b ⌣ a))) ⟩
                         (-^ n · m) (base (m +' n) (b ⌣ a)) ∎



-----------------------------------------------------------------------------
-- Equivalence of Type implies equivalence of Cohomology Ring

module CohomologyRing-Equiv
  {X : Type ℓ}
  {Y : Type ℓ'}
  (e : Iso X Y)
  where

  open IsGroupHom

  open RingStr (snd (H*R X)) using ()
    renaming
    ( 0r        to 0H*X
    ; 1r        to 1H*X
    ; _+_       to _+H*X_
    ; -_        to -H*X_
    ; _·_       to _cupX_
    ; +Assoc    to +H*XAssoc
    ; +Identity to +H*XIdentity
    ; +Lid      to +H*XLid
    ; +Rid      to +H*XRid
    ; +Inv      to +H*XInv
    ; +Linv     to +H*XLinv
    ; +Rinv     to +H*XRinv
    ; +Comm     to +H*XComm
    ; ·Assoc    to ·H*XAssoc
    ; ·Identity to ·H*XIdentity
    ; ·Lid      to ·H*XLid
    ; ·Rid      to ·H*XRid
    ; ·Rdist+   to ·H*XRdist+
    ; ·Ldist+   to ·H*XLdist+
    ; is-set    to isSetH*X     )

  open RingStr (snd (H*R Y)) using ()
    renaming
    ( 0r        to 0H*Y
    ; 1r        to 1H*Y
    ; _+_       to _+H*Y_
    ; -_        to -H*Y_
    ; _·_       to _cupY_
    ; +Assoc    to +H*YAssoc
    ; +Identity to +H*YIdentity
    ; +Lid      to +H*YLid
    ; +Rid      to +H*YRid
    ; +Inv      to +H*YInv
    ; +Linv     to +H*YLinv
    ; +Rinv     to +H*YRinv
    ; +Comm     to +H*YComm
    ; ·Assoc    to ·H*YAssoc
    ; ·Identity to ·H*YIdentity
    ; ·Lid      to ·H*YLid
    ; ·Rid      to ·H*YRid
    ; ·Rdist+   to ·H*YRdist+
    ; ·Ldist+   to ·H*YLdist+
    ; is-set    to isSetH*Y     )


  coHomGr-Iso : {n : ℕ} → GroupIso (coHomGr n X) (coHomGr n Y)
  fst (coHomGr-Iso {n}) = is
    where
    is : Iso (coHom n X) (coHom n Y)
    fun is = ST.rec squash₂ (λ f → ∣ (λ y → f (inv e y)) ∣₂)
    inv is = ST.rec squash₂ (λ g → ∣ (λ x → g (fun e x)) ∣₂)
    rightInv is = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (λ f → cong ∣_∣₂ (funExt (λ y → cong f (rightInv e y))))
    leftInv is = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (λ g → cong ∣_∣₂ (funExt (λ x → cong g (leftInv e x))))
  snd (coHomGr-Iso {n}) = makeIsGroupHom
                                        (ST.elim (λ _ → isProp→isSet λ u v i y → squash₂ _ _ (u y) (v y) i)
                                        (λ f → ST.elim (λ _ → isProp→isSet (squash₂ _ _))
                                        (λ f' → refl)))

  H*-X→H*-Y : H* X → H* Y
  H*-X→H*-Y = DS-Rec-Set.f _ _ _ _ isSetH*Y
               0H*Y
               (λ n a → base n (fun (fst coHomGr-Iso) a))
               _+H*Y_
               +H*YAssoc
               +H*YRid
               +H*YComm
               (λ n → cong (base n) (pres1 (snd coHomGr-Iso)) ∙ base-neutral n)
               λ n a b → base-add _ _ _ ∙ cong (base n) (sym (pres· (snd coHomGr-Iso) a b))

  H*-Y→H*-X : H* Y → H* X
  H*-Y→H*-X = DS-Rec-Set.f _ _ _ _ isSetH*X
               0H*X
               (λ m a → base m (inv (fst coHomGr-Iso) a))
               _+H*X_
               +H*XAssoc
               +H*XRid
               +H*XComm
               (λ m → cong (base m) (pres1 (snd (invGroupIso coHomGr-Iso))) ∙ base-neutral m)
               λ m a b → base-add _ _ _ ∙ cong (base m) (sym (pres· (snd (invGroupIso coHomGr-Iso)) a b))

  e-sect : (y : H* Y) → H*-X→H*-Y (H*-Y→H*-X y) ≡ y
  e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*Y _ _)
           refl
           (λ m a → cong (base m) (rightInv (fst coHomGr-Iso) a))
           (λ {U V} ind-U ind-V → cong₂ _+H*Y_ ind-U ind-V)

  e-retr : (x : H* X) → H*-Y→H*-X (H*-X→H*-Y x) ≡ x
  e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*X _ _)
           refl
           (λ n a → cong (base n) (leftInv (fst coHomGr-Iso) a))
           (λ {U V} ind-U ind-V → cong₂ _+H*X_ ind-U ind-V)

  H*-X→H*-Y-pres1 : H*-X→H*-Y 1H*X ≡ 1H*Y
  H*-X→H*-Y-pres1 = refl

  H*-X→H*-Y-pres+ : (x x' : H* X) → H*-X→H*-Y (x +H*X x') ≡ H*-X→H*-Y x +H*Y H*-X→H*-Y x'
  H*-X→H*-Y-pres+ x x' = refl

  H*-X→H*-Y-pres· : (x x' : H* X) → H*-X→H*-Y (x cupX x') ≡ H*-X→H*-Y x cupY H*-X→H*-Y x'
  H*-X→H*-Y-pres· = DS-Ind-Prop.f _ _ _ _ (λ x u v i y → isSetH*Y _ _ (u y) (v y) i)
         (λ _ → refl)
         (λ n → ST.elim (λ x → isProp→isSet λ u v i y → isSetH*Y _ _ (u y) (v y) i)
                (λ f → DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH*Y _ _)
                        refl
                        (λ m → ST.elim (λ _ → isProp→isSet (isSetH*Y _ _))
                                (λ g → refl))
                        λ {U V} ind-U ind-V → cong₂ _+H*Y_ ind-U ind-V) )
         (λ {U V} ind-U ind-V y → cong₂ _+H*Y_ (ind-U y) (ind-V y))


module _
  {X : Type ℓ}
  {Y : Type ℓ'}
  (e : Iso X Y)
  where

  open CohomologyRing-Equiv e

  CohomologyRing-Equiv : RingEquiv (H*R X) (H*R Y)
  fst CohomologyRing-Equiv = isoToEquiv is
    where
    is : Iso (H* X) (H* Y)
    fun is = H*-X→H*-Y
    inv is = H*-Y→H*-X
    rightInv is = e-sect
    leftInv is = e-retr
  snd CohomologyRing-Equiv = makeIsRingHom H*-X→H*-Y-pres1 H*-X→H*-Y-pres+ H*-X→H*-Y-pres·
