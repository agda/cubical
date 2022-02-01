{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Homotopy.HopfInvariant.Whitehead where

open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.SuspensionMap
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.HopfInvariant.Base
open import Cubical.Homotopy.Group.Pi4S3.Tricky
open import Cubical.Homotopy.Group.Pi4S3.S3PushoutIso
open import Cubical.Homotopy.Loopspace


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.GradedCommutativity
open import Cubical.ZCohomology.Gysin

open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Unit

open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup ; Unit to UnitGroup)
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Exact

open import Cubical.Relation.Nullary

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation
  renaming (elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation renaming (map to pMap ; rec to pRec)


-- abs (HopfInvariant-π' 0 [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π') ≡ 2


open import Cubical.Homotopy.Whitehead
open import Cubical.HITs.S1
open import Cubical.HITs.Join
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Unit

¬lem : (n m : ℕ) → ¬ suc (n +ℕ m) ≡ m
¬lem n zero = snotz
¬lem n (suc m) p = ¬lem n m (sym (+-suc n m) ∙ cong predℕ p)

H²-genₗ' : coHom 2 (S₊ 2 × S₊ 2)
H²-genₗ' = ∣ (λ x → ∣ fst x ∣) ∣₂

H²-genᵣ' : coHom 2 (S₊ 2 × S₊ 2)
H²-genᵣ' = ∣ (λ x → ∣ snd x ∣) ∣₂

abstract
  H²-genₗabs : coHom 2 (S₊ 2 × S₊ 2)
  H²-genₗabs = H²-genₗ'

  H²-genᵣabs : coHom 2 (S₊ 2 × S₊ 2)
  H²-genᵣabs = H²-genᵣ'

  absInd : ∀ {ℓ} (A : coHom 2 (S₊ 2 × S₊ 2) → coHom 2 (S₊ 2 × S₊ 2) → Type ℓ)
           → A H²-genₗabs H²-genᵣabs
           → A H²-genₗ' H²-genᵣ'
  absInd A p = p

  absInd⁻ : ∀ {ℓ} (A : coHom 2 (S₊ 2 × S₊ 2) → coHom 2 (S₊ 2 × S₊ 2) → Type ℓ)
           → A H²-genₗ' H²-genᵣ'
           → A H²-genₗabs H²-genᵣabs
  absInd⁻ A p = p


∨map = joinTo⋁ {A = S₊∙ 1} {B = S₊∙ 1}
module mv = MV ((S₊∙ 2) ⋁ (S₊∙ 2)) Unit (join S¹ S¹) ∨map (λ _ → tt)

downFun : (n m : ℕ)
  → (S₊ (suc (suc n)) → S₊ (suc m) → coHomK (suc (suc ((suc n) +ℕ m))))
  → S₊ (suc n) → S₊ (suc m) → coHomK (suc (suc (n +ℕ m)))
downFun n m f x y =
  ΩKn+1→Kn ((suc ((suc n) +ℕ m)))
    (sym (rCancelₖ _ (f north y))
    ∙∙ cong (λ x → f x y -ₖ f north y) (merid x ∙ sym (merid (ptSn (suc n))))
    ∙∙ rCancelₖ _ (f north y))

upFun : (n m : ℕ)
  → (S₊ (suc n) → S₊ (suc m) → coHomK (suc (suc (n +ℕ m))))
  → (S₊ (suc (suc n)) → S₊ (suc m) → coHomK (suc (suc ((suc n) +ℕ m))))
upFun n m f north y = 0ₖ _
upFun n m f south y = 0ₖ _
upFun n m f (merid a i) y =
  Kn→ΩKn+1 _ (f a y) i

funLem : (n m : ℕ) → (f : S₊ (suc m) → coHomK (suc n))
       → ¬ (n ≡ m)
       → ∥ f ≡ (λ _ → 0ₖ (suc n)) ∥
funLem n m f p =
  Iso.fun PathIdTrunc₀Iso
    (isContr→isProp
      (isOfHLevelRetractFromIso 0 (fst (Hⁿ-Sᵐ≅0 n m p)) isContrUnit)
        ∣ f ∣₂ (0ₕ _))

upDownIso : (n m : ℕ)
  → GroupIso (coHomGr (suc (((suc n) +ℕ m)))
                  (S₊ (suc n) × S₊ (suc m)))
              (coHomGr (suc (suc ((suc n) +ℕ m)))
                  (S₊ (suc (suc n)) × S₊ (suc m)))
Iso.fun (fst (upDownIso n m)) = sMap (uncurry ∘ upFun n m ∘ curry)
Iso.inv (fst (upDownIso n m)) = sMap ((uncurry ∘ downFun n m ∘ curry))
Iso.rightInv (fst (upDownIso n m)) =
  sElim (λ _ → isSetPathImplicit)
    λ f → Iso.inv PathIdTrunc₀Iso
      (pRec squash
        (uncurry (λ g p
          → pMap (λ gid → funExt λ {(x , y)
         → (λ i → uncurry (upFun n m (curry (uncurry (downFun n m (curry (p (~ i))))))) (x , y))
                ∙∙ main g gid x y
                ∙∙ funExt⁻ p (x , y)})
                   (gIdLem g)))
        (rewr f))
  where
  lem : (n m : ℕ) → ¬ suc (suc (n +ℕ m)) ≡ m
  lem n zero = snotz
  lem n (suc m) p = lem n m (cong suc (sym (+-suc n m)) ∙ cong predℕ p)

  charac-fun : (S₊ (suc n) → S₊ (suc m) → typ (Ω (coHomK-ptd (suc (suc (suc n +ℕ m))))))
            → S₊ (suc (suc n)) × S₊ (suc m) → coHomK (suc (suc (suc n +ℕ m)))
  charac-fun g (north , y) = 0ₖ _
  charac-fun g (south , y) = 0ₖ _
  charac-fun g (merid c i , y) = g c y i

  rewr : (f : S₊ (suc (suc n)) × S₊ (suc m) → coHomK (suc (suc (suc n +ℕ m))))
       → ∃[ g ∈ (S₊ (suc n) → S₊ (suc m) → typ (Ω (coHomK-ptd (suc (suc (suc n +ℕ m)))))) ]
            charac-fun g ≡ f
  rewr f =
    pMap (λ p → (λ x y → sym (funExt⁻ p y)
                       ∙∙ (λ i → f ((merid x ∙ sym (merid (ptSn (suc n)))) i , y))
                       ∙∙ funExt⁻ p y)
       , funExt λ { (north , y) → sym (funExt⁻ p y)
                  ; (south , y) → sym (funExt⁻ p y)
                                ∙ λ i → f (merid (ptSn (suc n)) i , y)
                  ; (merid a i , y) j →
                    hcomp (λ k → λ { (i = i0) → p (~ j ∧ k) y
                                    ; (i = i1) → compPath-filler'
                                                   (sym (funExt⁻ p y))
                                                   (λ i → f (merid (ptSn (suc n)) i , y)) k j
                                    ; (j = i1) → f (merid a i , y) })
                          (f (compPath-filler (merid a) (sym (merid (ptSn (suc n)))) (~ j) i
                            , y))})
      (funLem _ _ (λ x → f (north , x))
        (lem n m))

  gIdLem : (g : S₊ (suc n) → S₊ (suc m) → typ (Ω (coHomK-ptd (suc (suc (suc n +ℕ m))))))
       → ∥ (g (ptSn _)) ≡ (λ _ → refl) ∥
  gIdLem g =
      Iso.fun PathIdTrunc₀Iso
        (isContr→isProp
          (isOfHLevelRetractFromIso 0
            ((invIso (fst (coHom≅coHomΩ _ (S₊ (suc m))))))
             (0ₕ _ , sElim (λ _ → isProp→isSet (squash₂ _ _))
                 λ f → pRec (squash₂ _ _) (sym ∘ cong ∣_∣₂)
                   (funLem _ _ f (¬lem n m))))
          ∣ g (ptSn (suc n)) ∣₂ ∣ (λ _ → refl) ∣₂)

  main : (g : _) → (g (ptSn _)) ≡ (λ _ → refl)
     → (x : S₊ (suc (suc n))) (y : S₊ (suc m))
    → uncurry
      (upFun n m (curry (uncurry (downFun n m (curry (charac-fun g))))))
      (x , y)
      ≡ charac-fun g (x , y)
  main g gid north y = refl
  main g gid south y = refl
  main g gid (merid a i) y j = help j i
    where
    help : (λ i → uncurry
      (upFun n m (curry (uncurry (downFun n m (curry (charac-fun g))))))
      (merid a i , y)) ≡ g a y
    help = (λ i → Iso.rightInv (Iso-Kn-ΩKn+1 _)
                  ((sym (rCancel≡refl _ i)
           ∙∙ cong-∙ (λ x → rUnitₖ _ (charac-fun g (x , y)) i) (merid a) (sym (merid (ptSn (suc n)))) i
           ∙∙ rCancel≡refl _ i)) i)
        ∙∙ sym (rUnit _)
        ∙∙ (cong (g a y ∙_) (cong sym (funExt⁻ gid y))
          ∙ sym (rUnit (g a y)))
Iso.leftInv (fst (upDownIso n m)) =
  sElim (λ _ → isSetPathImplicit)
        λ f → pRec (squash₂ _ _)
          (λ id
            → cong ∣_∣₂
              (funExt (λ {(x , y) → (λ i → ΩKn+1→Kn _ (sym (rCancel≡refl _ i)
                       ∙∙ ((λ j → rUnitₖ _
                             (upFun n m (curry f)
                               ((merid x ∙ sym (merid (ptSn (suc n)))) j) y) i))
                       ∙∙ rCancel≡refl _ i))
                ∙ (λ i → ΩKn+1→Kn _  (rUnit
                           (cong-∙ (λ r → upFun n m (curry f) r y)
                                (merid x) (sym (merid (ptSn (suc n)))) i) (~ i)))
                ∙ cong (ΩKn+1→Kn _) (cong (Kn→ΩKn+1 _ (f (x , y)) ∙_)
                       (cong sym (cong (Kn→ΩKn+1 _) (funExt⁻ id y) ∙ (Kn→ΩKn+10ₖ _)))
                         ∙ sym (rUnit _))
                ∙ Iso.leftInv (Iso-Kn-ΩKn+1 _) (f (x , y))})))
          (funLem (suc n +ℕ m) m (λ x → f (ptSn _ , x))
            (¬lem n m))
snd (upDownIso n m) =
  makeIsGroupHom (sElim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂
      (funExt λ { (north , y) → refl
                ; (south , y) → refl
                ; (merid a i , y) j
                 → (sym (∙≡+₂ _ (Kn→ΩKn+1 _ (f (a , y))) (Kn→ΩKn+1 _ (g (a , y))))
                   ∙ sym (Kn→ΩKn+1-hom _ (f (a , y)) (g (a , y)))) (~ j) i}))

toBaseIso : (n m : ℕ) → GroupIso (coHomGr (suc (((suc n) +ℕ m)))
                                  (S₊ (suc n) × S₊ (suc m)))
                                  ((coHomGr (suc (suc m))
                                  (S₊ (suc zero) × S₊ (suc m))))
toBaseIso zero m = idGroupIso
toBaseIso (suc n) m =
  compGroupIso (invGroupIso (upDownIso n m)) (toBaseIso n m)

BaseIso→ : (m : ℕ)
  → (S₊ (suc m) → coHomK (suc m))
  → S₊ (suc zero) → S₊ (suc m) → coHomK (suc (suc m))
BaseIso→ m f base y = 0ₖ _
BaseIso→ m f (loop i) y = Kn→ΩKn+1 (suc m) (f y) i

BaseIso← : (m : ℕ)
  → (S₊ (suc zero) → S₊ (suc m) → coHomK (suc (suc m)))
  → (S₊ (suc m) → coHomK (suc m))
BaseIso← m f x =
  ΩKn+1→Kn (suc m)
    (sym (rCancelₖ _ (f base x)) ∙∙ ((λ i → f (loop i) x -ₖ f base x)) ∙∙ rCancelₖ _ (f base x))

BaseIso : (m : ℕ) → GroupIso (coHomGr (suc m) (S₊ (suc m)))
                              ((coHomGr (suc (suc m))
                                (S₊ (suc zero) × S₊ (suc m))))

Iso.fun (fst (BaseIso m)) = sMap (uncurry ∘ BaseIso→ m)
Iso.inv (fst (BaseIso m)) = sMap (BaseIso← m ∘ curry)
Iso.rightInv (fst (BaseIso m)) =
  sElim (λ _ → isSetPathImplicit)
    λ f → Iso.inv PathIdTrunc₀Iso
      (pMap (uncurry (λ g p
        → funExt λ {(x , y)
          → (λ i → uncurry (BaseIso→ m (BaseIso← m (curry (p i)))) (x , y))
          ∙∙ main g x y
          ∙∙ sym (funExt⁻ p (x , y))}))
        (ss f))
  where
  characFun : (x : S₊ (suc m) → coHomK (suc m))
           → S₊ 1 × S₊ (suc m) → coHomK (suc (suc m))
  characFun f (base , y) = 0ₖ _
  characFun f (loop i , y) = Kn→ΩKn+1 _ (f y) i

  main : (g : _) → (x : S¹) (y : S₊ (suc m)) → uncurry (BaseIso→ m (BaseIso← m (curry (characFun g))))
      (x , y)
      ≡ characFun g (x , y)
  main g base y = refl
  main g (loop i) y j = help j i
    where
    help : cong (λ x → BaseIso→ m (BaseIso← m (curry (characFun g))) x y) loop
         ≡ Kn→ΩKn+1 _ (g y)
    help = Iso.rightInv (Iso-Kn-ΩKn+1 (suc m))
             (sym (rCancelₖ _ (0ₖ _)) ∙∙ ((λ i → Kn→ΩKn+1 _ (g y) i -ₖ 0ₖ _)) ∙∙ rCancelₖ _ (0ₖ _))
        ∙∙ (λ i → sym (rCancel≡refl _ i) ∙∙ (λ j → rUnitₖ _ (Kn→ΩKn+1 _ (g y) j) i) ∙∙ rCancel≡refl _ i)
        ∙∙ sym (rUnit _)

  lem : (m : ℕ) → ¬ suc m ≡ m
  lem zero = snotz
  lem (suc m) p = lem m (cong predℕ p)

  ss : (f : S₊ 1 × S₊ (suc m) → coHomK (suc (suc m)))
     → ∃[ g ∈ (S₊ (suc m) → coHomK (suc m)) ] f ≡ characFun g
  ss f =
    pMap (λ p → (λ x → ΩKn+1→Kn _ (sym (funExt⁻ p x) ∙∙ (λ i → f (loop i , x)) ∙∙ funExt⁻ p x))
              , funExt λ { (base , y) → funExt⁻ p y
                         ; (loop i , x) j →
                           hcomp (λ k → λ {(i = i0) → funExt⁻ p x j
                                          ; (i = i1) → funExt⁻ p x j
                                          ; (j = i0) → f (loop i , x)
                                          ; (j = i1) →
                                              Iso.rightInv (Iso-Kn-ΩKn+1 (suc m))
                                                (sym (funExt⁻ p x) ∙∙ (λ i → f (loop i , x)) ∙∙ funExt⁻ p x) (~ k) i})
                                  (doubleCompPath-filler
                                    (sym (funExt⁻ p x)) (λ i → f (loop i , x)) (funExt⁻ p x) j i)})
     (funLem (suc m) m (λ x → f (base , x)) (lem m))
Iso.leftInv (fst (BaseIso m)) =
  sElim (λ _ → isSetPathImplicit)
    λ f
      → cong ∣_∣₂ (funExt λ x
        → cong (ΩKn+1→Kn (suc m))
               ((λ i → sym (rCancel≡refl _ i)
                 ∙∙ cong (λ z → rUnitₖ _ (BaseIso→ m f z x) i) loop
                 ∙∙ rCancel≡refl _ i) ∙ sym (rUnit (Kn→ΩKn+1 (suc m) (f x))))
        ∙ Iso.leftInv (Iso-Kn-ΩKn+1 _) (f x))
snd (BaseIso m) =
  makeIsGroupHom
    (sElim2
      (λ _ _ → isSetPathImplicit)
      λ f g → cong ∣_∣₂
        (funExt λ { (base , y) → refl
                  ; (loop i , y) j →
                          (sym (∙≡+₂ _ (Kn→ΩKn+1 _ (f y)) (Kn→ΩKn+1 _ (g y)))
                         ∙ sym (Kn→ΩKn+1-hom _ (f y) (g y))) (~ j) i}))

GroupIso2 : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → GroupIso (×coHomGr (suc n) A Unit) (coHomGr (suc n) A)
Iso.fun (fst (GroupIso2 n)) = fst
Iso.inv (fst (GroupIso2 n)) x = x , 0ₕ (suc n)
Iso.rightInv (fst (GroupIso2 n)) _ = refl
Iso.leftInv (fst (GroupIso2 n)) x =
  ΣPathP (refl , isContr→isProp (isContrHⁿ-Unit n) (0ₕ (suc n)) (snd x))
snd (GroupIso2 n) = makeIsGroupHom λ _ _ → refl

theIso : GroupIso (coHomGr 2 (S₊ 2)) (coHomGr 4 (S₊ 2 × S₊ 2))
theIso = (compGroupIso (BaseIso 1) (upDownIso 0 1))

Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ : (n m : ℕ)
  → GroupIso (coHomGr ((suc n) +' (suc m))
                  (S₊ (suc n) × S₊ (suc m)))
              ℤGroup
Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ zero m =
  compGroupIso (invGroupIso (BaseIso m)) (Hⁿ-Sⁿ≅ℤ m)
Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ (suc n) m =
  compGroupIso
          (invGroupIso (upDownIso n m))
            (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ n m)


theIso⌣ : Iso.fun (fst (theIso)) ∣ ∣_∣ₕ ∣₂ ≡ H²-genₗ' ⌣ H²-genᵣ'
theIso⌣ =
  cong ∣_∣₂ (funExt (uncurry
    (λ { north y → refl
       ; south y → refl
       ; (merid a i) y j → Kn→ΩKn+1 3 (lem₃ a y j) i})))
  where
  lem₃ : (a : S¹) (y : S₊ 2) → BaseIso→ 1 ∣_∣ₕ a y ≡ _⌣ₖ_ {n = 1} {m = 2} ∣ a ∣ₕ ∣ y ∣ₕ
  lem₃ base y = refl
  lem₃ (loop i) y = refl

abstract
  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs : (n m : ℕ)
    → GroupIso (coHomGr ((suc n) +' (suc m))
                    (S₊ (suc n) × S₊ (suc m)))
                ℤGroup
  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs = Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ

  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs≡ : (n m : ℕ) → Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs n m ≡ Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ n m
  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs≡ n m = refl

  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-⌣ : Iso.fun (fst (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1)) (H²-genₗ' ⌣ H²-genᵣ') ≡ 1
  Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-⌣ =
      cong (Iso.fun (fst (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1))) (sym theIso⌣)
    ∙ speedUp ∣_∣ₕ
    ∙ refl -- Computation! :-)
    where
    speedUp : (f : _) → Iso.fun (fst (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1)) (Iso.fun (fst (theIso)) ∣ f ∣₂)
                       ≡ Iso.fun (fst (Hⁿ-Sⁿ≅ℤ 1)) ∣ f ∣₂
    speedUp f i = (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ 1))) (Iso.leftInv (fst theIso) ∣ f ∣₂ i)



open import Cubical.Data.Sum renaming (rec to ⊎rec)
open Iso


Pushout≅Torus2 : GroupIso (coHomGr 2 (S₊ 2 × S₊ 2)) (coHomGr 2 (Pushout joinTo⋁ (λ _ → tt)))
Pushout≅Torus2 = coHomIso 2 (invIso (Iso-Susp×Susp-cofibJoinTo⋁ S¹ S¹ base base))

GroupHom2 :
  GroupHom (coHomGr 2 (Pushout ∨map (λ _ → tt)))
           (×coHomGr 2 (S₊∙ 2 ⋁ S₊∙ 2) Unit)
GroupHom2 = mv.i 2

GroupEquiv2 : GroupEquiv
               (coHomGr 2 (Pushout ∨map (λ _ → tt)))
               (×coHomGr 2 (S₊∙ 2 ⋁ S₊∙ 2) Unit)
fst (fst GroupEquiv2) = fst GroupHom2
snd (fst GroupEquiv2) =
  SES→isEquiv
    (isContr→≡UnitGroup
      (isOfHLevelRetractFromIso 0
        (compIso (coHomIso 1 (invIso (IsoSphereJoin 1 1)) .fst)
          (fst (Hⁿ-Sᵐ≅0 0 2 λ p → snotz (sym p))))
        isContrUnit))
    ((isContr→≡UnitGroup
      (isOfHLevelRetractFromIso 0
        (compIso (coHomIso 2 (invIso (IsoSphereJoin 1 1)) .fst)
          (fst (Hⁿ-Sᵐ≅0 1 2 λ p → snotz (cong predℕ (sym p)))))
        isContrUnit)))
    (mv.d 1) (mv.i 2)
    (mv.Δ 2)
    (mv.Ker-i⊂Im-d 1)
    (mv.Ker-Δ⊂Im-i 2)
snd GroupEquiv2 = snd GroupHom2

coHom2S²×S² : GroupIso (coHomGr 2 (S₊ 2 × S₊ 2)) (DirProd ℤGroup ℤGroup)
coHom2S²×S² =
  compGroupIso Pushout≅Torus2
    (compGroupIso
      (GroupEquiv→GroupIso GroupEquiv2)
      (compGroupIso (GroupIso2 1)
        (compGroupIso (Hⁿ-⋁ (S₊∙ 2) (S₊∙ 2) 1)
          (GroupIsoDirProd (Hⁿ-Sⁿ≅ℤ 1) (Hⁿ-Sⁿ≅ℤ 1)))))

zz : GroupIso (coHomGr 4 (S₊ 2 × S₊ 2)) (coHomGr 4 (Pushout joinTo⋁ (λ _ → tt)))
zz = coHomIso 4 (invIso (Iso-Susp×Susp-cofibJoinTo⋁ S¹ S¹ base base))

GroupEquiv1 : GroupEquiv
               (coHomGr 3 (join S¹ S¹))
               (coHomGr 4 (Pushout ∨map (λ _ → tt)))
fst (fst GroupEquiv1) = fst (mv.d 3)
snd (fst GroupEquiv1) = ss
  where
  abstract
    ss : isEquiv (fst (mv.d 3))
    ss = SES→isEquiv
          (isContr→≡UnitGroup
            (isOfHLevelΣ 0
              (isOfHLevelRetractFromIso 0
                (compIso
                  (fst (Hⁿ-⋁ (S₊∙ 2) (S₊∙ 2) 2))
                  (compIso
                    (prodIso (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p)))
                             (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p))))
                    lUnit×Iso))
                isContrUnit)
              (λ _ → isContrHⁿ-Unit 2)))
          (isContr→≡UnitGroup
            (isOfHLevelΣ 0
              (isOfHLevelRetractFromIso 0
                (compIso
                  (fst (Hⁿ-⋁ (S₊∙ 2) (S₊∙ 2) 3))
                  (compIso
                    (prodIso (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p)))
                             (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))))
                    lUnit×Iso))
                isContrUnit)
              λ _ → isContrHⁿ-Unit 3))
          (mv.Δ 3)
          (mv.d 3)
          (mv.i 4)
          (mv.Ker-d⊂Im-Δ 3)
          (mv.Ker-i⊂Im-d 3)
snd GroupEquiv1 = snd (mv.d 3)


coHom4S²×S² : GroupIso (coHomGr 4 (S₊ 2 × S₊ 2)) ℤGroup
coHom4S²×S² =
  compGroupIso zz
   (compGroupIso
     (invGroupIso (GroupEquiv→GroupIso GroupEquiv1))
     (compGroupIso
       (coHomIso 3 (invIso (IsoSphereJoin 1 1)))
       (Hⁿ-Sⁿ≅ℤ 2)))


CHopf : Type
CHopf = HopfInvariantPush 0 fold∘W

Hopfαfold∘W = Hopfα 0 (fold∘W , refl)
Hopfβfold∘W = Hopfβ 0 (fold∘W , refl)

lem₂ : Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁ ≃ fst thePushout∙
lem₂ = compEquiv
        (compEquiv pushoutSwitchEquiv
          (isoToEquiv (PushoutDistr.PushoutDistrIso fold⋁ W λ _ → tt)))
        pushoutSwitchEquiv

lem₁ : Pushout W (λ _ → tt) ≃ cofibW S¹ S¹ base base
lem₁ = pushoutEquiv W (λ _ → tt) joinTo⋁ (λ _ → tt)
         (isoToEquiv (invIso (IsoSphereJoin 1 1)))
         (idEquiv _)
         (idEquiv _)
         refl
         refl

lem : Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁
    ≃ fst (Pushout⋁↪fold⋁∙ (S₊∙ 2))
lem = pushoutEquiv inl _ ⋁↪ fold⋁
        (idEquiv _)
        (compEquiv lem₁ (isoToEquiv (invIso (Iso-Susp×Susp-cofibJoinTo⋁ S¹ S¹ base base))))
        (idEquiv _)
        (Susp×Susp→cofibW≡ S¹ S¹ base base)
        refl

lem∙ : (Pushout {B = (Pushout W (λ _ → tt))} inl fold⋁ , inr north)
     ≃∙ (Pushout⋁↪fold⋁∙ (S₊∙ 2))
fst lem∙ = lem
snd lem∙ = sym (push (inl north))


CHopfIso : Iso CHopf (Pushout⋁↪fold⋁ (S₊∙ 2))
CHopfIso =
  compIso (invIso (equivToIso
    (compEquiv (compEquiv pushoutSwitchEquiv
      (isoToEquiv (PushoutDistr.PushoutDistrIso fold⋁ W λ _ → tt)))
          pushoutSwitchEquiv)))
          (equivToIso lem)



S²×S² : Pointed₀
fst S²×S² = S₊ 2 × S₊ 2
snd S²×S² = north , north

q : (S²×S² →∙ (Pushout⋁↪fold⋁ (S₊∙ 2) , inl (north , north)))
fst q = inl
snd q = refl

qHom : GroupHom (coHomGr 4 (Pushout⋁↪fold⋁ (S₊∙ 2)))
                (coHomGr 4 (S₊ 2 × S₊ 2))
qHom = coHomMorph 4 (fst q)

qHomGen : (n : ℕ) →
       GroupHom (coHomGr n (Pushout⋁↪fold⋁ (S₊∙ 2)))
                (coHomGr n (S₊ 2 × S₊ 2))
qHomGen = λ n → coHomMorph n (fst q)

module mv2 = MV _ _ (S₊∙ 2 ⋁ S₊∙ 2) ⋁↪ fold⋁

gaha : isEquiv (fst (mv2.i 4))
gaha =
  SES→isEquiv
    (isContr→≡UnitGroup
      (isOfHLevelRetractFromIso 0
        (compIso
          (fst (Hⁿ-⋁ (S₊∙ 2) (S₊∙ 2) 2))
          (compIso
            (prodIso (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p)))
                     (fst (Hⁿ-Sᵐ≅0 2 1 λ p → snotz (cong predℕ p))))
            rUnit×Iso))
        isContrUnit))
    ((isContr→≡UnitGroup
      (isOfHLevelRetractFromIso 0
        (compIso
          (fst (Hⁿ-⋁ (S₊∙ 2) (S₊∙ 2) 3))
          (compIso
            (prodIso (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p)))
                     (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))))
            rUnit×Iso))
        isContrUnit)))
    (mv2.d 3)
    (mv2.i 4)
    (mv2.Δ 4)
    (mv2.Ker-i⊂Im-d 3)
    (mv2.Ker-Δ⊂Im-i 4)

qHomPP : {A B C : Type}
       → Unit ≡ C
       → (f : A → B × C)
       → isEquiv f
       → isEquiv (fst ∘ f)
qHomPP {A = A} {B = B} =
  J (λ C _ → (f : A → B × C) → isEquiv f → isEquiv (fst ∘ f))
    λ f eq → record { equiv-proof =
      λ b → ((fst (fst (equiv-proof eq (b , tt))))
        , cong fst (fst (equiv-proof eq (b , tt)) .snd))
        , λ y → ΣPathP ((cong fst (equiv-proof eq (b , tt) .snd ((fst y)
          , ΣPathP ((snd y) , refl))))
          , λ i j → equiv-proof eq (b , tt) .snd ((fst y)
          , ΣPathP ((snd y) , refl)) i .snd j .fst) }


isEquiv-qHom : GroupEquiv (coHomGr 4 (Pushout⋁↪fold⋁ (S₊∙ 2)))
                (coHomGr 4 (S₊ 2 × S₊ 2))
fst (fst isEquiv-qHom) = qHom .fst
snd (fst isEquiv-qHom) =
  subst isEquiv
    (funExt (sElim (λ _ → isSetPathImplicit) (λ _ → refl)))
    (qHomPP (isoToPath
      (invIso (fst (Hⁿ-Sᵐ≅0 3 1 λ p → snotz (cong predℕ p))))) _ gaha)
snd isEquiv-qHom = qHom .snd

coHomCHopfIso : (n : ℕ)
  → GroupIso (coHomGr n CHopf) (coHomGr n (Pushout⋁↪fold⋁ (S₊∙ 2)))
coHomCHopfIso n = invGroupIso (coHomIso n CHopfIso)

H⁴-gen = Iso.inv (fst coHom4S²×S²) 1
H²-genₗ = Iso.inv (fst coHom2S²×S²) (1 , 0)
H²-genᵣ = Iso.inv (fst coHom2S²×S²) (0 , 1)



open import Cubical.ZCohomology.RingStructure.RingLaws

module postul (is : GroupIso (coHomGr 4 (S₊ 2 × S₊ 2)) ℤGroup)
              (isEq : (fun (fst is) (H²-genₗ' ⌣ H²-genᵣ') ≡ 1)) where
  α' : coHom 2 (Pushout⋁↪fold⋁ (S₊∙ 2))
  α' = fun (fst (coHomCHopfIso 2)) Hopfαfold∘W

  β' : coHom 4 (Pushout⋁↪fold⋁ (S₊∙ 2))
  β' = fun (fst (coHomCHopfIso 4)) Hopfβfold∘W

  ⌣→≡ : (α' ⌣ α' ≡ β' +ₕ β') ⊎ (α' ⌣ α' ≡ -ₕ (β' +ₕ β'))
    → (Hopfαfold∘W ⌣ Hopfαfold∘W ≡ Hopfβfold∘W +ₕ Hopfβfold∘W)
    ⊎ (Hopfαfold∘W ⌣ Hopfαfold∘W ≡ -ₕ (Hopfβfold∘W +ₕ Hopfβfold∘W))
  ⌣→≡ (inl x) = inl ((λ i → leftInv (fst (coHomCHopfIso 2)) Hopfαfold∘W (~ i)
                            ⌣ leftInv (fst (coHomCHopfIso 2)) Hopfαfold∘W (~ i))
                    ∙∙ cong (inv (fst (coHomCHopfIso 4))) x
                    ∙∙ leftInv (fst (coHomCHopfIso 4)) (Hopfβfold∘W +ₕ Hopfβfold∘W))
  ⌣→≡ (inr x) = inr ((λ i → leftInv (fst (coHomCHopfIso 2)) Hopfαfold∘W (~ i)
                            ⌣ leftInv (fst (coHomCHopfIso 2)) Hopfαfold∘W (~ i))
                   ∙∙ cong (inv (fst (coHomCHopfIso 4))) x
                   ∙∙ leftInv (fst (coHomCHopfIso 4))
                        (-ₕ (Hopfβfold∘W +ₕ Hopfβfold∘W)))

  Q : (qHom .fst β' ≡  H²-genₗ' ⌣ H²-genᵣ')
    ⊎ (qHom .fst β' ≡  -ₕ (H²-genₗ' ⌣ H²-genᵣ'))
  Q =
    ⊎rec
      (λ p → inl (sym (leftInv (fst is) (qHom .fst β'))
                ∙∙ cong (inv (fst is)) (p ∙ sym isEq)
                ∙∙ leftInv (fst is) (H²-genₗ' ⌣ H²-genᵣ')))
      (λ p → inr (sym (leftInv (fst is) (qHom .fst β'))
               ∙∙ cong (inv (fst is))
                    (p ∙ sym (cong (GroupStr.inv (snd ℤGroup)) isEq))
               ∙∙ (IsGroupHom.presinv (invGroupIso is .snd) (fun (fst is) (H²-genₗ' ⌣ H²-genᵣ'))
                 ∙ cong -ₕ_ (leftInv (fst is) (H²-genₗ' ⌣ H²-genᵣ')))))
      p2
    where
    h : GroupEquiv (coHomGr 4 (HopfInvariantPush 0 fold∘W)) ℤGroup
    h = compGroupEquiv (GroupIso→GroupEquiv (coHomCHopfIso 4))
          (compGroupEquiv
            isEquiv-qHom
            (GroupIso→GroupEquiv is))

    p2 : (fst (fst h) Hopfβfold∘W ≡ 1) ⊎ (fst (fst h) Hopfβfold∘W ≡ -1)
    p2 = groupEquivPresGen _ (GroupIso→GroupEquiv (Hopfβ-Iso 0 (fold∘W , refl)))
          Hopfβfold∘W (inl (Hopfβ↦1 0 (fold∘W , refl))) h

  qpres⌣ : (x y : coHom 2 _)
    → fst qHom (x ⌣ y) ≡ fst (qHomGen 2) x ⌣ fst (qHomGen 2) y
  qpres⌣ = sElim2 (λ _ _ → isSetPathImplicit) λ _ _ → refl

-- H¹(...) → H²(S² ∨ S²) → H²(S² × S²) × H²(S²) → H²(...)

  i* : coHom 2 (Pushout⋁↪fold⋁ (S₊∙ 2)) → coHom 2 (S₊ 2)
  i* = coHomFun 2 inr

  kata : i* (coHomFun 2 (Iso.inv CHopfIso) Hopfαfold∘W) ≡ ∣ ∣_∣ ∣₂
  kata = refl

  incl∘q : fst q ∘ (λ x → x , north) ≡ inr
  incl∘q = funExt λ x → (push (inl x))

  incr∘q :  fst q ∘ (λ x → north , x) ≡ inr
  incr∘q = funExt λ x → (push (inr x))

  q≡' : coHomFun 2 (λ x → x , north) ∘ fst (qHomGen 2) ≡ i*
  q≡' = funExt (sElim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → cong f (push (inl x))))

  kzz : (x : _) → i* x ≡ ∣ ∣_∣ ∣₂ → fst (qHomGen 2) x
     ≡ ∣ (λ x → ∣ fst x ∣) ∣₂
    +ₕ ∣ (λ x → ∣ snd x ∣) ∣₂
  kzz = sElim (λ _ → isSetΠ λ _ → isSetPathImplicit)
    λ f p → Cubical.HITs.PropositionalTruncation.rec
      (squash₂ _ _)
      (λ r → cong ∣_∣₂ (funExt (uncurry
        (wedgeconFun 1 1 (λ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _)
          (λ x → cong f (push (inr x)) ∙∙ funExt⁻ r x ∙∙ refl)
          ((λ x → cong f (push (inl x)) ∙∙ funExt⁻ r x ∙∙ sym (rUnitₖ 2 ∣ x ∣ₕ)))
          (cong (_∙∙ funExt⁻ r north ∙∙ refl)
            (cong (cong f) λ j i → push (push tt j) i))))))
      (Iso.fun PathIdTrunc₀Iso p)


  q≡'2 : coHomFun 2 (λ x → north , x) ∘ fst (qHomGen 2) ≡ i*
  q≡'2 = funExt (sElim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → cong f (push (inr x))))

  q₂ : fst (qHomGen 2) α'
    ≡ ∣ (λ x → ∣ fst x ∣) ∣₂ +ₕ ∣ (λ x → ∣ snd x ∣) ∣₂
  q₂ = kzz ((coHomFun 2 (Iso.inv CHopfIso) Hopfαfold∘W)) refl

  q₂' : fst (qHomGen 2) α' ≡ H²-genₗ' +ₕ H²-genᵣ'
  q₂' = q₂

  triv⌣ : (a : S¹) → cong₂ (_⌣ₖ_ {n = 2} {m = 2}) (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (merid a)) ≡ λ _ → ∣ north ∣ₕ
  triv⌣ a = cong₂Funct (_⌣ₖ_ {n = 2} {m = 2}) (cong ∣_∣ₕ (merid a)) (cong ∣_∣ₕ (merid a))
      ∙ sym (rUnit λ j → _⌣ₖ_ {n = 2} {m = 2} ∣ merid a j ∣ₕ ∣ north ∣)
      ∙ (λ i j → ⌣ₖ-0ₖ 2 2 ∣ merid a j ∣ₕ i)

  distLem : (x : coHom 4 (S₊ 2 × S₊ 2)) → -ₕ ((-ₕ x) +ₕ (-ₕ x)) ≡ x +ₕ x
  distLem =
    sElim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂ (funExt λ x → cong -ₖ_ (sym (-distrₖ 4 (f x) (f x)))
                     ∙ -ₖ^2  (f x +ₖ f x))

  MainId : ((fst qHom) (α' ⌣ α') ≡ qHom .fst (β' +ₕ β'))
         ⊎ ((fst qHom) (α' ⌣ α') ≡ qHom .fst (-ₕ (β' +ₕ β')))
  MainId =
    ⊎rec
      (λ id → inl (h ∙ H
                  ∙ cong (λ x → x +ₕ x) (sym id)
                  ∙ sym (IsGroupHom.pres· (snd qHom) β' β')))
      (λ id → inr (h ∙ H
                 ∙ ((sym (distLem (x ⌣ y))
                 ∙ cong -ₕ_ (cong (λ x → x +ₕ x) (sym id)))
                 ∙ cong (-ₕ_) (IsGroupHom.pres· (snd qHom) β' β'))
                 ∙ sym (IsGroupHom.presinv (snd qHom) (β' +ₕ β'))))
      Q
    where
    H²-genₗ⌣H²-genₗ : H²-genₗ' ⌣ H²-genₗ' ≡ 0ₕ 4
    H²-genₗ⌣H²-genₗ =
      cong ∣_∣₂
        (funExt (uncurry λ { north y → refl
                           ; south y → refl
                           ; (merid a i) y j → triv⌣ a j i}))

    H²-genᵣ⌣H²-genᵣ : H²-genᵣ' ⌣ H²-genᵣ' ≡ 0ₕ 4
    H²-genᵣ⌣H²-genᵣ = cong ∣_∣₂
        (funExt (uncurry λ { x north → refl
                           ; x south → refl
                           ; x (merid a i) j → triv⌣ a j i}))

    x = H²-genₗ'
    y = H²-genᵣ'

    -ₕId : (x : coHom 4 (S₊ 2 × S₊ 2)) → (-ₕ^ 2 · 2) x ≡ x
    -ₕId = sElim (λ _ → isSetPathImplicit)
                 λ a → cong ∣_∣₂ (funExt λ x → -ₖ-gen-inl-left 2 2 tt (inl tt) (a x))

    H : (H²-genₗ' +ₕ H²-genᵣ') ⌣ (H²-genₗ' +ₕ H²-genᵣ')
      ≡ (H²-genₗ' ⌣ H²-genᵣ') +ₕ (H²-genₗ' ⌣ H²-genᵣ')
    H = (x +ₕ y) ⌣ (x +ₕ y)                       ≡⟨ leftDistr-⌣ 2 2 (x +ₕ y) x y ⟩
        ((x +ₕ y) ⌣ x) +ₕ ((x +ₕ y) ⌣ y)          ≡⟨ cong₂ _+ₕ_ (rightDistr-⌣ 2 2 x y x) (rightDistr-⌣ 2 2 x y y) ⟩
        ((x ⌣ x +ₕ y ⌣ x)) +ₕ (x ⌣ y +ₕ y ⌣ y)    ≡⟨ cong₂ _+ₕ_ (cong₂ _+ₕ_ H²-genₗ⌣H²-genₗ
                                                                    ((gradedComm-⌣ 2 2 y x)
                                                                    ∙ cong (-ₕ^ 2 · 2)
                                                                    (transportRefl (x ⌣ y))
                                                                    ∙ -ₕId (x ⌣ y))
                                                                    ∙ lUnitₕ 4 (x ⌣ y))
                                                                (cong (x ⌣ y +ₕ_) H²-genᵣ⌣H²-genᵣ ∙ rUnitₕ 4 (x ⌣ y)) ⟩
        ((x ⌣ y) +ₕ (x ⌣ y)) ∎

    h : (fst qHom) (α' ⌣ α') ≡ (H²-genₗ' +ₕ H²-genᵣ') ⌣ (H²-genₗ' +ₕ H²-genᵣ')
    h = (fst qHom) (α' ⌣ α')                        ≡⟨ refl ⟩
        fst (qHomGen 2) α' ⌣ fst (qHomGen 2) α'     ≡⟨ cong (λ x → x ⌣ x) q₂ ⟩
        ((H²-genₗ' +ₕ H²-genᵣ') ⌣ (H²-genₗ' +ₕ H²-genᵣ')) ∎

  HopfInvariantLem : (HopfInvariant 0 (fold∘W , refl) ≡ 2)
                  ⊎ (HopfInvariant 0 (fold∘W , refl) ≡ -2)
  HopfInvariantLem =
    ⊎rec (λ p → inl (p1
                   ∙ cong (Iso.fun (fst (Hopfβ-Iso 0 (fold∘W , refl)))) p
                   ∙ IsGroupHom.pres· (Hopfβ-Iso 0 (fold∘W , refl) .snd) Hopfβfold∘W Hopfβfold∘W
                   ∙ cong (λ x → x + x) (Hopfβ↦1 0 (fold∘W , refl))))
         (λ p → inr (p1
                   ∙ cong (Iso.fun (fst (Hopfβ-Iso 0 (fold∘W , refl)))) p
                   ∙ IsGroupHom.presinv (Hopfβ-Iso 0 (fold∘W , refl) .snd) (Hopfβfold∘W +ₕ Hopfβfold∘W)
                   ∙ cong (GroupStr.inv (snd ℤGroup))
                          (IsGroupHom.pres· (Hopfβ-Iso 0 (fold∘W , refl) .snd) Hopfβfold∘W Hopfβfold∘W
                         ∙ cong (λ x → x + x) (Hopfβ↦1 0 (fold∘W , refl)))))
         p2
    where
    p1 : HopfInvariant 0 (fold∘W , refl)
       ≡ Iso.fun (fst (Hopfβ-Iso 0 (fold∘W , refl))) (Hopfαfold∘W ⌣ Hopfαfold∘W)
    p1 = cong (Iso.fun (fst (Hopfβ-Iso 0 (fold∘W , refl)))) (transportRefl (Hopfαfold∘W ⌣ Hopfαfold∘W))

    p2 : (Hopfαfold∘W ⌣ Hopfαfold∘W ≡ Hopfβfold∘W +ₕ Hopfβfold∘W)
      ⊎ (Hopfαfold∘W ⌣ Hopfαfold∘W ≡ -ₕ (Hopfβfold∘W +ₕ Hopfβfold∘W))
    p2 = ⌣→≡ (⊎rec (λ p → inl (sym (retEq (fst isEquiv-qHom) (α' ⌣ α'))
                              ∙∙ cong (invEq (fst isEquiv-qHom)) p
                              ∙∙ retEq (fst isEquiv-qHom) (β' +ₕ β')))
                    (λ p → inr ((sym (retEq (fst isEquiv-qHom) (α' ⌣ α'))
                              ∙∙ cong (invEq (fst isEquiv-qHom)) p
                              ∙∙ retEq (fst isEquiv-qHom) (-ₕ (β' +ₕ β')))))
                    MainId)

HopfInvariantLemfold∘W : abs (HopfInvariant 0 (fold∘W , refl)) ≡ 2
HopfInvariantLemfold∘W =
  ⊎→abs (HopfInvariant 0 (fold∘W , refl)) 2
    (postul.HopfInvariantLem
      (Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-abs 1 1) Hⁿ⁺ᵐ-Sⁿ×Sᵐ≅ℤ-⌣)

Whitehead≡ : [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π' ≡ ∣ fold∘W , refl ∣₂
Whitehead≡ =
    cong ∣_∣₂ ([]≡[]₂ (idfun∙ (S₊∙ 2)) (idfun∙ (S₊∙ 2)) )
  ∙ sym Fold∘W
  ∙ cong ∣_∣₂ (∘∙-idˡ (fold∘W , refl))

HopfInvariantWhitehead :
  abs (HopfInvariant-π' 0 [ ∣ idfun∙ (S₊∙ 2) ∣₂ ∣ ∣ idfun∙ (S₊∙ 2) ∣₂ ]π') ≡ 2
HopfInvariantWhitehead =
  cong abs (cong (HopfInvariant-π' 0) Whitehead≡) ∙ HopfInvariantLemfold∘W
