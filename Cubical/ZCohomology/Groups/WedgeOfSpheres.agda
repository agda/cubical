{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.WedgeOfSpheres where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.Data.Int renaming (_+_ to _ℤ+_) 

open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation renaming (elim to trElim) hiding (map ; elim2)
open import Cubical.Algebra.Group
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim)

S¹⋁S¹ : Type₀
S¹⋁S¹ = S₊∙ 1 ⋁ S₊∙ 1

S²⋁S¹⋁S¹ : Type₀
S²⋁S¹⋁S¹ = S₊∙ 2 ⋁ (S¹⋁S¹ , inl base)

------------- H⁰(S¹⋁S¹) ------------
H⁰-S¹⋁S¹ : GroupIso (coHomGr 0 S¹⋁S¹) intGroup
H⁰-S¹⋁S¹ = H⁰-connected (inl base) (wedgeConnected _ _ (Sn-connected 0) (Sn-connected 0))

------------- H¹(S¹⋁S¹) ------------
H¹-S¹⋁S¹ : GroupIso (coHomGr 1 S¹⋁S¹) (dirProd intGroup intGroup)
H¹-S¹⋁S¹ =  (Hⁿ-⋁ _ _ 0) □ dirProdGroupIso coHom1S1≃ℤ coHom1S1≃ℤ

------------- H⁰(S²⋁S¹⋁S¹) ---------
H⁰-S²⋁S¹⋁S¹ : GroupIso (coHomGr 0 S²⋁S¹⋁S¹) intGroup
H⁰-S²⋁S¹⋁S¹ = H⁰-connected (inl north)
                  (wedgeConnected _ _
                    (Sn-connected 1)
                    (wedgeConnected _ _
                      (Sn-connected 0)
                      (Sn-connected 0)))

------------- H¹(S²⋁S¹⋁S¹) ---------
H¹-S²⋁S¹⋁S¹ : GroupIso (coHomGr 1 S²⋁S¹⋁S¹) (dirProd intGroup intGroup)
H¹-S²⋁S¹⋁S¹ =
    Hⁿ-⋁ (S₊∙ 2) (S¹⋁S¹ , inl base) 0
  □ dirProdGroupIso (H¹-Sⁿ≅0 0) H¹-S¹⋁S¹
  □ lUnitGroupIso

------------- H²(S²⋁S¹⋁S¹) ---------

H²-S²⋁S¹⋁S¹ : GroupIso (coHomGr 2 S²⋁S¹⋁S¹) intGroup
H²-S²⋁S¹⋁S¹ =
  compGroupIso
  (Hⁿ-⋁ _ _ 1)
  (dirProdGroupIso {B = trivialGroup}
    (Hⁿ-Sⁿ≅ℤ 1)
    ((Hⁿ-⋁ _ _ 1)  □ dirProdGroupIso (Hⁿ-S¹≅0 0) (Hⁿ-S¹≅0 0) □ rUnitGroupIso)
  □ rUnitGroupIso)

private
  open import Cubical.Data.Int
  open import Cubical.Foundations.Equiv
  open import Cubical.Data.Sigma
  to₂ : coHom 2 S²⋁S¹⋁S¹ → Int
  to₂ = GroupHom.fun (GroupIso.map H²-S²⋁S¹⋁S¹)
  from₂ : Int → coHom 2 S²⋁S¹⋁S¹
  from₂ = GroupIso.inv H²-S²⋁S¹⋁S¹

  to₁ : coHom 1 S²⋁S¹⋁S¹ → Int × Int
  to₁ = GroupHom.fun (GroupIso.map H¹-S²⋁S¹⋁S¹)
  from₁ : Int × Int → coHom 1 S²⋁S¹⋁S¹
  from₁ = GroupIso.inv H¹-S²⋁S¹⋁S¹

  to₀ : coHom 0 S²⋁S¹⋁S¹ → Int
  to₀ = GroupHom.fun (GroupIso.map H⁰-S²⋁S¹⋁S¹)
  from₀ : Int → coHom 0 S²⋁S¹⋁S¹
  from₀ = GroupIso.inv H⁰-S²⋁S¹⋁S¹

-- test2 : to₂ (from₂ 0) ≡ 0
-- test2 = refl

{-

-- Computes (a lot slower than for the torus)
test : to₁ (from₁ (1 , 0) +ₕ from₁ (0 , 1)) ≡ (1 , 1)
test = refl

-- Does not compute:
test2 : to₂ (from₂ 0) ≡ 0
test2 = refl
-}

-- open import Cubical.HITs.KleinBottle
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Data.Sigma
-- IsoHelp : Iso (KleinBottle → coHomK 1) (Σ[ x ∈ coHomK 1 ] (Σ[ p ∈ x ≡ x ] (Σ[ q ∈ x ≡ x ] PathP (λ i → p (~ i) ≡ p i) q q)))
-- Iso.fun IsoHelp f = (f point) , ((cong f line1) , (cong f line2) , λ i j → f (square i j))
-- Iso.inv IsoHelp (p , l1 , l2 , sq) point = p
-- Iso.inv IsoHelp (p , l1 , l2 , sq) (line1 i) = l1 i
-- Iso.inv IsoHelp (p , l1 , l2 , sq) (line2 i) = l2 i
-- Iso.inv IsoHelp (p , l1 , l2 , sq) (square i i₁) = sq i i₁
-- Iso.rightInv IsoHelp f = refl
-- Iso.leftInv IsoHelp f = funExt λ {point → refl ; (line1 i) → refl ; (line2 i) → refl ; (square i j) → refl }

-- IsoHelp2 : Iso (Σ[ x ∈ coHomK 2 ] (Σ[ p ∈ x ≡ x ] (Σ[ q ∈ x ≡ x ] PathP (λ i → p (~ i) ≡ p i) q q))) {!!}
-- IsoHelp2 = {!!}


-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Path
-- isoHelp2 : Iso (Σ[ x ∈ coHomK 1 ] (Σ[ p ∈ x ≡ x ] (Σ[ q ∈ x ≡ x ] PathP (λ i → p (~ i) ≡ p i) q q))) (Σ[ x ∈ coHomK 1 ] (x ≡ x))
-- Iso.fun isoHelp2 (x , p , q , r) = x , q
-- Iso.inv isoHelp2 (x , p) = x , refl , p , refl
-- Iso.rightInv isoHelp2 (x , p) = refl
-- Iso.leftInv isoHelp2 (x , p , q , r) =
--   ΣPathP (refl , ΣPathP (tihi , subst (λ x → x) (sym (PathP≡Path _ _ _)) (Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isOfHLevelTrunc 3 _ _) _ _) (transportRefl q))))
--   where
--   tihi : refl ≡ p
--   tihi = {!!} -- {!!} ∙ {!!} cong (rUnitₖ 3) {!!} ∙ {!!} 
--   open import Cubical.Data.Nat renaming (_+_ to _ℕ+_ ; +-comm to ℕ+-comm) hiding (+-assoc)
--   open import Cubical.Foundations.GroupoidLaws
--   open import Cubical.Data.Empty renaming (elim to ⊥-elim)
--   open import Cubical.ZCohomology.KcompPrelims
  
--   helper : (x : S¹) → (p : Path (coHomK 1) ∣ x ∣ ∣ x ∣) → p ≡ sym p → p ≡ refl
--   helper = toPropElim (λ _ → isPropΠ2 λ _ _ → isOfHLevelTrunc 3 _ _ _ _)
--                       λ p pId → sym (Iso.rightInv (Iso-Kn-ΩKn+1 0) p)
--                               ∙∙ cong (Iso.fun (Iso-Kn-ΩKn+1 0)) (test (Iso.inv (Iso-Kn-ΩKn+1 0) p) (cong (Iso.inv (Iso-Kn-ΩKn+1 0) p ℤ+_) (cong (Iso.inv (Iso-Kn-ΩKn+1 0)) pId ∙ helper2 0 p) ∙∙ {!!} ∙∙ {!!})) -- cong (Iso.fun (Iso-Kn-ΩKn+1 0)) (cong (Iso.inv (Iso-Kn-ΩKn+1 0)) pId)
--                               ∙∙ sym (rUnit refl)
--     where
--     open GroupStr renaming (_-_ to _G-_)
--     helper2 : (n : ℕ) (p : _) → Iso.inv (Iso-Kn-ΩKn+1 n) (sym p) ≡ -[ n ]ₖ Iso.inv (Iso-Kn-ΩKn+1 n) p
--     helper2 n p = {!!}
--     test : (x : Int) → x ℤ+ x ≡ 0 → x ≡ 0
--     test (pos zero) p = refl
--     test (pos (suc n)) p = ⊥-elim {A = λ _ → (pos (suc n)) ≡ 0}
--                                   (znots (sym (injPos (sym (help n) ∙ p))))
--       where
--       help : (n : ℕ) → sucInt (pos (suc n) +pos n) ≡ sucInt (pos (suc n ℕ+ n))
--       help zero = refl
--       help (suc n) = cong (λ x → sucInt (sucInt x)) (sym (sucInt+pos n (pos (suc n))))
--                   ∙∙ cong (λ x → sucInt (sucInt x)) (help n)
--                   ∙∙ cong (λ x → pos (3 ℕ+ x)) (sym (+-suc n n))
--     test (negsuc n) p = ⊥-elim {A = λ _ → negsuc n ≡ pos 0}
--                                (negsucNotpos _ _ (sym (minusPlus (pos (suc n)) (negsuc n))
--                                                ∙∙ cong (_- negsuc n) p
--                                                ∙∙ sym (cong sucInt (pos0+ (pos n)))))



-- open import Cubical.Data.Bool
-- open import Cubical.Algebra.Monoid
-- open import Cubical.Algebra.Semigroup
-- BoolGr : Group₀
-- fst BoolGr = Bool
-- GroupStr.0g (snd BoolGr) = true
-- (snd BoolGr GroupStr.+ false) false = true
-- (snd BoolGr GroupStr.+ false) true = false
-- (snd BoolGr GroupStr.+ true) y = y
-- (GroupStr.- snd BoolGr) x = x
-- IsSemigroup.is-set (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) = isSetBool
-- IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) false false false = refl
-- IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) false false true = refl
-- IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) false true false = refl
-- IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) false true true = refl
-- IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) true false false = refl
-- IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) true false true = refl
-- IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) true true false = refl
-- IsSemigroup.assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr)))) true true true = refl
-- IsMonoid.identity (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr))) false = refl , refl
-- IsMonoid.identity (IsGroup.isMonoid (GroupStr.isGroup (snd BoolGr))) true = refl , refl
-- IsGroup.inverse (GroupStr.isGroup (snd BoolGr)) false = refl , refl
-- IsGroup.inverse (GroupStr.isGroup (snd BoolGr)) true = refl , refl


-- data Disk {ℓ} : Type ℓ where
--   left : Disk
--   right : Disk
--   lid : left ≡ right
--   bot : left ≡ right
--   idemp : bot ≡ lid

-- PathP→∙∙ : ∀ {ℓ} {A : Type ℓ} {x : A} → ((p q : x ≡ x ) → p ∙ q ≡ q ∙ p) → (p q : x ≡ x) →
--   Iso (PathP (λ i → q (~ i) ≡ q i) p p) (PathP (λ i → x ≡ p i) p refl)
-- Iso.fun (PathP→∙∙ comm p q) x i = {!!}
-- Iso.inv (PathP→∙∙ comm p q) = {!!}
-- Iso.rightInv (PathP→∙∙ comm p q) = {!!}
-- Iso.leftInv (PathP→∙∙ comm p q) = {!!}

-- test : Iso (KleinBottle → coHomK 2) {!K!}
-- Iso.fun test = {!!}
-- Iso.inv test = {!!}
-- Iso.rightInv test = {!!}
-- Iso.leftInv test = {!!}

-- open import Cubical.Homotopy.Connected
-- test3 : ∀ {ℓ} {B : coHom 2 KleinBottle → Type ℓ}
--        → ((p : _) → isProp (B p))
--        → {!!}
--        → (p : _) → B p
-- test3 = {!!}

-- test2 : ∀ (p : coHom 2 KleinBottle) → p +ₕ p ≡ 0ₕ 2
-- test2 =
--   coHomPointedElim
--     1 point (λ _ → setTruncIsSet _ _)
--       λ f fId → rec {!!} (λ l1Id → rec {!!}
--         (λ l2Id → cong ∣_∣₂ (funExt λ {point → cong₂ _+ₖ_ fId fId
--                                     ; (line1 i) j → {!!}
--                                     ; (line2 i) j → {!!}
--                                     ; (square i j) k → {!!}}))
--         ((Iso.fun (PathIdTruncIso _) (isContr→isProp (isConnectedPathKn 1 (f point) (f point)) ∣ cong f line2 ∣  ∣ refl ∣))))
--         (Iso.fun (PathIdTruncIso _) (isContr→isProp (isConnectedPathKn 1 (f point) (f point)) ∣ cong f line1 ∣  ∣ refl ∣))

-- mikmok : (p : Path (Path (coHomK 2) ∣ north ∣ ∣ north ∣) refl refl) → ∥ (KleinBottle → coHomK 2) ∥₂ 
-- mikmok p = ∣ (λ {point → ∣ north ∣ ; (line1 i) → ∣ north ∣ ; (line2 i) → ∣ north ∣ ; (square i j) → p i j}) ∣₂

-- l-loop : Path S¹⋁S¹ (inl base) (inr base)
-- l-loop = cong inl loop ∙ push tt

-- r-loop : Path S¹⋁S¹ (inr base) (inl base)
-- r-loop = cong inr loop ∙ sym (push tt)

-- open import Cubical.HITs.Pushout
-- Test : Iso KleinBottle (Pushout {A = S¹} {B = S¹⋁S¹} {C = S¹}
--                        (λ {base → inl base
--                         ; (loop i) → (l-loop ∙ r-loop) i})
--                         λ x → x)
-- Iso.fun Test point = inl (inl base)
-- Iso.fun Test (line1 i) = inl (inl (loop i))
-- Iso.fun Test (line2 i) = inl ((push tt ∙ r-loop) i)
-- Iso.fun Test (square i j) = {!!}
-- Iso.inv Test (inl x) = {!!}
-- Iso.inv Test (inr x) = {!!}
-- Iso.inv Test (push a i) = {!!}
-- Iso.rightInv Test = {!!}
-- Iso.leftInv Test = {!!}
