{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Unit where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int hiding (_+_ ; +-comm)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Data.Unit
open import Cubical.Structures.Group

-- H⁰(Unit)
H⁰-Unit≅ℤ' : GroupIso (coHomGr 0 Unit) intGroup
GroupHom.fun (GroupIso.map H⁰-Unit≅ℤ') = sRec isSetInt (λ f → f tt)
GroupHom.isHom (GroupIso.map H⁰-Unit≅ℤ') = sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ a b → addLemma (a tt) (b tt)
GroupIso.inv H⁰-Unit≅ℤ' a = ∣ (λ _ → a) ∣₂
GroupIso.rightInv H⁰-Unit≅ℤ' _ = refl
GroupIso.leftInv H⁰-Unit≅ℤ' = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _) λ a → refl

H⁰-Unit≅ℤ : GroupEquiv (coHomGr 0 Unit) intGroup
H⁰-Unit≅ℤ = GrIsoToGrEquiv H⁰-Unit≅ℤ'

{- Hⁿ(Unit) for n ≥ 1 -}
isContrHⁿ-Unit : (n : ℕ) → isContr (coHom (suc n) Unit)
isContrHⁿ-Unit n = subst isContr (λ i → ∥ UnitToTypeId (coHomK (suc n)) (~ i) ∥₂) (helper' n)
  where
  helper' : (n : ℕ) → isContr (∥ coHomK (suc n) ∥₂)
  helper' n =
    subst isContr
      ((isoToPath (truncOfTruncIso {A = S₊ (1 + n)} 2 (1 + n)))
         ∙∙ sym propTrunc≡Trunc2
         ∙∙ λ i → ∥ hLevelTrunc (suc (+-comm n 2 i)) (S₊ (1 + n)) ∥₂)
      (isConnectedSubtr 2 (helper2 n .fst)
        (subst (λ x → isConnected x (S₊ (suc n))) (sym (helper2 n .snd)) (sphereConnected (suc n))) )
    where
    helper2 : (n : ℕ) → Σ[ m ∈ ℕ ] m + 2  ≡ 2 + n
    helper2 zero = 0 , refl
    helper2 (suc n) = (suc n) , λ i → suc (+-comm n 2 i)

Hⁿ-Unit≅0' : (n : ℕ) → GroupIso (coHomGr (suc n) Unit) trivialGroup
GroupHom.fun (GroupIso.map (Hⁿ-Unit≅0' n)) _ = _
GroupHom.isHom (GroupIso.map (Hⁿ-Unit≅0' n)) _ _ = refl
GroupIso.inv (Hⁿ-Unit≅0' n) _ = 0ₕ
GroupIso.rightInv (Hⁿ-Unit≅0' n) _ = refl
GroupIso.leftInv (Hⁿ-Unit≅0' n) _ = isOfHLevelSuc 0 (isContrHⁿ-Unit n) _ _

Hⁿ-Unit≅0 : (n : ℕ) → GroupEquiv (coHomGr (suc n) Unit) trivialGroup
Hⁿ-Unit≅0 n = GrIsoToGrEquiv (Hⁿ-Unit≅0' n)

{- Hⁿ for arbitrary contractible types -}
private
  Hⁿ-contrTypeIso : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
                   → Iso (coHom (suc n) A) (coHom (suc n) Unit)
  Hⁿ-contrTypeIso n contr = compIso (setTruncIso (ContrToTypeIso contr))
                                    (setTruncIso (invIso (ContrToTypeIso isContrUnit)))

Hⁿ-contrType≅0' : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
              → GroupIso (coHomGr (suc n) A) trivialGroup
GroupHom.fun (GroupIso.map (Hⁿ-contrType≅0' _ _)) _ = _
GroupHom.isHom (GroupIso.map (Hⁿ-contrType≅0' _ _)) _ _ = refl
GroupIso.inv (Hⁿ-contrType≅0' _ _) _ = 0ₕ
GroupIso.rightInv (Hⁿ-contrType≅0' _ _) _ = refl
GroupIso.leftInv (Hⁿ-contrType≅0' {A = A} n contr) _ = isOfHLevelSuc 0 helper _ _
  where
  helper : isContr (coHom (suc n) A)
  helper = (Iso.inv (Hⁿ-contrTypeIso n contr) 0ₕ)
          , λ y →  cong (Iso.inv (Hⁿ-contrTypeIso n contr)) (isOfHLevelSuc 0 (isContrHⁿ-Unit n) 0ₕ (Iso.fun (Hⁿ-contrTypeIso n contr) y))
                  ∙ Iso.leftInv (Hⁿ-contrTypeIso n contr) y

Hⁿ-contrType≅0 : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A
              → GroupEquiv (coHomGr (suc n) A) trivialGroup
Hⁿ-contrType≅0 n contr = GrIsoToGrEquiv (Hⁿ-contrType≅0' n contr)

-- open import Cubical.Data.Bool
-- open import Cubical.Data.Sigma
-- open import Cubical.Foundations.GroupoidLaws
-- test : ∀ {ℓ} {A : Type ℓ} (a : A) → Iso (Unit → A) (Σ[ f ∈ (Bool → A) ] f true ≡ a)
-- Iso.fun (test {A = A} a) x = fhel , refl
--   module _ where
--   fhel : Bool → A
--   fhel false = x _
--   fhel true = a
-- Iso.inv (test a) (f , id) _ = f false
-- Iso.rightInv (test a) (f , id) = λ i → (funExt helper i) , λ j → id ((~ i) ∨ j)
--   where
--   helper : (x : Bool) → fhel a (λ _ → f false) x ≡ f x 
--   helper false = refl
--   helper true = sym id
-- Iso.leftInv (test a) x = refl

-- test2 : Iso (Susp Unit) Unit
-- Iso.fun test2 _ = _
-- Iso.inv test2 _ = north
-- Iso.rightInv test2 a = refl
-- Iso.leftInv test2 north = refl
-- Iso.leftInv test2 south = merid tt
-- Iso.leftInv test2 (merid tt i) j = merid tt (i ∧ j)


-- -- open import Cubical.Foundations.Pointed
-- -- test3 : ∀ {ℓ} {A : Type ℓ} (a : A) → Iso (a ≡ a) ((Σ[ f ∈ (Unit → A) ] f tt ≡ a))
-- -- Iso.fun (test3 a) p = (λ _ → a) , p
-- -- Iso.inv (test3 a) (f , id) = refl
-- -- Iso.rightInv (test3 a) = {!!}
-- -- Iso.leftInv (test3 a) x = {!!}

-- -- open import Cubical.HITs.S1
-- -- test4 : {A : Type₀} (a : A) → Iso ((S¹ , base) →∙ (A , a)) (a ≡ a)
-- -- Iso.fun (test4 a) (f , id) = sym id ∙∙ (cong f loop) ∙∙ id
-- -- Iso.inv (test4 a) p = (λ {base → a ; (loop i) → p i}) , refl
-- -- Iso.rightInv (test4 a) b = sym (doubleCompPath-filler refl b refl)
-- -- Iso.leftInv (test4 a) (f , id) i = (funExt helper i) , λ j → id (~ i ∨ j)
-- --   where
-- --   helper : (x : S¹) → fst (Iso.inv (test4 a) (Iso.fun (test4 a) (f , id))) x ≡ f x
-- --   helper base = sym id
-- --   helper (loop i) j = doubleCompPath-filler (sym id) (cong f loop) (id) (~ j) i


-- -- test5 : {A B : Type₀} (a : A) (b : B) → Iso ((Susp A , north) →∙ (B , b)) ((A , a) →∙ ((b ≡ b) , refl))
-- -- Iso.fun (test5 a b) (f , p) = (λ a' → sym p ∙∙ cong f ((merid a') ∙ sym (merid a)) ∙∙ p) , {!!}
-- -- Iso.inv (test5 {A = A} {B = B} a b) (f , p) = helper , refl
-- --   where
-- --   helper : Susp A → B
-- --   helper north = b
-- --   helper south = b
-- --   helper (merid x i) = f x i
-- -- Iso.rightInv (test5 a b) (f , p) = {!!}
-- -- Iso.leftInv (test5 a b) = {!!}


-- -- open import Cubical.Foundations.Equiv
-- -- open import Cubical.Homotopy.Connected
-- -- H⁰-connected : ∀ {ℓ} {A : Type ℓ} (a : A) → isConnected 2 A → Iso (coHom 0 A) Int
-- -- Iso.fun (H⁰-connected a con) = sRec isSetInt λ f → f a
-- -- Iso.inv (H⁰-connected a con) b = ∣ (λ x → b) ∣₂
-- -- Iso.rightInv (H⁰-connected a con) b = refl
-- -- Iso.leftInv (H⁰-connected a con) =
-- --   sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --         λ f → cong ∣_∣₂ (funExt (equiv-proof (elim.isEquivPrecompose (λ (x : Unit) → a) 1 (λ x → _ , isSetInt _ _) (isConnectedPoint _ con _)) (λ _ → refl) .fst .fst ))

-- -- open import Cubical.HITs.Truncation renaming (rec to trRec)
-- -- H⁰-connected' : ∀ {ℓ} {A : Type ℓ} (a : A) → isConnected 2 A → Iso (coHom 0 A) Int
-- -- Iso.fun (H⁰-connected' a con) = sRec isSetInt λ f → f a
-- -- Iso.inv (H⁰-connected' a con) b = ∣ (λ x → b) ∣₂
-- -- Iso.rightInv (H⁰-connected' a con) b = refl
-- -- Iso.leftInv (H⁰-connected' a con) =
-- --   sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
-- --         λ f → cong ∣_∣₂ (funExt λ x → trRec (isSetInt _ _) (cong f) (isConnectedPath 1 con a x .fst))
