{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Groups.Wedge where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.S1.S1
open import Cubical.HITs.S1
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.NatMinusTwo.Base
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₋₁ ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; +-comm to +ℤ-comm ; +-assoc to +ℤ-assoc)
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; recElim to trRec ; rec to trRec2 ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Freudenthal
open import Cubical.HITs.SmashProduct.Base
open import Cubical.Data.Unit
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso ; invIso to invGrIso ; idIso to idGrIso)
open import Cubical.Data.Group.GroupLibrary
open import Cubical.ZCohomology.coHomZero-map
open import Cubical.HITs.Wedge

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Torus

open import Cubical.ZCohomology.KcompPrelims


open import Cubical.HITs.Pushout
open import Cubical.Data.Sum.Base
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Bool hiding (_⊕_)

private
  variable
    ℓ : Level
    A B : Pointed ℓ


private
  Δ : (n : ℕ) → morph (×coHomGr n (typ A) (typ B)) (coHomGr n Unit)
  Δ {A = A} {B = B} = MV.Δ (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B)
  d : (n : ℕ) → morph (coHomGr n Unit) (coHomGr (suc n) (A ⋁ B))
  d {A = A} {B = B} = MV.d (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B)
  i : (n : ℕ) → morph (coHomGr n (A ⋁ B)) (×coHomGr n (typ A) (typ B))
  i {A = A} {B = B} = MV.i (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B)

abstract
  anotherhelper : (x : coHom 0 Unit)
                → isInIm (×coHomGr 0 (typ A) (typ B)) (coHomGr 0 Unit) (Δ {A = A} {B = B} 0) x
  anotherhelper =
    sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
          λ f → ∣ (∣ (λ _ → f tt) ∣₀ , 0ₕ) , cong ∣_∣₀ (funExt (λ _ → cong ((f tt) +ₖ_) -0ₖ ∙ rUnitₖ (f tt))) ∣₋₁

  athirdhelper : (x : coHom 0 Unit)
               → isInKer (coHomGr 0 Unit) (coHomGr 1 _) (d {A = A} {B = B} 0) x
  athirdhelper {A = A} {B = B} x = MV.Im-Δ⊂Ker-d (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 0 x
                   (anotherhelper x)

  afourthhelper : (x : coHom 1 (A ⋁ B)) → isInIm (coHomGr 0 Unit) (coHomGr 1 _) (d {A = A} {B = B} 0) x
                → x ≡ 0ₕ
  afourthhelper x inim = pRec (setTruncIsSet _ _) (λ p → sym (snd p) ∙ athirdhelper (fst p)) inim

H¹-⋁ : grIso (coHomGr 1 (Pushout (λ _ → snd A) (λ _ → snd B))) (dirProd (coHomGr 1 (typ A)) (coHomGr 1 (typ B)))
H¹-⋁ {A = A} {B = B} =
  Iso''→Iso
    (iso''
      (i 1)
      {!!} -- (λ x ker → afourthhelper x (MV.Ker-i⊂Im-d (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 0 x ker))
      λ x → MV.Ker-Δ⊂Im-i (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 1 x
        (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _))

H¹-⋁' : Iso'' (coHomGr 1 (Pushout {A = Unit} (λ _ → snd A) (λ _ → snd B))) (×coHomGr 1 (typ A) (typ B))
Iso''.ϕ (H¹-⋁' {A = A} {B = B}) = MV.i-n+1 (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 0 -- ? sElim2 (λ _ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _) λ _ _ → refl
Iso''.inj (H¹-⋁' {A = A} {B = B}) x ker = {!!} -- afourthhelper x (MV.Ker-i⊂Im-d (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 0 x ker) -- afourthhelper x (MV.Ker-i⊂Im-d (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 0 x ker)
Iso''.surj (H¹-⋁' {A = A} {B = B}) x = {!MV.Ker-Δ⊂Im-i (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B) 1 x
        (isOfHLevelSuc 0 (isContrHⁿ-Unit 0) _ _)!}
