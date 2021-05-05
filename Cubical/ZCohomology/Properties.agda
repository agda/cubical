{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Properties where

{-
This module contains:
1. direct proofs of connectedness of Kn and ΩKn
2. Induction principles for cohomology groups of pointed types
3. Equivalence between cohomology of A and reduced cohomology of (A + 1)
4. Equivalence between cohomology and reduced cohomology for dimension ≥ 1
5. Encode-decode proof of Kₙ ≃ ΩKₙ₊₁ and proofs that this equivalence
   and its inverse are morphisms
6. A proof of coHomGr ≅ coHomGrΩ
7. A locked (non-reducing) version of Kₙ ≃ ΩKₙ₊₁
-}


open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure

open import Cubical.HITs.S1 hiding (encode ; decode ; _·_)
open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2 ; setTruncIsSet to §)
open import Cubical.Data.Int renaming (_+_ to _ℤ+_ ; _·_ to _ℤ∙_ ; +-comm to +ℤ-comm ; ·-comm to ∙-comm) hiding (-_)
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; map2 to trMap2; rec to trRec ; elim3 to trElim3)
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.Group hiding (Unit ; Int)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.Sum.Base hiding (map)
open import Cubical.Functions.Morphism
open import Cubical.Data.Sigma

open Iso renaming (inv to inv')

private
  variable
    ℓ ℓ' : Level

------------------- Connectedness ---------------------
is2ConnectedKn : (n : ℕ) → isConnected 2 (coHomK (suc n))
is2ConnectedKn zero = ∣ ∣ base ∣ ∣
                    , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                        (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 (isOfHLevelTrunc 2)) _ _)
                          (toPropElim (λ _ → isOfHLevelTrunc 2 _ _) refl))
is2ConnectedKn (suc n) = ∣ ∣ north ∣ ∣
                       , trElim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
                           (trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isOfHLevelTrunc 2 _ _))
                             (suspToPropElim (ptSn (suc n)) (λ _ → isOfHLevelTrunc 2 _ _) refl))

isConnectedKn : (n : ℕ) → isConnected (2 + n) (coHomK (suc n))
isConnectedKn n = isOfHLevelRetractFromIso 0 (invIso (truncOfTruncIso (2 + n) 1)) (sphereConnected (suc n))

-- direct proof of connectedness of ΩKₙ₊₁ not relying on the equivalence ∥ a ≡ b ∥ₙ ≃ (∣ a ∣ₙ₊₁ ≡ ∣ b ∣ₙ₊₁)
isConnectedPathKn : (n : ℕ) (x y : (coHomK (suc n))) → isConnected (suc n) (x ≡ y)
isConnectedPathKn n =
  trElim (λ _ → isProp→isOfHLevelSuc (2 + n) (isPropΠ λ _ → isPropIsContr))
    (sphereElim _ (λ _ → isProp→isOfHLevelSuc n (isPropΠ λ _ → isPropIsContr))
      λ y → isContrRetractOfConstFun
               {B = (hLevelTrunc (suc n) (ptSn (suc n) ≡ ptSn (suc n)))} ∣ refl ∣
                 (fun⁻ n y
                , trElim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
                         (J (λ y p → fun⁻ n y _ ≡ _) (funExt⁻ (fun⁻Id n) ∣ refl ∣))))
  where
  fun⁻ : (n : ℕ) → (y : coHomK (suc n)) →
         hLevelTrunc (suc n) (ptSn (suc n) ≡ ptSn (suc n))
      → hLevelTrunc (suc n) (∣ ptSn (suc n) ∣ ≡ y)
  fun⁻ n =
    trElim (λ _ → isOfHLevelΠ (3 + n) λ _ → isOfHLevelSuc (2 + n) (isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n))))
      (sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelTrunc (suc n)) λ _ → ∣ refl ∣)

  fun⁻Id : (n : ℕ) → fun⁻ n ∣ ptSn (suc n) ∣ ≡ λ _ → ∣ refl ∣
  fun⁻Id zero = refl
  fun⁻Id (suc n) = refl

-------------------
-- Induction principles for cohomology groups (n ≥ 1)
-- If we want to show a proposition about some x : Hⁿ(A), it suffices to show it under the
-- assumption that x = ∣ f ∣₂ for some f : A → Kₙ and that f is pointed

coHomPointedElim : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom (suc n) A → Type ℓ'}
                 → ((x : coHom (suc n) A) → isProp (B x))
                 → ((f : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → B ∣ f ∣₂)
                 → (x : coHom (suc n) A) → B x
coHomPointedElim {ℓ' = ℓ'} {A = A} n a isprop indp =
  sElim (λ _ → isOfHLevelSuc 1 (isprop _))
         λ f → helper n isprop indp f (f a) refl
  where
  helper :  (n : ℕ) {B : coHom (suc n) A → Type ℓ'}
         → ((x : coHom (suc n) A) → isProp (B x))
         → ((f : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → B ∣ f ∣₂)
         → (f : A → coHomK (suc n))
         → (x : coHomK (suc n))
         → f a ≡ x → B ∣ f ∣₂
  -- pattern matching a bit extra to avoid isOfHLevelPlus'
  helper zero isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 2 (isPropΠ λ _ → isprop _))
           (toPropElim (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc zero) isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 3 (isPropΠ λ _ → isprop _))
           (suspToPropElim base (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc (suc zero)) isprop ind f =
    trElim (λ _ → isOfHLevelPlus {n = 1} 4 (isPropΠ λ _ → isprop _))
           (suspToPropElim north (λ _ → isPropΠ λ _ → isprop _) (ind f))
  helper (suc (suc (suc n))) isprop ind f =
    trElim (λ _ → isOfHLevelPlus' {n = 5 + n} 1 (isPropΠ λ _ → isprop _))
           (suspToPropElim north (λ _ → isPropΠ λ _ → isprop _) (ind f))


coHomPointedElim2 : {A : Type ℓ} (n : ℕ) (a : A) {B : coHom (suc n) A → coHom (suc n) A → Type ℓ'}
                 → ((x y : coHom (suc n) A) → isProp (B x y))
                 → ((f g : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → g a ≡ coHom-pt (suc n) → B ∣ f ∣₂ ∣ g ∣₂)
                 → (x y : coHom (suc n) A) → B x y
coHomPointedElim2 {ℓ' = ℓ'} {A = A} n a isprop indp = sElim2 (λ _ _ → isOfHLevelSuc 1 (isprop _ _))
                                                   λ f g → helper n a isprop indp f g (f a) (g a) refl refl
  where
  helper : (n : ℕ) (a : A) {B : coHom (suc n) A → coHom (suc n) A → Type ℓ'}
                 → ((x y : coHom (suc n) A) → isProp (B x y))
                 → ((f g : A → coHomK (suc n)) → f a ≡ coHom-pt (suc n) → g a ≡ coHom-pt (suc n) → B ∣ f ∣₂ ∣ g ∣₂)
                 → (f g : A → coHomK (suc n))
                 → (x y : coHomK (suc n))
                 → f a ≡ x → g a ≡ y
                 → B ∣ f ∣₂ ∣ g ∣₂
  helper zero a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 2 (isPropΠ2 λ _ _ → isprop _ _))
          (toPropElim2 (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc zero) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 3 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 base (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc (suc zero)) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus {n = 1} 4 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 north (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))
  helper (suc (suc (suc n))) a isprop indp f g =
    elim2 (λ _ _ → isOfHLevelPlus' {n = 5 + n} 1 (isPropΠ2 λ _ _ → isprop _ _))
          (suspToPropElim2 north (λ _ _ → isPropΠ2 λ _ _ → isprop _ _) (indp f g))

coHomK-elim : ∀ {ℓ} (n : ℕ) {B : coHomK (suc n) → Type ℓ}
           → ((x : _) → isOfHLevel (suc n) (B x))
           → B (0ₖ (suc n))
           → (x : _) → B x
coHomK-elim n {B = B } hlev b =
  trElim (λ _ → isOfHLevelPlus {n = (suc n)} 2 (hlev _))
    (sphereElim _ (hlev ∘ ∣_∣) b)

{- Equivalence between cohomology of A and reduced cohomology of (A + 1) -}
coHomRed+1Equiv : (n : ℕ) →
                  (A : Type ℓ) →
                  (coHom n A) ≡ (coHomRed n ((A ⊎ Unit , inr (tt))))
coHomRed+1Equiv zero A i = ∥ helpLemma {C = (Int , pos 0)} i ∥₂
  module coHomRed+1 where
  helpLemma : {C : Pointed ℓ} → ( (A → (typ C)) ≡  ((((A ⊎ Unit) , inr (tt)) →∙ C)))
  helpLemma {C = C} = isoToPath (iso map1
                                     map2
                                     (λ b → linvPf b)
                                     (λ _  → refl))
    where
    map1 : (A → typ C) → ((((A ⊎ Unit) , inr (tt)) →∙ C))
    map1 f = map1' , refl
      module helpmap where
      map1' : A ⊎ Unit → fst C
      map1' (inl x) = f x
      map1' (inr x) = pt C

    map2 : ((((A ⊎ Unit) , inr (tt)) →∙ C)) → (A → typ C)
    map2 (g , pf) x = g (inl x)

    linvPf : (b :((((A ⊎ Unit) , inr (tt)) →∙ C))) →  map1 (map2 b) ≡ b
    linvPf (f , snd) i = (λ x → helper x i)  , λ j → snd ((~ i) ∨ j)
      where
      helper : (x : A ⊎ Unit) → ((helpmap.map1') (map2 (f , snd)) x) ≡ f x
      helper (inl x) = refl
      helper (inr tt) = sym snd
coHomRed+1Equiv (suc zero) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK 1 , ∣ base ∣)} i ∥₂
coHomRed+1Equiv (suc (suc n)) A i = ∥ coHomRed+1.helpLemma A i {C = (coHomK (2 + n) , ∣ north ∣)} i ∥₂

Iso-coHom-coHomRed : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) → Iso (coHomRed (suc n) A) (coHom (suc n) (typ A))
fun (Iso-coHom-coHomRed {A = A , a} n) = map fst
inv' (Iso-coHom-coHomRed {A = A , a} n) = map λ f → (λ x → f x -ₖ f a) , rCancelₖ _ _
rightInv (Iso-coHom-coHomRed {A = A , a} n) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
         λ f → trRec (isProp→isOfHLevelSuc _ (§ _ _))
                      (λ p → cong ∣_∣₂ (funExt λ x → cong (λ y → f x +ₖ y) (cong -ₖ_ p ∙ -0ₖ) ∙ rUnitₖ _ (f x)))
                      (Iso.fun (PathIdTruncIso (suc n)) (isContr→isProp (isConnectedKn n) ∣ f a ∣ ∣ 0ₖ _ ∣))
leftInv (Iso-coHom-coHomRed {A = A , a} n) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ {(f , p) → cong ∣_∣₂ (ΣPathP (((funExt λ x → (cong (λ y → f x -ₖ y) p
                                                    ∙∙ cong (λ y → f x +ₖ y) -0ₖ
                                                    ∙∙ rUnitₖ _ (f x)) ∙ refl))
                              , helper n (f a) (sym p)))}
    where
    path : (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ _ ≡ x) → _
    path n x p = (cong (λ y → x -ₖ y) (sym p) ∙∙ cong (λ y → x +ₖ y) -0ₖ ∙∙ rUnitₖ _ x) ∙ refl

    helper :  (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ _ ≡ x)
            → PathP (λ i → path n x p i ≡ 0ₖ _) (rCancelₖ _ x) (sym p)
    helper zero x =
      J (λ x p → PathP (λ i → path 0 x p i ≡ 0ₖ _)
                        (rCancelₖ _ x) (sym p))
        λ i j → rUnit (rUnit (λ _ → 0ₖ 1) (~ j)) (~ j) i
    helper (suc n) x =
      J (λ x p → PathP (λ i → path (suc n) x p i ≡ 0ₖ _) (rCancelₖ _ x) (sym p))
        λ i j → rCancelₖ (suc (suc n)) (0ₖ (suc (suc n))) (~ i ∧ ~ j)

+∙≡+ : (n : ℕ) {A : Pointed ℓ} (x y : coHomRed (suc n) A)
     → Iso.fun (Iso-coHom-coHomRed n) (x +ₕ∙ y)
      ≡ Iso.fun (Iso-coHom-coHomRed n) x +ₕ Iso.fun (Iso-coHom-coHomRed n) y

+∙≡+ zero = sElim2 (λ _ _ → isOfHLevelPath 2 § _ _) λ _ _ → refl
+∙≡+ (suc n) = sElim2 (λ _ _ → isOfHLevelPath 2 § _ _) λ _ _ → refl

private
  homhelp : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) (x y : coHom (suc n) (typ A))
          → Iso.inv (Iso-coHom-coHomRed {A = A} n) (x +ₕ y)
           ≡ Iso.inv (Iso-coHom-coHomRed n) x +ₕ∙ Iso.inv (Iso-coHom-coHomRed n) y
  homhelp n A = morphLemmas.isMorphInv _+ₕ∙_ _+ₕ_
                (Iso.fun (Iso-coHom-coHomRed n)) (+∙≡+ n) _
                (Iso.rightInv (Iso-coHom-coHomRed n)) (Iso.leftInv (Iso-coHom-coHomRed n))

coHomGr≅coHomRedGr : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ)
                  → GroupEquiv (coHomRedGrDir (suc n) A) (coHomGr (suc n) (typ A))
GroupEquiv.eq (coHomGr≅coHomRedGr n A) = isoToEquiv (Iso-coHom-coHomRed n)
GroupEquiv.isHom (coHomGr≅coHomRedGr n A) = +∙≡+ n

coHomRedGroup : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ) → AbGroup {ℓ}
coHomRedGroup zero A = coHomRedGroupDir zero A
coHomRedGroup (suc n) A =
  InducedAbGroup (coHomGroup (suc n) (typ A))
                 (coHomRed (suc n) A , _+ₕ∙_)
                 (isoToEquiv (invIso (Iso-coHom-coHomRed n)))
                 (homhelp n A)

abstract
  coHomGroup≡coHomRedGroup : ∀ {ℓ} (n : ℕ) (A : Pointed ℓ)
                          → coHomGroup (suc n) (typ A) ≡ coHomRedGroup (suc n) A
  coHomGroup≡coHomRedGroup n A =
    InducedAbGroupPath (coHomGroup (suc n) (typ A))
              (coHomRed (suc n) A , _+ₕ∙_)
              (isoToEquiv (invIso (Iso-coHom-coHomRed n)))
              (homhelp n A)

------------------- Kₙ ≃ ΩKₙ₊₁ ---------------------
-- This proof uses the encode-decode method rather than Freudenthal

-- We define the map σ : Kₙ → ΩKₙ₊₁ and prove that it is a morphism
private
  module _ (n : ℕ) where
  σ : {n : ℕ} → coHomK (suc n) → Path (coHomK (2 + n)) ∣ north ∣ ∣ north ∣
  σ {n = n} = trRec (isOfHLevelTrunc (4 + n) _ _)
                    λ a → cong ∣_∣ (merid a ∙ sym (merid (ptSn (suc n))))

  σ-hom-helper : ∀ {ℓ} {A : Type ℓ} {a : A} (p : a ≡ a) (r : refl ≡ p)
                   → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r
  σ-hom-helper p = J (λ p r → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r) refl

  σ-hom : {n : ℕ} (x y : coHomK (suc n)) → σ (x +ₖ y) ≡ σ x ∙ σ y
  σ-hom {n = zero} =
    elim2 (λ _ _ → isOfHLevelPath 3 (isOfHLevelTrunc 4 _ _) _ _)
          (wedgeconFun _ _
            (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
            (λ x → lUnit _
                  ∙ cong (_∙ σ ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid base)))))
            (λ y → cong σ (rUnitₖ 1 ∣ y ∣)
                 ∙∙ rUnit _
                 ∙∙ cong (σ ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid base)))))
            (sym (σ-hom-helper (σ ∣ base ∣) (cong (cong ∣_∣) (sym (rCancel (merid base)))))))
  σ-hom {n = suc n} =
    elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
          (wedgeconFun _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (wedgeConHLev' n) _ _)
           (λ x → lUnit _
                 ∙ cong (_∙ σ ∣ x ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
           (λ y → cong σ (rUnitₖ (2 + n) ∣ y ∣)
                ∙∙ rUnit _
                ∙∙ cong (σ ∣ y ∣ ∙_) (cong (cong ∣_∣) (sym (rCancel (merid north)))))
           (sym (σ-hom-helper (σ ∣ north ∣) (cong (cong ∣_∣) (sym (rCancel (merid north)))))))

  -- We will need to following lemma
  σ-minusDistr : {n : ℕ} (x y : coHomK (suc n)) → σ (x -ₖ y) ≡ σ x ∙ sym (σ y)
  σ-minusDistr {n = n} =
    morphLemmas.distrMinus'
      _+ₖ_ _∙_
      σ σ-hom ∣ (ptSn (suc n)) ∣ refl
      -ₖ_ sym
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (rUnitₖ (suc n))
      (lCancelₖ (suc n)) rCancel
      (assocₖ (suc n)) assoc∙
       (cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

  -- we define the code using addIso
  Code : (n : ℕ) →  coHomK (2 + n) → Type₀
  Code n x = (trElim {B = λ _ → TypeOfHLevel ℓ-zero (3 + n)} (λ _ → isOfHLevelTypeOfHLevel (3 + n))
                     λ a → Code' a , hLevCode' a) x .fst
    where
    Code' : (S₊ (2 + n)) → Type₀
    Code' north = coHomK (suc n)
    Code' south = coHomK (suc n)
    Code' (merid a i) = isoToPath (addIso (suc n) ∣ a ∣) i

    hLevCode' : (x : S₊ (2 + n)) → isOfHLevel (3 + n) (Code' x)
    hLevCode' = suspToPropElim (ptSn (suc n)) (λ _ → isPropIsOfHLevel (3 + n)) (isOfHLevelTrunc (3 + n))

  symMeridLem : (n : ℕ) → (x : S₊ (suc n)) (y : coHomK (suc n))
                        → subst (Code n) (cong ∣_∣ (sym (merid x))) y ≡ y -ₖ ∣ x ∣
  symMeridLem n x = trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
                            (λ y → cong (_-ₖ ∣ x ∣) (transportRefl ∣ y ∣))

  decode : {n : ℕ} (x : coHomK (2 + n)) → Code n x → ∣ north ∣ ≡ x
  decode {n = n} = trElim (λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
                          decode-elim
    where
    north≡merid : (a : S₊ (suc n))
                → Path (coHomK (2 + n)) ∣ north ∣ ∣ north ∣
                ≡ (Path (coHomK (2 + n)) ∣ north ∣ ∣ south ∣)
    north≡merid a i = Path (coHomK (2 + n)) ∣ north ∣ ∣ merid a i ∣

    decode-elim : (a : S₊ (2 + n)) → Code n ∣ a ∣ → Path (coHomK (2 + n)) ∣ north ∣ ∣ a ∣
    decode-elim north = σ
    decode-elim south = trRec (isOfHLevelTrunc (4 + n) _ _)
                              λ a → cong ∣_∣ (merid a)
    decode-elim (merid a i) =
      hcomp (λ k → λ { (i = i0) → σ
                      ; (i = i1) → mainPath a k})
            (funTypeTransp (Code n) (λ x → ∣ north ∣ ≡ x) (cong ∣_∣ (merid a)) σ i)
      where
      mainPath : (a : (S₊ (suc n))) →
             transport (north≡merid a) ∘ σ ∘ transport (λ i → Code n ∣ merid a (~ i) ∣)
           ≡ trRec (isOfHLevelTrunc (4 + n) _ _) λ a → cong ∣_∣ (merid a)
      mainPath a = funExt (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (4 + n) _ _) _ _)
                                  (λ x → (λ i → transport (north≡merid a) (σ (symMeridLem n a ∣ x ∣ i)))
                                       ∙∙ cong (transport (north≡merid a)) (-distrHelp x)
                                       ∙∙ (substAbove x)))
        where
        -distrHelp : (x : S₊ (suc n)) → σ (∣ x ∣ -ₖ ∣ a ∣) ≡ cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a))
        -distrHelp x =
             σ-minusDistr ∣ x ∣ ∣ a ∣
           ∙ (λ i → (cong ∣_∣ (compPath-filler (merid x) (λ j → merid (ptSn (suc n)) (~ j ∨ i)) (~ i)))
                   ∙ (cong ∣_∣ (sym (compPath-filler (merid a) (λ j → merid (ptSn (suc n)) (~ j ∨ i)) (~ i)))))

        substAbove : (x : S₊ (suc n)) → transport (north≡merid a) (cong ∣_∣ (merid x) ∙ cong ∣_∣ (sym (merid a)))
                   ≡ cong ∣_∣ (merid x)
        substAbove x i = transp (λ j → north≡merid a (i ∨ j)) i
                                (compPath-filler (cong ∣_∣ (merid x)) (λ j → ∣ merid a (~ j ∨ i) ∣) (~ i))

  encode : {n : ℕ} {x : coHomK (2 + n)} → Path (coHomK (2 + n)) ∣ north ∣ x → Code n x
  encode {n = n} p = transport (cong (Code n) p) ∣ (ptSn (suc n)) ∣

  decode-encode : {n : ℕ} {x : coHomK (2 + n)} (p : Path (coHomK (2 + n)) ∣ north ∣ x)
               → decode _ (encode p) ≡ p
  decode-encode {n = n} =
    J (λ y p → decode _ (encode p) ≡ p)
        (cong (decode ∣ north ∣) (transportRefl ∣ ptSn (suc n) ∣)
       ∙ cong (cong ∣_∣) (rCancel (merid (ptSn (suc n)))))

-- We define an addition operation on Code which we can use in order to show that encode is a
-- morphism (in a very loose sense)
  hLevCode : {n : ℕ} (x : coHomK (2 + n)) → isOfHLevel (3 + n) (Code n x)
  hLevCode {n = n} =
    trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropIsOfHLevel (3 + n)))
      (sphereToPropElim _
        (λ _ → (isPropIsOfHLevel (3 + n))) (isOfHLevelTrunc (3 + n)))

  Code-add' : {n : ℕ} (x : _) → Code n ∣ north ∣ → Code n ∣ x ∣ → Code n ∣ x ∣
  Code-add' {n = n} north = _+ₖ_
  Code-add' {n = n} south = _+ₖ_
  Code-add' {n = n} (merid a i) = helper n a i
    where
    help : (n : ℕ) → (x y a : S₊ (suc n))
        → transport (λ i → Code n ∣ north ∣ → Code n ∣ merid a i ∣ → Code n ∣ merid a i ∣)
                     (_+ₖ_) ∣ x ∣ ∣ y ∣
         ≡ ∣ x ∣ +ₖ ∣ y ∣
    help n x y a =
         (λ i → transportRefl ((∣ transportRefl x i ∣  +ₖ (∣ transportRefl y i ∣ -ₖ ∣ a ∣)) +ₖ ∣ a ∣) i)
      ∙∙ cong (_+ₖ ∣ a ∣) (assocₖ _ ∣ x ∣ ∣ y ∣ (-ₖ ∣ a ∣))
      ∙∙ sym (assocₖ _ (∣ x ∣ +ₖ ∣ y ∣) (-ₖ ∣ a ∣) ∣ a ∣)
      ∙∙ cong ((∣ x ∣ +ₖ ∣ y ∣) +ₖ_) (lCancelₖ _ ∣ a ∣)
      ∙∙ rUnitₖ _ _

    helper : (n : ℕ) (a : S₊ (suc n))
           → PathP (λ i → Code n ∣ north ∣ → Code n ∣ merid a i ∣ → Code n ∣ merid a i ∣) _+ₖ_ _+ₖ_
    helper n a =
      toPathP (funExt
                (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelΠ (3 + n) (λ _ → isOfHLevelTrunc (3 + n))) _ _)
                  λ x → funExt
                           (trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
                                   λ y → help n x y a)))

  Code-add : {n : ℕ} (x : _) → Code n ∣ north ∣ → Code n x → Code n x
  Code-add {n = n} =
    trElim (λ x → isOfHLevelΠ (4 + n) λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelSuc (3 + n) (hLevCode {n = n} x))
           Code-add'

  encode-hom : {n : ℕ} {x : _} (q : 0ₖ _ ≡ 0ₖ _) (p : 0ₖ _ ≡ x)
             → encode (q ∙ p) ≡ Code-add {n = n} x (encode q) (encode p)
  encode-hom {n = n} q = J (λ x p → encode (q ∙ p) ≡ Code-add {n = n} x (encode q) (encode p))
                           (cong encode (sym (rUnit q))
                         ∙∙ sym (rUnitₖ _ (encode q))
                         ∙∙ cong (encode q +ₖ_) (cong ∣_∣ (sym (transportRefl _))))

stabSpheres : (n : ℕ) → Iso (coHomK (suc n)) (typ (Ω (coHomK-ptd (2 + n))))
fun (stabSpheres n) = decode _
inv' (stabSpheres n) = encode
rightInv (stabSpheres n) p = decode-encode p
leftInv (stabSpheres n) =
  trElim (λ _ → isOfHLevelPath (3 + n) (isOfHLevelTrunc (3 + n)) _ _)
    λ a → cong encode (congFunct ∣_∣ (merid a) (sym (merid (ptSn (suc n)))))
        ∙∙ (λ i → transport (congFunct (Code n) (cong ∣_∣ (merid a))
                             (cong ∣_∣ (sym (merid (ptSn (suc n))))) i) ∣ ptSn (suc n) ∣)
        ∙∙ (substComposite (λ x → x)
                           (cong (Code n) (cong ∣_∣ (merid a)))
                           (cong (Code n) (cong ∣_∣ (sym (merid (ptSn (suc n)))))) ∣ ptSn (suc n) ∣
        ∙∙ cong (transport (λ i → Code n ∣ merid (ptSn (suc n)) (~ i) ∣))
                (transportRefl (∣ (ptSn (suc n)) ∣ +ₖ ∣ a ∣) ∙ lUnitₖ (suc n) ∣ a ∣)
        ∙∙ symMeridLem n (ptSn (suc n)) ∣ a ∣
        ∙∙ cong (∣ a ∣ +ₖ_) -0ₖ
        ∙∙ rUnitₖ (suc n) ∣ a ∣)

Iso-Kn-ΩKn+1 : (n : HLevel) → Iso (coHomK n) (typ (Ω (coHomK-ptd (suc n))))
Iso-Kn-ΩKn+1 zero = invIso (compIso (congIso (truncIdempotentIso _ isGroupoidS¹)) ΩS¹IsoInt)
Iso-Kn-ΩKn+1 (suc n) = stabSpheres n

Kn≃ΩKn+1 : {n : ℕ} → coHomK n ≃ typ (Ω (coHomK-ptd (suc n)))
Kn≃ΩKn+1 {n = n} = isoToEquiv (Iso-Kn-ΩKn+1 n)

-- Some properties of the Iso
Kn→ΩKn+1 : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
Kn→ΩKn+1 n = Iso.fun (Iso-Kn-ΩKn+1 n)

ΩKn+1→Kn : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
ΩKn+1→Kn n = Iso.inv (Iso-Kn-ΩKn+1 n)

Kn→ΩKn+10ₖ : (n : ℕ) → Kn→ΩKn+1 n (0ₖ n) ≡ refl
Kn→ΩKn+10ₖ zero = sym (rUnit refl)
Kn→ΩKn+10ₖ (suc n) i j = ∣ (rCancel (merid (ptSn (suc n))) i j) ∣

ΩKn+1→Kn-refl : (n : ℕ) → ΩKn+1→Kn n refl ≡ 0ₖ n
ΩKn+1→Kn-refl zero = refl
ΩKn+1→Kn-refl (suc zero) = refl
ΩKn+1→Kn-refl (suc (suc n)) = refl

Kn→ΩKn+1-hom : (n : ℕ) (x y : coHomK n) → Kn→ΩKn+1 n (x +[ n ]ₖ y) ≡ Kn→ΩKn+1 n x ∙ Kn→ΩKn+1 n y
Kn→ΩKn+1-hom zero x y = (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
                                         (inS (∣ intLoop (x ℤ+ y) i ∣)) (~ j))
                      ∙∙ (λ j i → ∣ intLoop-hom x y (~ j) i ∣)
                      ∙∙ (congFunct ∣_∣ (intLoop x) (intLoop y)
                        ∙ cong₂ _∙_ (λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
                                                    (inS (∣ intLoop x i ∣)) j)
                                     λ j i → hfill (doubleComp-faces (λ i₁ → ∣ base ∣) (λ _ → ∣ base ∣) i)
                                                    (inS (∣ intLoop y i ∣)) j)
Kn→ΩKn+1-hom (suc n) = σ-hom

ΩKn+1→Kn-hom : (n : ℕ) (x y : Path (coHomK (suc n)) (0ₖ _) (0ₖ _))
             → ΩKn+1→Kn n (x ∙ y) ≡ ΩKn+1→Kn n x +[ n ]ₖ ΩKn+1→Kn n y
ΩKn+1→Kn-hom zero p q =
     cong winding (congFunct (trRec isGroupoidS¹ (λ x → x)) p q)
   ∙ winding-hom (cong (trRec isGroupoidS¹ (λ x → x)) p) (cong (trRec isGroupoidS¹ (λ x → x)) q)
ΩKn+1→Kn-hom (suc n) = encode-hom

-- With the equivalence Kn≃ΩKn+1, we get that the two definitions of cohomology groups agree
open GroupHom
open GroupIso

coHom≅coHomΩ : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → GroupIso (coHomGr n A) (coHomGrΩ n A)
fun (isom (coHom≅coHomΩ n A)) = map λ f a → Kn→ΩKn+1 n (f a)
inv' (isom (coHom≅coHomΩ n A)) = map λ f a → ΩKn+1→Kn n (f a)
rightInv (isom (coHom≅coHomΩ n A)) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ f → cong ∣_∣₂ (funExt λ x → rightInv (Iso-Kn-ΩKn+1 n) (f x))
leftInv (isom (coHom≅coHomΩ n A)) =
  sElim (λ _ → isOfHLevelPath 2 § _ _)
        λ f → cong ∣_∣₂ (funExt λ x → leftInv (Iso-Kn-ΩKn+1 n) (f x))
isHom (coHom≅coHomΩ n A) =
  sElim2 (λ _ _ → isOfHLevelPath 2 § _ _)
         λ f g → cong ∣_∣₂ (funExt λ x → Kn→ΩKn+1-hom n (f x) (g x))

module lockedKnIso (key : Unit') where
  Kn→ΩKn+1' : (n : ℕ) → coHomK n → typ (Ω (coHomK-ptd (suc n)))
  Kn→ΩKn+1' n = lock key (Iso.fun (Iso-Kn-ΩKn+1 n))

  ΩKn+1→Kn' : (n : ℕ) → typ (Ω (coHomK-ptd (suc n))) → coHomK n
  ΩKn+1→Kn' n = lock key (Iso.inv (Iso-Kn-ΩKn+1 n))

  ΩKn+1→Kn→ΩKn+1 : (n : ℕ) → (x : typ (Ω (coHomK-ptd (suc n)))) → Kn→ΩKn+1' n (ΩKn+1→Kn' n x) ≡ x
  ΩKn+1→Kn→ΩKn+1 n x = pm key
    where
    pm : (key : Unit') → lock key (Iso.fun (Iso-Kn-ΩKn+1 n)) (lock key (Iso.inv (Iso-Kn-ΩKn+1 n)) x) ≡ x
    pm unlock = Iso.rightInv (Iso-Kn-ΩKn+1 n) x

  Kn→ΩKn+1→Kn : (n : ℕ) → (x : coHomK n) → ΩKn+1→Kn' n (Kn→ΩKn+1' n x) ≡ x
  Kn→ΩKn+1→Kn n x = pm key
    where
    pm : (key : Unit') → lock key (Iso.inv (Iso-Kn-ΩKn+1 n)) (lock key (Iso.fun (Iso-Kn-ΩKn+1 n)) x) ≡ x
    pm unlock = Iso.leftInv (Iso-Kn-ΩKn+1 n) x

-distrLemma : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n m : ℕ) (f : GroupHom (coHomGr n A) (coHomGr m B))
              (x y : coHom n A)
            → fun f (x -[ n ]ₕ y) ≡ fun f x -[ m ]ₕ fun f y
-distrLemma n m f' x y = sym (-cancelRₕ m (f y) (f (x -[ n ]ₕ y)))
                     ∙∙ cong (λ x → x -[ m ]ₕ f y) (sym (isHom f' (x -[ n ]ₕ y) y))
                     ∙∙ cong (λ x → x -[ m ]ₕ f y) ( cong f (-+cancelₕ n _ _))
  where
  f = fun f'

isOfHLevelΩ→isOfHLevel :
  ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → ((x : A) → isOfHLevel (suc n) (x ≡ x)) → isOfHLevel (2 + n) A
isOfHLevelΩ→isOfHLevel zero hΩ x y =
  J (λ y p → (q : x ≡ y) → p ≡ q) (hΩ x refl)
isOfHLevelΩ→isOfHLevel (suc n) hΩ x y =
  J (λ y p → (q : x ≡ y) → isOfHLevel (suc n) (p ≡ q)) (hΩ x refl)

contrMin : (n : ℕ) → isContr (coHomK-ptd (suc n) →∙ coHomK-ptd n)
fst (contrMin zero) = (λ _ → 0) , refl
snd (contrMin zero) (f , p) =
  Σ≡Prop (λ f → isSetInt _ _)
         (funExt (trElim (λ _ → isOfHLevelPath 3 (isOfHLevelSuc 2 isSetInt) _ _)
                 (toPropElim (λ _ → isSetInt _ _) (sym p))))
fst (contrMin (suc n)) = (λ _ → 0ₖ _) , refl
snd (contrMin (suc n)) f =
  ΣPathP ((funExt (trElim (λ _ → isOfHLevelPath (4 + n) (isOfHLevelSuc (3 + n) (isOfHLevelTrunc (3 + n))) _ _)
         (sphereElim _ (λ _ → isOfHLevelTrunc (3 + n) _ _) (sym (snd f))))) ,
         λ i j → snd f (~ i ∨ j))

ΩfunExtIso : (A B : Pointed₀) → Iso (typ (Ω (A →∙ B ∙))) (A →∙ Ω B)
fst (fun (ΩfunExtIso A B) p) x = funExt⁻ (cong fst p) x
snd (fun (ΩfunExtIso A B) p) i j = snd (p j) i
fst (inv' (ΩfunExtIso A B) (f , p) i) x = f x i
snd (inv' (ΩfunExtIso A B) (f , p) i) j = p j i
fst (rightInv (ΩfunExtIso A B) (f , p) i) x = f x
snd (rightInv (ΩfunExtIso A B) (f , p) i) j = p j
fst (leftInv (ΩfunExtIso A B) p i j) y = fst (p j) y
snd (leftInv (ΩfunExtIso A B) p i j) k = snd (p j) k

open import Cubical.Foundations.Univalence
pointedEquiv→Path : {A B : Pointed₀} (e : fst A ≃ fst B) → fst e (snd A) ≡ snd B → A ≡ B
fst (pointedEquiv→Path e p i) = ua e i
snd (pointedEquiv→Path {A = A} e p i) = hcomp (λ k → λ {(i = i0) → snd A ; (i = i1) → (transportRefl (fst e (snd A)) ∙ p) k}) (transp (λ j → ua e (i ∧ j)) (~ i) (snd A))

ind₂ : {A : Pointed₀} (n : ℕ) → Iso (A →∙ Ω (coHomK-ptd (suc n))) (typ (Ω (A →∙ coHomK-ptd (suc n) ∙)))
fst (fun (ind₂ n) (f , p) i) x = f x i
snd (fun (ind₂ n) (f , p) i) j = p j i
fst (inv' (ind₂ n) p) x = funExt⁻ (cong fst p) x
snd (inv' (ind₂ n) p) i j = snd (p j) i
rightInv (ind₂ n) p = refl
leftInv (ind₂ n) (f , p) = refl

taha : {A : Pointed₀} (n : ℕ) (f : A →∙ coHomK-ptd (suc n)) → Iso (typ A → coHomK (suc n)) (typ A → coHomK (suc n))
fun (taha n (f , p)) g a = g a +ₖ f a
inv' (taha n (f , p)) g a = g a -ₖ f a
rightInv (taha n (f , p)) g =
  funExt λ x → sym (assocₖ (suc n) (g x) (-ₖ (f x)) (f x)) ∙∙ cong (g x +ₖ_) (lCancelₖ (suc n) (f x)) ∙∙ rUnitₖ (suc n) (g x)
leftInv (taha n (f , p)) g =
  funExt λ x → sym (assocₖ (suc n) (g x) (f x) (-ₖ (f x))) ∙∙ cong (g x +ₖ_) (rCancelₖ (suc n) (f x)) ∙∙ rUnitₖ (suc n) (g x)


ind₁ : {A : Pointed₀} (n : ℕ) (f : A →∙ coHomK-ptd (suc n)) → (A →∙ coHomK-ptd (suc n) ∙) ≡ ((A →∙ coHomK-ptd (suc n) , f))
ind₁ {A  = A} n (f , p) = pointedEquiv→Path (Σ-cong-equiv (isoToEquiv (taha n (f , p))) λ g → pathToEquiv λ i → (cong ((g (snd A)) +ₖ_) p ∙ rUnitₖ (suc n) (g (snd A))) (~ i) ≡ 0ₖ (suc n))
                          (ΣPathP ((funExt (λ x → lUnitₖ (suc n) (f x)))
                          , (toPathP ((λ j → transp (λ i → lUnitₖ (suc n) (f (snd A)) i ≡ ∣ ptSn (suc n) ∣) i0
                                                   (transp
                                                    (λ i →
                                                       hcomp
                                                       (doubleComp-faces (λ _ → ∣ ptSn (suc n) ∣ +ₖ f (snd A))
                                                        (rUnitₖ (suc n) ∣ ptSn (suc n) ∣) (~ i ∧ ~ j))
                                                       (∣ ptSn (suc n) ∣ +ₖ p (~ i ∧ ~ j))
                                                       ≡ ∣ ptSn (suc n) ∣)
                                                    j λ i → hcomp
                                                       (doubleComp-faces (λ _ → ∣ ptSn (suc n) ∣ +ₖ f (snd A))
                                                        (rUnitₖ (suc n) ∣ ptSn (suc n) ∣) (i ∨ ~ j))
                                                       (∣ ptSn (suc n) ∣ +ₖ p (i ∨ ~ j))))
                                                    ∙∙ (λ j → transp (λ i → lUnitₖ (suc n) (f (snd A)) (i ∨ j) ≡ ∣ ptSn (suc n) ∣) j
                                                                      ((λ i → lUnitₖ (suc n) (f (snd A)) (~ i ∧ j)) ∙∙ (λ i → ∣ ptSn (suc n) ∣ +ₖ p i) ∙∙ (rUnitₖ (suc n) ∣ ptSn (suc n) ∣)))
                                                    ∙∙ helper n (f (snd A)) (sym p)))))
  where
  helper : (n : ℕ) (x : coHomK (suc n)) (p : 0ₖ (suc n) ≡ x) → (sym (lUnitₖ (suc n) x) ∙∙ cong (0ₖ (suc n) +ₖ_) (sym p) ∙∙ rUnitₖ (suc n) (0ₖ _)) ≡ sym p
  helper zero x =
    J (λ x p → (sym (lUnitₖ 1 x) ∙∙ cong (0ₖ 1 +ₖ_) (sym p) ∙∙ rUnitₖ 1 (0ₖ _)) ≡ sym p)
      (sym (rUnit refl))
  helper (suc n) x =
    J (λ x p → (sym (lUnitₖ (suc (suc n)) x) ∙∙ cong (0ₖ (suc (suc n)) +ₖ_) (sym p) ∙∙ rUnitₖ (suc (suc n)) (0ₖ _)) ≡ sym p)
      (sym (rUnit refl))


hlevStep₁ : {A : Pointed₀} (n m : ℕ) → isOfHLevel (suc m) (typ (Ω (A →∙ coHomK-ptd (suc n) ∙)))
                                    → isOfHLevel (suc (suc m)) (A →∙ coHomK-ptd (suc n))
hlevStep₁ n m hlev =
  isOfHLevelΩ→isOfHLevel m λ f → subst (λ x → isOfHLevel (suc m) (typ (Ω x))) (ind₁ n f) hlev
  
hlevStep₂ : {A : Pointed₀} (n m : ℕ) → isOfHLevel (suc m) (A →∙ Ω (coHomK-ptd (suc n))) → isOfHLevel (suc m) (typ (Ω (A →∙ coHomK-ptd (suc n) ∙)))
hlevStep₂ n m hlev = isOfHLevelRetractFromIso (suc m) (invIso (ind₂ n)) hlev

hlevStep₃ :  {A : Pointed₀} (n m : ℕ) → isOfHLevel (suc m) (A →∙ coHomK-ptd n) → isOfHLevel (suc m) (A →∙ Ω (coHomK-ptd (suc n)))
hlevStep₃ {A = A} n m hlev = subst (isOfHLevel (suc m)) (λ i → A →∙ pointedEquiv→Path {A = Ω (coHomK-ptd (suc n))} {B = coHomK-ptd n} (invEquiv Kn≃ΩKn+1) (ΩKn+1→Kn-refl n) (~ i)) hlev

hlevTotal : {A : Pointed₀} (n m : ℕ) → isOfHLevel (suc m) (A →∙ coHomK-ptd n) → isOfHLevel (suc (suc m)) (A →∙ coHomK-ptd (suc n))
hlevTotal n m hlev = hlevStep₁ n m (hlevStep₂ n m (hlevStep₃ n m hlev))

wow : ∀ n m → isOfHLevel (2 + n) (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (n + m)))
wow zero m = hlevTotal m 0 (isContr→isProp (contrMin m))
wow (suc n) m = hlevTotal (suc (n + m)) (suc n) (wow n m)

isOfHLevel→∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} (n : ℕ) → isOfHLevel n (fst B) → isOfHLevel n (A →∙ B)
isOfHLevel→∙ n hlev = isOfHLevelΣ n (isOfHLevelΠ n (λ _ → hlev)) λ x → isOfHLevelPath n hlev _ _

^ₖ : {n : ℕ} (m : Int) → coHomK n → coHomK n
^ₖ {n = n} (pos zero) x = 0ₖ _
^ₖ {n = n} (pos (suc m)) x = x +ₖ ^ₖ (pos m) x
^ₖ {n = n} (negsuc zero) x = -ₖ x
^ₖ {n = n} (negsuc (suc m)) x = ^ₖ (negsuc m) x -ₖ x

^ₖ-base : {n : ℕ} (m : Int) → ^ₖ m (0ₖ n) ≡ 0ₖ n
^ₖ-base (pos zero) = refl
^ₖ-base (pos (suc n)) = cong (0ₖ _ +ₖ_) (^ₖ-base (pos n)) ∙ rUnitₖ _ (0ₖ _)
^ₖ-base {n = zero} (negsuc zero) = refl
^ₖ-base {n = suc zero} (negsuc zero) = refl
^ₖ-base {n = suc (suc k)} (negsuc zero) = refl
^ₖ-base {n = zero} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (^ₖ-base (negsuc n))
^ₖ-base {n = suc zero} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (^ₖ-base (negsuc n))
^ₖ-base {n = suc (suc k)} (negsuc (suc n)) = cong (λ x → x -ₖ (0ₖ _)) (^ₖ-base (negsuc n))

k : (n m : ℕ) → S₊ (suc n) → coHomK-ptd (suc m) →∙ coHomK-ptd (suc (n + suc m))
k zero m base = (λ _ → 0ₖ _) , refl
k zero m (loop i) = (λ x → Kn→ΩKn+1 _ x i) , (λ j → Kn→ΩKn+10ₖ _ j i)
fst (k (suc n) m north) _ = 0ₖ _
snd (k (suc n) m north) = refl
fst (k (suc n) m south) _ = 0ₖ _
snd (k (suc n) m south) = refl
fst (k (suc n) m (merid a i)) x = Kn→ΩKn+1 _ (k n m a .fst x) i
snd (k (suc n) m (merid a i)) j =
  (cong (Kn→ΩKn+1 (suc (n + suc m))) (k n m a .snd)
  ∙ Kn→ΩKn+10ₖ (suc (n + (suc m)))) j i


⌣ₖ' : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
⌣ₖ' zero zero x = (λ y → y ℤ∙ x) , refl
⌣ₖ' zero (suc m) x = ^ₖ x , ^ₖ-base x
⌣ₖ' (suc n) zero x =
  subst (λ m → coHomK-ptd zero →∙ coHomK-ptd (suc m)) (+-comm zero n)
        ((λ y → ^ₖ y x) , refl)
⌣ₖ' (suc n) (suc m) =
  trRec (subst (isOfHLevel (3 + n))
            (λ i → (coHomK-ptd (suc m) →∙ coHomK-ptd (suc (+-suc n m (~ i))))) (wow (suc n) m))
    (k n m)
_⌣ₖ_ : {n m : ℕ} → coHomK n → coHomK m → coHomK (n + m)
_⌣ₖ_ {n = n} {m = m} x = fst (⌣ₖ' n m x)

_⌣_ : ∀ {ℓ} {A : Type ℓ} {n m : ℕ} → coHom n A → coHom m A → coHom (n + m) A
_⌣_ {n = n} {m = m} = sRec2 squash₂ λ f g → ∣ (λ x → f x ⌣ₖ g x) ∣₂

-ₖ̂_ : (n : ℕ) {m : ℕ} → coHomK m → coHomK m
-ₖ̂ zero = λ x → x
(-ₖ̂ suc n) {m = m} x = -[ m ]ₖ (-ₖ̂ n) x

sisi : (n m : ℕ) → (x : coHomK n) (y : coHomK m) → (x ⌣ₖ y) ≡ -ₖ̂_ (n · m) (subst (coHomK) (+-comm m n) (y ⌣ₖ x))
sisi zero m = {!!}
sisi (suc n) zero = {!!}
sisi (suc n) (suc m) = {!!}

ptpt : (n m : ℕ) → (x : coHomK n) → (-ₖ̂ (n · m)) (subst coHomK (+-comm m n) (fst (⌣ₖ' m n (snd (coHomK-ptd m))) x)) ≡ 0ₖ _
ptpt n m = {!!}

cong-ₖ : (n : ℕ) → (p : typ ((Ω^ 2) (coHomK-ptd 1))) → cong (cong (-ₖ_)) p ≡ {!!}
cong-ₖ = {!!}

ptCP∞ : (n m : ℕ) (x : coHomK n) → ⌣ₖ' n m x ≡ ((λ y → -ₖ̂_ (n · m) (subst (coHomK) (+-comm m n) (fst (⌣ₖ' m n y) x))) , ptpt n m x)
ptCP∞ zero m x = {!!}
ptCP∞ (suc n) zero x = {!!}
ptCP∞ (suc n) (suc m) = trElim {!!} {!!}
  where
  help : (n m : ℕ) → (s : S₊ (suc n)) (l : _) → fst (k n m s) l ≡ -ₖ̂_ ((suc n) · (suc m)) (subst (coHomK) (+-comm (suc m) (suc n)) (fst (⌣ₖ' (suc m) (suc n) l) ∣ s ∣))
  help zero zero s =
    trElim (λ _ → isOfHLevelTrunc 4 _ _)
           λ a → {!!} ∙∙ (λ i → -ₖ transportRefl (fst (k 0 0 a) ∣ s ∣) (~ i)) ∙∙ λ i → -ₖ (subst coHomK (rUnit (λ i → 2) i) (fst (k 0 0 a) ∣ s ∣))
    where
    r : cong (fst (k zero zero base)) (λ i → ∣ loop i ∣) ≡ cong (λ x → -ₖ (fst (k 0 0 x) ∣ base ∣)) loop
    r i = cong (λ x → -ₖ x) (Kn→ΩKn+10ₖ 1 (~ i))

    l : cong (λ x → fst (k 0 0 x) ∣ base ∣) loop ≡ cong (λ x → -ₖ (fst (k zero zero base) x)) (λ i → ∣ loop i ∣)
    l i = Kn→ΩKn+10ₖ 1 i

    r-l : Square {!λ i j → (fst (k 0 0 (loop (i ∧ j)))) (∣ loop j ∣)!} {!cong (λ x → -ₖ fst (k zero zero base) x) (λ i → ∣ loop i ∣)!} l r
    -- PathP (λ i → {!cong (λ x → fst (k 0 0 x) ∣ base ∣) loop!} ≡ {!!}) l r
    r-l = {!!}

    lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (n : ℕ)
         → PathP (λ i → Path (Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ x ∣) (congFunct ∣_∣ p (sym p) (~ i)) refl)
                  (rCancel (cong ∣_∣ p)) (cong (cong ∣_∣) (rCancel p))
    lem = {!!}

    lem₂ : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → B) → PathP (λ i → congFunct f p (sym p) i ≡ refl) (cong (cong f) (rCancel p)) (rCancel (cong f p))
    lem₂ = {!!}

    lem₃ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p (~ i) ≡ z) q (p ∙ q)
    lem₃ = {!!}

    lem₄ : (cong₂ (λ s t → fst (k zero zero s) ∣ t ∣) loop loop) ≡ (cong₂ (λ s t → -ₖ (fst (k zero zero t) ∣ s ∣)) loop loop)
    lem₄ = {!!}

    characFun≡S¹ : ∀ {ℓ} {A : Type ℓ} (f g : S¹ → S¹ → A)
                  → (p : f base base ≡ g base base)
                  → (ppₗ : PathP (λ i → p i ≡ p i) (cong (f base) loop) (cong (g base) loop))
                  → (ppᵣ : PathP (λ i → p i ≡ p i) (cong (λ x → f x base) loop ) (cong (λ x → g x base) loop))
                  → PathP (λ i → ppₗ i ≡ ppᵣ i) {!λ i j → f (loop i) (loop j)!} {!!}
                  → (s t : S¹) → f s t ≡ g s t
    characFun≡S¹ f g p ppl ppr pp base base = p
    characFun≡S¹ f g p ppl ppr pp base (loop i) j = ppl j i
    characFun≡S¹ f g p ppl ppr pp (loop i) base j = ppr j i
    characFun≡S¹ f g p ppl ppr pp (loop i) (loop k) j = {!!}

    help2 : (s a : S¹) → fst (k zero zero s) ∣ a ∣ ≡ -ₖ (fst (k 0 0 a) ∣ s ∣)
    help2 base base = refl
    help2 base (loop i) j = r j i
    help2 (loop i) base j = l j i
    help2 (loop i) (loop j) s =
      hcomp (λ r → λ { (i = i0) → -ₖ lem (merid base) 3 r (~ s) j
                       ; (i = i1) → -ₖ lem (merid base) 3 r (~ s) j
                       ; (j = i0) → lem (merid base) 3 r s i
                       ; (j = i1) → lem (merid base) 3 r s i
                       ; (s = i0) → congFunct ∣_∣ (merid (loop j)) (sym (merid base)) (~ r) i
                       ; (s = i1) → -ₖ congFunct ∣_∣ (merid (loop i)) (sym (merid base)) (~ r) j })
            (hcomp (λ r → λ { (i = i0) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ r) (~ s) j -- -ₖ lem (merid base) 3 r (~ s) j
                       ; (i = i1) → lem₂ (cong ∣_∣ (merid base)) (-ₖ_) (~ r) (~ s) j -- -ₖ lem (merid base) 3 r (~ s) j
                       ; (j = i0) → rCancel (cong ∣_∣ (merid base)) s i -- lem (merid base) 3 r s i
                       ; (j = i1) → rCancel (cong ∣_∣ (merid base)) s i -- lem (merid base) 3 r s i
                       ; (s = i0) → (cong ∣_∣ (merid (loop j)) ∙ cong ∣_∣ (sym (merid base))) i
                       ; (s = i1) → congFunct (-ₖ_) (cong ∣_∣ (merid (loop i))) (cong ∣_∣ (sym (merid base))) (~ r) j })
                   (hcomp (λ r → λ { (i = i0) → rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r)) (~ s) j
                       ; (i = i1) → rCancel (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r)) (~ s) j
                       ; (j = i0) → rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ r))) s i
                       ; (j = i1) → rCancel (cong ∣_∣ (λ i → merid base (i ∨ ~ r))) s i
                       ; (s = i0) → {!(cong ∣_∣ (λ i → merid (loop j) (i ∨ ~ r)) ∙ cong ∣_∣ (sym (λ i → merid base (i ∨ ~ r)))) i!}
                       ; (s = i1) → (((cong ∣_∣ (lem₃ (merid base) (sym (merid (loop i))) r))) ∙ sym (cong ∣_∣ (lem₃ (merid base) (sym (merid base)) r))) j })
                         {!!}))
      where
      help3 : {!!}
      help3 = {!!}
  help zero (suc m) s l = {!!}
  help (suc n) m s l = {!i = i0 ⊢ help2 base (loop j) s
i = i1 ⊢ help2 base (loop j) s
j = i0 ⊢ help2 (loop i) base s
j = i1 ⊢ help2 (loop i) base s
s = i0 ⊢ fst (k zero zero (loop i))
         ∣ loop j ∣
s = i1 ⊢ -ₖ
         fst (k 0 0 (loop j)) ∣ loop i ∣!}

-- ⌣ₖ∙ : (n m : ℕ) → (coHomK n → (coHomK-ptd m) →∙ coHomK-ptd (n + m))
-- ⌣ₖ∙ zero zero = λ x → (λ y → y ℤ∙ x) , refl
-- ⌣ₖ∙ zero (suc zero) x = (trMap λ {base → base ; (loop i) → intLoop x i}) , refl
-- ⌣ₖ∙ zero (suc (suc m)) = {!!}
-- ⌣ₖ∙ (suc n) zero = {!!}
-- ⌣ₖ∙ (suc zero) (suc m) = {!!}
-- ⌣ₖ∙ (suc (suc n)) (suc zero) = {!!}
-- ⌣ₖ∙ (suc (suc n)) (suc (suc m)) = trRec {!wow (suc n) (suc m)!} {!!}
--   where
--   helpME! : Susp (S₊ (suc n)) →
--       coHomK (suc m) → coHomK (suc (suc (n + (suc m))))
--   helpME! north x = 0ₖ _
--   helpME! south x = 0ₖ _
--   helpME! (merid a i) x = Kn→ΩKn+1 (suc (n + suc m)) (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst x) i
--   {- (λ x → Kn→ΩKn+1 _ (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst x) i) , λ j → (cong (Kn→ΩKn+1 (suc (n + (suc m)))) (⌣ₖ∙ (suc n) m ∣ a ∣ .snd) ∙ Kn→ΩKn+10ₖ (suc (n + (suc m)))) j i 
--     where
--     help : (n m : ℕ) (a : _) → Kn→ΩKn+1 (suc (n + (suc m)))
--       (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .fst (snd (coHomK-ptd (suc m)))) ≡ refl
--     help n m a = cong (Kn→ΩKn+1 (suc (n + (suc m)))) (⌣ₖ∙ (suc n) (suc m) ∣ a ∣ .snd) ∙ Kn→ΩKn+10ₖ (suc (n + (suc m))) -}
