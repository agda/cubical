{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.Groups.WedgeOfSpheres where

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

S₊∙ : (n : ℕ) → Pointed₀
S₊∙ n = (S₊ n) , north


isOfHLevelPushout : ∀ {ℓ} {A : Type ℓ} (a : A) (n : ℕ) → isOfHLevel n A → isOfHLevel n ((A , a) ⋁ (A , a))
isOfHLevelPushout {A = A} a zero hlev = (inr a) , (λ {(inr a2) → helper2 a2
                                             ; (inl a2) → helper a2
                                             ; (push t i) → pathP i})
  where
  helper : (a2 : A) →  Path ((A , a) ⋁ (A , a)) (inr a) (inl a2)
  helper a2 = sym (push tt) ∙ λ i → inl (isOfHLevelSuc 0 hlev a a2 i)
  helper2 : (a2 : A) →  Path ((A , a) ⋁ (A , a)) (inr a) (inr a2)
  helper2 a2 i = inr (isOfHLevelSuc 0 hlev a a2 i)

  pathP : PathP (λ i → Path ((A , a) ⋁ (A , a)) (inr a) (push tt i))
                (helper a) (helper2 a)
  pathP j i =
    hcomp (λ k → λ { (i = i0) → inr a
                    ; (i = i1) → push tt j
                    ; (j = i0) → ((rUnit (sym (push tt)))
                                 ∙ (λ i → sym (push tt) ∙ (λ j → inl (helper3 (~ i) j)))) k i
                    ; (j = i1) → inr (helper3 (~ k) i)})
          (push tt (~ i ∨ j))
    where
    helper3 : (isOfHLevelSuc 0 hlev a a) ≡ refl
    helper3 = isOfHLevelPlus 2 hlev a a (isOfHLevelSuc 0 hlev a a) refl

isOfHLevelPushout {A = A} a (suc zero) hlev x y = {!!}
  where
  helper : (a2 : A) →  Path ((A , a) ⋁ (A , a)) (inr a) (inl a2)
  helper a2 = sym (push tt) ∙ λ i → inl (hlev a a2 i)
  helper2 : (a2 : A) →  Path ((A , a) ⋁ (A , a)) (inr a) (inr a2)
  helper2 a2 i = inr (hlev a a2 i)

  pathP : PathP (λ i → Path ((A , a) ⋁ (A , a)) (inr a) (push tt i))
                (helper a) (helper2 a)
  pathP j i =
    hcomp (λ k → λ { (i = i0) → inr a
                    ; (i = i1) → push tt j
                    ; (j = i0) → ((rUnit (sym (push tt)))
                                 ∙ (λ i → sym (push tt) ∙ (λ j → inl (helper3 (~ i) j)))) k i
                    ; (j = i1) → inr (helper3 (~ k) i)})
          (push tt (~ i ∨ j))
    where
    helper3 : hlev a a ≡ refl
    helper3 = isOfHLevelSuc 1 hlev a a _ _

isOfHLevelPushout a (suc (suc n)) hlev (inl x) (inl y) = {!!}
isOfHLevelPushout a (suc (suc n)) hlev (inl x) (inr x₁) = {!!}
isOfHLevelPushout a (suc (suc n)) hlev (inl x) (push a₁ i) = {!!}
isOfHLevelPushout a (suc (suc n)) hlev (inr x) y = {!!}
isOfHLevelPushout a (suc (suc n)) hlev (push a₁ i) y = {!!}

PushoutToProp : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : A → B} {g : A → C}
                {D : Pushout f g → Type ℓ'''}
              → ((x : Pushout f g) → isProp (D x))
              → ((a : B) → D (inl a))
              → ((c : C) → D (inr c))
              → (x : Pushout f g) → D x
PushoutToProp isset baseB baseC (inl x) = baseB x
PushoutToProp isset baseB baseC (inr x) = baseC x
PushoutToProp {f = f} {g = g} isset baseB baseC (push a i) =
  isOfHLevel→isOfHLevelDep 1 isset (baseB (f a)) (baseC (g a)) (push a) i

H⁰-S¹⋁S¹ : grIso intGroup (coHomGr 0 ((S₊∙ 1) ⋁ S₊∙ 1))
H⁰-S¹⋁S¹ =
  Iso'→Iso
    (iso'
      (iso
        (λ a → ∣ (λ _ → a) ∣₀)
        (sRec isSetInt (λ f → f (inl north)))
        (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
               (λ f → cong ∣_∣₀
                           (funExt (PushoutToProp
                                      (λ _ → isSetInt _ _)
                                      (suspToPropRec north (λ _ → isSetInt _ _) refl)
                                      (suspToPropRec north (λ _ → isSetInt _ _) λ i → f (push tt i))))))
        λ _ → refl)
      λ a b → cong ∣_∣₀ (funExt λ _ → sym (addLemma a b)))

test0 : Iso (((S₊ 1 , north) ⋁ ((S₊ 1) , north) → Int)) Int
Iso.fun test0 f = f (inl north)
Iso.inv test0 a _ = a
Iso.rightInv test0 = λ a → refl
Iso.leftInv test0 a =
  funExt (PushoutToProp (λ _ → isSetInt _ _)
         (suspToPropRec north (λ _ → isSetInt _ _) refl)
         (suspToPropRec north (λ _ → isSetInt _ _) λ i → a (push tt i)))



test : Iso (((S₊ 1 , north) ⋁ ((S₊ 1) , north) → hLevelTrunc 3 (S₊ 1))) ((S₊ 1 → hLevelTrunc 3 (S₊ 1)) × (S₊ 1 → hLevelTrunc 3 (S₊ 1)))
Iso.fun test f = (λ x → f (inl x)) , (λ x → f (inr x)) -- (λ x → f (inl x)) , λ x → f (inr x)
Iso.inv test (f , g) (inl x) = f x +ₖ (-ₖ f north) -- f x
Iso.inv test (f , g) (inr x) = g x +ₖ (-ₖ g north) -- g x
Iso.inv test (f , g) (push a i) = (rCancelₖ (f north) ∙ (sym (rCancelₖ (g north)))) i
Iso.rightInv test (f , g) = ×≡ (funExt {!!}) {!!}
Iso.leftInv test a = funExt λ {(inl x) → {!!} ; (inr x) → {!!} ; (push a i) → {!!}}



mapsTo0 : (f : S₊ 1 → hLevelTrunc 3 (S₊ 1))
      → ∥ f north ≡ ∣ north ∣ ∥₋₁
mapsTo0 f = coInd f (f north) refl 
  where
  coInd : (f : S₊ 1 → hLevelTrunc 3 (S₊ 1)) (x : hLevelTrunc 3 (S₊ 1)) → f north ≡ x → ∥ f north ≡ ∣ north ∣ ∥₋₁
  coInd f =
    trElim (λ _ → isOfHLevelΠ 3 λ _ → isOfHLevelPlus {n = 1} 2 propTruncIsProp)
           (suspToPropRec north
                          (λ _ → isOfHLevelΠ 1 λ _ → propTruncIsProp)
                          ∣_∣₋₁)

mapsTo0' : (f : S₊ 1 → hLevelTrunc 3 (S₊ 1)) (x : _)
      → ∥ f x ≡ ∣ north ∣ ∥₋₁
mapsTo0' f = suspToPropRec north (λ _ → propTruncIsProp) (mapsTo0 f)

testID : Iso ∥ (((S¹ , base) ⋁ (S¹ , base)) → S¹) ∥₀ ∥ ((S¹ × S¹) → S¹) ∥₀
Iso.fun testID = sRec setTruncIsSet λ f → ∣ (λ {(a , b) → f {!!}}) ∣₀
Iso.inv testID a = {!!}
Iso.rightInv testID a = {!!}
Iso.leftInv testID = {!!}


maybe13 : Iso (Σ[ f ∈ coHom 1 (S₊∙ 1 ⋁ S₊∙ 1) ] isInIm (coHomGr 0 Unit) (coHomGr 1 _) (morph.fun (MV.d (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0)) f)
              ∥ S₊ 1 ∥₀
Iso.fun maybe13 (f , inim) =
  pRec helper (sigmaElim (λ _ → setTruncIsSet) (λ g id → {!!})) inim
  where
  helper : isProp ∥ S₊ 1 ∥₀
  helper = {!!}
Iso.inv maybe13 = {!!}
{- 
  sRec (isOfHLevelΣ 2 setTruncIsSet (λ _ → isOfHLevelSuc 1 (propTruncIsProp)))
       (λ p →  ∣ (λ {(inl x) → 0ₖ ; (inr x) → 0ₖ ; (push tt i) → p i}) ∣₀
              , ∣ ∣ (λ _ → ΩKn+1→Kn p) ∣₀ , (cong ∣_∣₀ (funExt λ {(inl x) → refl
                                                               ; (inr x) → refl
                                                               ; (push tt i) → cong (λ x → x i)
       (Iso.rightInv (Iso3-Kn-ΩKn+1 0) p)})) ∣₋₁) -}
Iso.rightInv maybe13 = {!!}
Iso.leftInv maybe13 (f , inim) =
  pRec {!!} {!!} inim


maybe : (a b : Int) (x : MV.D (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north)) → MV.d-pre (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0 (λ _ → a) x ≡ MV.d-pre (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0 (λ _ → b) x
maybe a b (inl x) = refl
maybe a b (inr x) = refl
maybe a b (push a₁ i) j = {!Kn→ΩKn+1 zero ?!}

testID2 : Iso (coHom 1 ((S₊∙ 1) ⋁ S₊∙ 1)) (coHom 1 (S₊ 1 × S₊ 1))
Iso.fun testID2 = sRec setTruncIsSet λ f → ∣ (λ {(a , b) → f (inl a) +ₖ f (inl b)}) ∣₀
Iso.inv testID2 = sRec setTruncIsSet λ f → ∣ (λ {(inl x) → f (x , north) ; (inr x) → f (north , x) ; (push tt i) → f (north , snd (S₊∙ 1))}) ∣₀
Iso.rightInv testID2 = sElim {!!} λ f → cong ∣_∣₀ (funExt (λ {(a , b) → {!!}}))
  where 
  helper : (f : S₊ 1 × S₊ 1 → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1) → (f (north , north) ≡ 0ₖ ) → (a b : S₊ 1) → f (a , north) +ₖ f (b , north) ≡ f (a , b)
  helper f id north north = (cong ((f (north , north)) +ₖ_) id) ∙ rUnitₖ (f (north , north))
  helper f id north south = cong (f (north , north) +ₖ_) (λ i → f (merid north (~ i) , north)) ∙ cong ((f (north , north)) +ₖ_) id ∙ rUnitₖ (f (north , north)) ∙ λ i → f (north , merid north i)
  helper f id north (merid a i) = {!!}
    where
    testhelper : {!!} ∙ (cong ((f (north , north)) +ₖ_) id) ∙ rUnitₖ (f (north , north)) ∙ {!λ i → f (north , merid a i)!} ≡ cong (f (north , north) +ₖ_) (λ i → f (merid north (~ i) , north)) ∙ cong ((f (north , north)) +ₖ_) id ∙ rUnitₖ (f (north , north)) ∙ λ i → f (north , merid north i)
    testhelper = {!!}
  helper f id south north = {!!}
  helper f id south south = {!!}
  helper f id south (merid a i) = {!!}
  helper f id (merid a i) north = {!!}
  helper f id (merid a i) south = {!!}
  helper f id (merid a i) (merid a₁ i₁) j = {!!}
Iso.leftInv testID2 = sElim {!!} λ f → cong ∣_∣₀ (funExt λ {(inl x) → {!!} ; (inr x) → {!!} ; (push tt i) → {!!}} )

testId3 : Iso (coHom 1 ((S₊∙ 1) ⋁ S₊∙ 1)) (coHom 1 (S₊ 1) × coHom 1 (S₊ 1))
Iso.fun testId3 = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) λ f → ∣ (λ x → {!!}) ∣₀ , {!!}
Iso.inv testId3 = {!!}
Iso.rightInv testId3 = {!!}
Iso.leftInv testId3 = {!!}





test1' : Iso (((S¹ , base) ⋁ (S¹ , base)) → S¹) Int
Iso.fun test1' f = winding (basechange2⁻ _ ((λ i → f (inl (loop i))) ∙ (λ i → f (push tt i)) ∙ (λ i → f (inr (loop i))) ∙ λ i → f (push tt (~ i))))
Iso.inv test1' int (inl x) = {!!}
Iso.inv test1' int (inr x) = x
Iso.inv test1' int (push a i) = basechange2 {!!} {!!} i
Iso.rightInv test1' = {!!}
Iso.leftInv test1' = {!!}

test1 : Iso (coHom 1 (S₊∙ 1 ⋁ S₊∙ 1)) (coHom 1 (S₊ 1) × coHom 1 (S₊ 1))
Iso.fun test1 = sRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet)
                     λ f → ∣ (λ x → f (inl x)) ∣₀ , ∣ (λ x → f (inr x)) ∣₀
Iso.inv test1 (f , g) =
  sElim2 (λ _ _ → setTruncIsSet)
         (λ f g → ∣ (λ {(inl x) → f x +ₖ (-ₖ f north)
                      ; (inr x) → g x +ₖ (-ₖ (g north))
                      ; (push a i) → (rCancelₖ (f north) ∙ (sym (rCancelₖ (g north)))) i}) ∣₀)
         f g
  where

Iso.rightInv test1 =
  prodElim (λ _ → isOfHLevelPath 2 (isOfHLevelProd 2 setTruncIsSet setTruncIsSet) _ _)
            λ f g → pRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet _ _)
                         (λ f0 → pRec (isOfHLevelProd 2 setTruncIsSet setTruncIsSet _ _)
                           (λ g0 → ×≡ (cong ∣_∣₀ (funExt λ {north → cong (λ x → f north +ₖ (-ₖ x)) f0  ∙ cong (f north +ₖ_) -0ₖ ∙ rUnitₖ (f north)
                                                          ; south → cong (λ x → f south +ₖ (-ₖ x)) f0  ∙ cong (f south +ₖ_) -0ₖ ∙ rUnitₖ (f south)
                                                          ; (merid a i) → cong (λ x → f (merid a i) +ₖ (-ₖ x)) f0  ∙ cong (f (merid a i) +ₖ_) -0ₖ ∙ rUnitₖ (f (merid a i))}))
                                       ((cong ∣_∣₀ (funExt λ {north → cong (λ x → g north +ₖ (-ₖ x)) g0  ∙ cong (g north +ₖ_) -0ₖ ∙ rUnitₖ (g north)
                                                          ; south → cong (λ x → g south +ₖ (-ₖ x)) g0  ∙ cong (g south +ₖ_) -0ₖ ∙ rUnitₖ (g south)
                                                          ; (merid a i) → cong (λ x → g (merid a i) +ₖ (-ₖ x)) g0  ∙ cong (g (merid a i) +ₖ_) -0ₖ ∙ rUnitₖ (g (merid a i))}))))
                                       (mapsTo0 g))
                           (mapsTo0 f)

{-        d            i           
 H⁰(Unit) → H¹(S¹∨S¹) → H¹(S¹) × H¹(S¹) → H¹(Unit)
    ℤ                         ℤ×ℤ            0
-}




Iso.leftInv test1 =
  sElim {!!}
   λ f → pRec {!f!}
           (λ fl → pRec {!!}
                     (λ fr → cong ∣_∣₀ (funExt λ {(inl x) → cong (λ y → f (inl x) +ₖ (-ₖ y)) fl  ∙ cong (f (inl x) +ₖ_) -0ₖ ∙ rUnitₖ (f (inl x))
                                                ; (inr x) → cong (λ y → f (inr x) +ₖ (-ₖ y)) fr  ∙ cong (f (inr x) +ₖ_) -0ₖ ∙ rUnitₖ (f (inr x))
                                                ; (push a i) → {!fl -- cong (λ y → f (inl ?) +ₖ (-ₖ y)) fl  ∙ cong (f (inl ?) +ₖ_) -0ₖ ∙ rUnitₖ (f (inl ?))!}}))
                     (mapsTo0 λ x → f (inr x)))
           (mapsTo0 λ x → f (inl x))
  where
  test2 : Iso.inv test1 ≡ {!!}
  test2 = {!!}

  helper4 : (f : S₊∙ 1 ⋁ S₊∙ 1 → ∥ S₊ 1 ∥ ℕ→ℕ₋₂ 1)
         → (x y : hLevelTrunc 3 (S₊ 1))
         → (p : (x ≡ ∣ north ∣))
         → (q : (y ≡ ∣ north ∣))
         → (P : x ≡ y)
         → ∥ PathP (λ i → P i ≡ 0ₖ) p q ∥₋₁
  helper4 f x y p q =
    {!!}
    where
    helper5 : (x y : hLevelTrunc 3 (S₊ 1)) → ∥ x ≡ y ∥₋₁
    helper5 = elim2 (λ _ _ → isOfHLevelPlus {n = 1} 2 propTruncIsProp)
                    (suspToPropRec2 north (λ _ _ → propTruncIsProp)
                      ∣ refl ∣₋₁)


{-        d            i           
 H⁰(Unit) → H¹(S¹∨S¹) → H¹(S¹) × H¹(S¹) → H¹(Unit)
    ℤ                         ℤ×ℤ            0
-}

anotherhelper : (x : coHom 0 Unit)
              → isInIm (×coHomGr 0 (S₊ 1) (S₊ 1)) (coHomGr 0 Unit) (morph.fun (MV.Δ (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0)) x
anotherhelper =
  sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
        λ f → ∣ (∣ (λ _ → f tt) ∣₀ , 0ₕ) , cong ∣_∣₀ (funExt (λ _ → cong ((f tt) +ₖ_) -0ₖ ∙ rUnitₖ (f tt))) ∣₋₁

athirdhelper : (x : coHom 0 Unit)
             → isInKer (coHomGr 0 Unit) (coHomGr 1 _) (morph.fun (MV.d (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0)) x
athirdhelper x = MV.Im-Δ⊂Ker-d (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0 x
                 (anotherhelper x)


afourthhelper : (x : coHom 1 (S₊∙ 1 ⋁ S₊∙ 1)) → isInIm (coHomGr 0 Unit) (coHomGr 1 _) (morph.fun (MV.d (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0)) x
              → x ≡ 0ₕ
afourthhelper x inim = pRec (setTruncIsSet _ _) (λ {(y , id) → sym id ∙ athirdhelper y}) inim

H¹-S¹∨S¹ : grIso (coHomGr 1 (S₊∙ 1 ⋁ S₊∙ 1)) (×coHomGr 1 (S₊ 1) (S₊ 1))
H¹-S¹∨S¹ =
  Iso''→Iso
    (iso''
      (MV.i (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 1)
      (λ x inker → afourthhelper x {!!})
      λ x → {!MV.Ker-Δ⊂Im-i (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 1 x ?!})





-- H¹-S¹∨S¹ : grIso (coHomGr 1 (S₊∙ 1 ⋁ S₊∙ 1)) (×coHomGr 1 (S₊ 1) (S₊ 1))
-- H¹-S¹∨S¹ =
--   Iso''→Iso
--     (iso''
--       (MV.i (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 1)
--       (λ a inker → {!!})
--       λ f → {!!})
--   where
--   test3 : (g : Unit → Int) → {!!}
--   test3 = {!!}


-- coHom1-S1∨S1 : (x : coHom 1 (S₊∙ 1 ⋁ S₊∙ 1))
--              → isInIm (coHomGr 0 Unit) (coHomGr 1 (S₊∙ 1 ⋁ S₊∙ 1))
--                        (morph.fun (MV.d (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0)) x
--              → x ≡ 0ₕ
-- coHom1-S1∨S1 =
--   sElim (λ _ → isOfHLevelΠ 2 λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--         λ f → pRec (setTruncIsSet _ _)
--                 (sigmaElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
--                 λ g id → pRec (setTruncIsSet _ _)
--                                (λ id → {!!})
--                                (Iso.fun PathIdTrunc₀Iso id))
--   where
--   id : (g : (Unit → Int))
--     → (x : MV.D (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north))
--     → MV.d-pre (S₊ 1) (S₊ 1) Unit (λ _ → north) (λ _ → north) 0 g x ≡ 0ₖ
--   id g (inl x) = refl
--   id g (inr x) = refl
--   id g (push a i) j = {!!}


