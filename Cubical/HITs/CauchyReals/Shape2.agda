{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.Shape2 where

open import Cubical.Foundations.Prelude renaming (Cube to PreludeCube)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
-- open import Cubical.Data.Fin

import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Vec as V
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos;ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.GroupoidTruncation as GT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyReals.Circle
open import Cubical.HITs.CauchyReals.CircleMore
open import Cubical.HITs.Sn as Sn
open import Cubical.HITs.S1 as S1
open import Cubical.HITs.Susp
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.Categories.Category

-- open import Cubical.WildCat.Base

open import Cubical.Algebra.Group.ZAction

open import Cubical.Structures.Pointed
open import Cubical.Structures.Product

import Cubical.Homotopy.Loopspace as Lsp
import Cubical.Homotopy.Group.Base as HG

open import Cubical.HITs.SequentialColimit as Seq
open import Cubical.Data.Sequence
open import Cubical.Foundations.Pointed as P

open import Cubical.Foundations.Cubes

-- open import Cubical.Categories.Category renaming (isIso to isCIso)
-- open import Cubical.Categories.Monoidal
-- open import Cubical.Categories.Functor

-- open import Cubical.HITs.CauchyReals.BoundaryHIT

open import Cubical.HITs.Truncation as T

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties


private
  variable
   ℓ ℓ' ℓ'' : Level
   X : Type ℓ

-- open Category
-- open TensorStr

open BinaryRelation


spheres-path : ∀ (A : P.Pointed ℓ) n
   → isOfHLevel (2 ℕ.+ n) (fst A)
   → (f : S₊∙ (suc n) P.→∙ A) →
    ∀ s → fst f s ≡ P.pt A
spheres-path A n hLevelA (f , f-pt) =
  Sn.sphereElim n (λ _ → hLevelA _ _) f-pt


record GSeq (obj : ℕ → Type)
            (_≋_ : ∀ {n} → Rel (obj n) (obj n) ℓ-zero) : Type₁ where
 field
  isEquivRel≋ : ∀ n → isEquivRel (_≋_ {n})
  obj-inv : ∀ {n} → obj n → obj n
  obj-inv-funct : ∀ {n} → (a a' : obj n) → a ≋ a' → obj-inv a ≋ obj-inv a'
  _⊙_ : ∀ {n} → obj n → obj n → obj n
  ⊙-sym : ∀ n → (a b : obj (suc n)) → (a ⊙ b) ≋ (b ⊙ a)
  ⊙-functL : ∀ n → (a a' b : obj n) → a ≋ a' → (a ⊙ b) ≋ (a' ⊙ b)
  ⊙-functR : ∀ n → (a b b' : obj n) → b ≋ b' → (a ⊙ b) ≋ (a ⊙ b')
  unit : ∀ {n} → obj n
  middleIso : ∀ {n} → Iso (obj (suc n)) (Σ (obj n) λ m → (unit ≋ m) × (unit ≋ m))
  -- middle-≋ : ∀ n (a b : obj (suc n)) → a ≋ b → fst (middle a) ≋ fst (middle b)
  -- obj₋₁ : Type
  -- obj₋₁-unit : obj₋₁
  -- obj₀-ev : obj zero → S¹ → obj₋₁
  -- obj₋₁-pt : (x : obj zero) → obj₋₁-ev x (ptSn 1) ≡ obj₋₁-unit

 ⊙-funct : ∀ {n} → (a a' b b' : obj n) → a ≋ a' → b ≋ b' → (a ⊙ b) ≋ (a' ⊙ b')
 ⊙-funct {n} _ _ _ _ a≋a' b≋b' =
  isEquivRel.transitive (isEquivRel≋ n) _ _ _
    (⊙-functL _ _ _ _ a≋a') (⊙-functR _ _ _ _ b≋b')
 
 middle : ∀ {n} →  (obj (suc n)) → (Σ (obj n) λ m → (unit ≋ m) × (unit ≋ m))
 middle {n} = Iso.fun (middleIso {n})
 
 obj/ : ℕ → Type
 obj/ n = (obj n / _≋_)

 obj/∙ : ℕ → Pointed₀
 obj/∙ n = (obj n / _≋_) , [ unit ]/

 obj∙ : ℕ → Pointed₀
 obj∙ n = obj n , unit
 
 _⊙/_ : ∀ {n} → obj/ n → obj/ n → obj/ n
 _⊙/_ {n} = setQuotBinOp
   (isEquivRel.reflexive (isEquivRel≋ n))
   (isEquivRel.reflexive (isEquivRel≋ n))
   _⊙_ ⊙-funct
   
 inv/ :  ∀ {n} → obj/ n → obj/ n 
 inv/ = (setQuotUnaryOp obj-inv obj-inv-funct)

 -- _⊙/_ : ∀ {n} → obj/ (suc n) → obj/ (suc n) → obj/ (suc n)
 -- _⊙/_ {n} = setQuotSymmBinOp
 --   (isEquivRel.reflexive (isEquivRel≋ (suc n)))
 --   (isEquivRel.transitive (isEquivRel≋ (suc n)))
 --   _⊙_ (⊙-sym n) (⊙-functL _)


 _∙≋_ : ∀ {n} → {a b c : obj n} → a ≋ b → b ≋ c → a ≋ c
 _∙≋_ {n} = isEquivRel.transitive (isEquivRel≋ n) _ _ _

 -- split≋ : ∀ n → Σ (obj n) (λ m → (unit ≋ m) × (unit ≋ m)) →
 --                 Σ (obj n) (λ m → (unit ≋ m) × (unit ≋ m)) → Type
 -- split≋ n (o , (o₀ , o₁)) (o' , (o'₀ , o'₁)) =
 --   Σ[ o≋o' ∈ (o ≋ o') ]
 --      (split≋Half n o o' o≋o' o₀ o'₀)
 --       × split≋Half n o o' o≋o' o₁ o'₁


 field

   isGrp⊙/₀ :
     IsGroup [ unit {zero} ]/ _⊙/_ inv/

   isAbGrp⊙/ : ∀ n →
     IsAbGroup [ unit {suc n} ]/ _⊙/_ inv/
   
   middle-⊙ : ∀ n x y →
     fst (middle {n} (x ⊙ y)) ≋ (fst (middle x) ⊙ fst (middle y))


   reflOver≋ : ∀ n →
     GQ.RelOver {ℓ''' = ℓ-zero}
     (λ o → ((unit {n = n} ≋ o))) (_≋_ {n}) (isEquivRel≋ n)

   to-middle-≋ : ∀ n
     → {a b : Σ (obj n) (λ m → (unit ≋ m) × (unit ≋ m))} →
      Iso.inv middleIso a ≋ Iso.inv middleIso b →
      RelOver.RΣ (RelOver× (_≋_ unit) _≋_ (isEquivRel≋ n) (reflOver≋ n))
      a b

   from-middle-≋ : ∀ n {a b : Σ (obj n) (λ m → (unit ≋ m) × (unit ≋ m))} →
      RelOver.RΣ (RelOver× (_≋_ unit) _≋_ (isEquivRel≋ n) (reflOver≋ n))
      a b →
      Iso.inv middleIso a ≋ Iso.inv middleIso b
   

   unit⊙unit : ∀ n → unit ⊙ unit ≡ unit {n}

   middleUnit : ∀ n → middle {n} unit ≡
    (unit , ((isEquivRel.reflexive (isEquivRel≋ n) _)
          , (isEquivRel.reflexive (isEquivRel≋ n) _)))



 
 middle-≋ : ∀ n (a b : obj (suc n)) → a ≋ b → fst (middle a) ≋ fst (middle b)
 middle-≋ n a b r =
  let z = fst (to-middle-≋ n {middle a} {middle b}
            (subst2 _≋_
              (sym (Iso.leftInv middleIso a))
              (sym (Iso.leftInv middleIso b)) r))
  in z
 module _ {n : ℕ} where
  module ER≋ = isEquivRel (isEquivRel≋ n) 
 
 middleIso/ : ∀ n → Iso (obj/ (suc n))
     ∥ Σ (obj n // ER≋.transitive) _ ∥₂
 middleIso/ n =
   compIso
     (liftIso/ _ middleIso )
     (compIso
       (relBiimpl→TruncIso
         (to-middle-≋ n)
         (from-middle-≋ n))
       (RelOver.Σ/Iso (RelOver× _ _ _ (reflOver≋ n))))



 obj-grpStr : ∀ n → AbGroupStr (obj (suc n) / _≋_)
 obj-grpStr n = abgroupstr [ unit ]/ (_⊙/_ {suc n} )
  (setQuotUnaryOp obj-inv obj-inv-funct)
   (isAbGrp⊙/ n)

 objAbGroup : ℕ → AbGroup ℓ-zero 
 objAbGroup n = _ , obj-grpStr n

 isGrp⊙/ : ∀ n →
   IsGroup [ unit {n} ]/ _⊙/_ (setQuotUnaryOp obj-inv obj-inv-funct)
 isGrp⊙/ zero = isGrp⊙/₀
 isGrp⊙/ (suc n) = GroupStr.isGroup (snd (AbGroup→Group (objAbGroup n))) 

 objGroup : ℕ → Group ℓ-zero
 objGroup n = (obj/ n) , (groupstr _ _ _ (isGrp⊙/ n))

 from-a≋a' : ∀ n → {a a' : obj n}
    → Iso (∥ a ≋ a' ∥₁) (∥ unit ≋ (a ⊙ obj-inv a') ∥₁)
 from-a≋a' n {a} {a'} = 
  compIso
   (invIso (isEquivRel→TruncIso (isEquivRel≋ n) _ _))
   (compIso
      (equivToIso (propBiimpl→Equiv (squash/ _ _) (squash/ _ _)
       ((sym
         ∘S _∙ (GroupStr.·InvR (snd (objGroup n)) [ a' ]/))
         ∘S cong (_⊙/ (inv/ [ a' ]/)))
       (invUniqueL' {g = [ _ ]/} {[ _ ]/} ∘S sym)))
      (isEquivRel→TruncIso (isEquivRel≋ n) _ _))
   where 
    open GroupTheory (objGroup n)



 middle/ : ∀ {n} → obj/ (suc n) → obj/ n
 middle/ = SQ.Rec.go w
  where
  w : Rec (obj/ _)
  w .Rec.isSetB = SQ.squash/ 
  w .Rec.f = SQ.[_] ∘ fst ∘ middle
  w .Rec.f∼ a a' = SQ.eq/ _ _ ∘ middle-≋ _ _ _
  
 middleGroupHom : ∀ n → IsGroupHom
      (snd (objGroup (suc n)))
     (middle/)
     (snd (objGroup n))
 middleGroupHom n = makeIsGroupHom
   (SQ.ElimProp2.go w)
  where
  w : ElimProp2
       (λ z z₁ →
          middle/ ((snd (objGroup (suc n)) GroupStr.· z) z₁) ≡
          (snd (objGroup n) GroupStr.· middle/ z) (middle/ z₁))
  w .ElimProp2.isPropB _ _ = SQ.squash/ _ _
  w .ElimProp2.f x y = SQ.eq/ _ _ (middle-⊙ n x y) 

 module Sh (n : ℕ) (A∙ : Pointed₀) 
           (obj→evS₊∙ : obj∙ n →∙ (S₊∙ (suc n) →∙ A∙ ∙))
           
            where
 
  evS₊ : (obj n) → S₊ (suc n) → ⟨ A∙ ⟩ 
  evS₊ o = fst (fst obj→evS₊∙ o)

  evS₊pt : ∀ o → evS₊ o (ptSn (suc n)) ≡ pt A∙
  evS₊pt o = snd (fst obj→evS₊∙ o)
  
  data Sh  : Type where
   σ : ⟨ A∙ ⟩ → Sh
   spoke :
      ∀ (m : obj n) → (r : unit ≋ m) → (s : S₊ (suc n)) →
        σ (evS₊ m s) ≡ σ (pt A∙)

   spoke-pt :
       ∀ (m : obj n) → (r : unit ≋ m) → 
          Square (spoke m r (ptSn (suc n)))
            refl
            (cong σ (evS₊pt m))
            refl

   sh-comp-center : ∀ (x y : obj (suc n)) s →
     (Sh.σ (pt A∙) ≡ Sh.σ (evS₊ (middle (x ⊙ y) .fst) s))
   sh-comp-sqL : ∀ (x y : obj (suc n)) s →
     Square
       (spoke (middle x .fst) (middle x .snd .fst)
         s)
       (sh-comp-center x y s)
       (spoke (middle x .fst) (middle x .snd .snd)
         s)
       (sym (spoke
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
         s))
   sh-comp-sqR : ∀ (x y : obj (suc n)) s →
     Square
       (spoke (middle y .fst) (middle y .snd .snd)
         s)
       (sh-comp-center x y s)
       (spoke (middle y .fst) (middle y .snd .fst)
         s)
       (sym (spoke
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
         s))


   sh-comp-center-pt : ∀ (x y : obj (suc n)) →     
       Square (sh-comp-center x y (ptSn (suc n)))
              refl
              refl
              (cong σ (evS₊pt (middle (x ⊙ y) .fst)))

   sh-comp-sqL-pt : ∀ (x y : obj (suc n)) →
     PreludeCube
       (sh-comp-sqL x y (ptSn (suc n)))
       refl

       (spoke-pt (middle x .fst) (middle x .snd .fst))
       (sh-comp-center-pt x y)

       (spoke-pt (middle x .fst) (middle x .snd .snd))
       (congP (λ _ → sym) (spoke-pt (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)))

   sh-comp-sqR-pt : ∀ (x y : obj (suc n)) →
     PreludeCube
       (sh-comp-sqR x y (ptSn (suc n)))
       refl

       (spoke-pt (middle y .fst) (middle y .snd .snd))
       (sh-comp-center-pt x y)
       
       (spoke-pt (middle y .fst) (middle y .snd .fst))
       (congP (λ _ → sym) (spoke-pt (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)))
       

  -- IsEquivEvS₊ : Type
  -- IsEquivEvS₊ = isEquiv (∣_∣₂ ∘ evS₊)
  
  ptSh : Sh
  ptSh = σ (pt A∙)

  Sh∙ : P.Pointed₀
  Sh∙ = Sh , ptSh

  evS₊-suc : obj (suc n) → S₊ (suc (suc n)) → Sh
  evS₊-suc x north = ptSh
  evS₊-suc x south = ptSh
  evS₊-suc x (merid a i) =
     (sym (spoke _ (fst (snd (middle x))) a)
     ∙∙ refl ∙∙
       (spoke _ (snd (snd (middle x))) a)) i



  evS₊-suc-unit : ∀ s → evS₊-suc unit s ≡ ptSh
  evS₊-suc-unit north = refl
  evS₊-suc-unit south = refl
  evS₊-suc-unit (merid a i) j =
    hcomp (λ k →
    λ {(j = i1) → spoke unit (ER≋.reflexive unit) a k
      ;(i = i0) → spoke (middleUnit n j .fst) (fst (snd (middleUnit n j))) a k
      ;(i = i1) → spoke (middleUnit n j .fst) (snd (snd (middleUnit n j))) a k
      }) (σ (evS₊ (middleUnit n j .fst) a)) 

  evS₊-suc-unit-pt : evS₊-suc-unit (ptSn (suc (suc n))) ≡ refl
  evS₊-suc-unit-pt = refl
  
  obj→evS₊∙-suc : obj∙ (suc n) →∙ (S₊∙ (suc (suc n)) →∙ Sh∙ ∙)
  obj→evS₊∙-suc .fst x .fst = evS₊-suc x
  obj→evS₊∙-suc .fst x .snd = refl
  obj→evS₊∙-suc .snd = ΣPathP (funExt evS₊-suc-unit ,
    flipSquare evS₊-suc-unit-pt)


  evS₊-suc-merid-ptSn : ∀ x →
   cong (evS₊-suc x) (merid (pt (S₊∙ (suc n)))) ≡
    refl
  evS₊-suc-merid-ptSn x =
    sym (PathP→compPathR∙∙ (flipSquare
     (cong sym (PathP→compPathR∙∙ (spoke-pt _ _)) ∙
      sym (cong sym (PathP→compPathR∙∙ (spoke-pt _ _))))))     


  -- evS₊-≋unit : {o o' : obj (suc n)} → o ≋ o' →
  --                 evS₊-suc o ≡ evS₊-suc o'
  -- evS₊-≋unit r = {!!}


  module _ (x y : obj (suc n)) where
   opaque


    mM : obj n
    mM = (middle (x ⊙ y) .fst)

    r₀M : unit ≋ mM
    r₀M = (middle (x ⊙ y) .snd) .fst

    r₁M : unit ≋ mM
    r₁M = (middle (x ⊙ y) .snd) .snd

    evS₊-suc-comp-sq : ∀ (a : S₊ (suc n)) →
        ((refl ∙∙ cong (evS₊-suc x) (toSusp (S₊∙ (suc n)) a) ∙∙ refl))
       ∙ (refl ∙∙ cong (evS₊-suc y) (toSusp (S₊∙ (suc n)) a) ∙∙ refl) ≡
        cong (evS₊-suc (x ⊙ y)) (merid a)
    evS₊-suc-comp-sq a =
      cong₂ _∙_
        (sym (rUnit _)
         ∙ cong-∙ (evS₊-suc x) (merid a) (sym (merid (pt (S₊∙ (suc n)))))
         ∙ cong ((cong (evS₊-suc x) (merid a)) ∙_)
           (cong sym (evS₊-suc-merid-ptSn x))
          ∙ sym (rUnit _)
          ∙ λ j →
             sym (spoke (middle x .fst) (middle x .snd .fst) a)
            ∙∙ (λ i → spoke (middle x .fst) (middle x .snd .snd) a (i ∧ j))
            ∙∙ λ i → spoke (middle x .fst) (middle x .snd .snd) a (i ∨ j))
        (sym (rUnit _)
         ∙ cong-∙ (evS₊-suc y) (merid a) (sym (merid (pt (S₊∙ (suc n)))))
         ∙ cong ((cong (evS₊-suc y) (merid a)) ∙_)
               (cong sym (evS₊-suc-merid-ptSn y))
         ∙ sym (rUnit _)
         ∙ λ j →
             (λ i → spoke (Iso.fun middleIso y .fst)
               (fst (snd (Iso.fun middleIso y))) a (~ i ∨ j))
            ∙∙ (λ i → spoke (Iso.fun middleIso y .fst)
               (fst (snd (Iso.fun middleIso y))) a (~ i ∧ j))
            ∙∙ spoke (Iso.fun middleIso y .fst) (Iso.fun middleIso y .snd .snd)
                a) ∙
        (λ j →
           (sym (spoke (middle x .fst) (middle x .snd .fst) a) ∙∙
             spoke (middle x .fst) (middle x .snd .snd) a
             ∙∙ λ i → sh-comp-center x y a (i ∧ j))
             ∙ ((λ i → sh-comp-center x y a (~ i ∧ j))
              ∙∙ sym (spoke (Iso.fun middleIso y .fst)
                (Iso.fun middleIso y .snd .fst) a) ∙∙
               spoke (Iso.fun middleIso y .fst)
                (Iso.fun middleIso y .snd .snd) a)) ∙ cong₂ (_∙_)
         (sym
           (PathP→compPathR∙∙ (symP (flipSquare (sh-comp-sqL x y a)))))
         ((sym
           (cong (sym)
            (PathP→compPathR∙∙ (symP (flipSquare (sh-comp-sqR x y a))))))) 
        ∙ λ j → (λ i → (spoke
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
         a (~ i ∨ ~ j))) ∙∙ (λ i → (spoke
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
         a (~ i ∧ ~ j))) ∙∙ (spoke
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
         a)
    evS₊-suc-comp : ∀ s →
      fst (HG.∙Π {A = (Sh , σ (pt A∙))}
        (evS₊-suc x  , refl)
        (evS₊-suc y  , refl)) s ≡
        (evS₊-suc (x ⊙ y)) s
    evS₊-suc-comp north _ = ptSh
    evS₊-suc-comp south _ = ptSh 
    evS₊-suc-comp (merid a i) j = evS₊-suc-comp-sq a j i



  -- σ-evS₊-≋ : {o o' : obj (suc n)} → o ≋ o' →
  --                 evS₊-suc o ≡ evS₊-suc o'
  -- σ-evS₊-≋ r = {!!}


  record ShElim {ℓ} (B : Sh → Type ℓ) : Type ℓ where
   field
    σB : ∀ a → B (σ a)
    spokeB : ∀ m r s →
     PathP (λ i → B (spoke m r s i))
       (σB (evS₊ m s)) (σB (pt A∙))
    spokeB-pt : ∀ m r → SquareP (λ i i₁ → B (spoke-pt m r i i₁))
        (spokeB m r (ptSn (suc n)))
        refl
        (cong σB (evS₊pt m))
        refl
        
    sh-comp-centerB : ∀ x y s →
      PathP (λ i → B (sh-comp-center x y s i))
        (σB (pt A∙))
        (σB (evS₊ (middle (x ⊙ y) .fst) s))        

    sh-comp-sqLB : ∀ x y s →
       SquareP (λ i j → B (sh-comp-sqL x y s i j))
       (spokeB (middle x .fst) (middle x .snd .fst)
         s)
       (sh-comp-centerB x y s)
       (spokeB (middle x .fst) (middle x .snd .snd)
         s)
       (symP (spokeB
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
         s))

    sh-comp-sqRB : ∀ x y s →
       SquareP (λ i j → B (sh-comp-sqR x y s i j))
       (spokeB (middle y .fst) (middle y .snd .snd)
         s)
       (sh-comp-centerB x y s)
       (spokeB (middle y .fst) (middle y .snd .fst)
         s)
       (symP (spokeB
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
         s))

    sh-comp-center-ptB : ∀ x y → SquareP
     (λ i i₁ → B (sh-comp-center-pt x y i i₁))
     (sh-comp-centerB x y (ptSn (suc n)) )
     refl
     refl
     (cong σB (evS₊pt (middle (x ⊙ y) .fst)))
    
    sh-comp-sqL-ptB : ∀ x y → CubeP (λ i j k → B (sh-comp-sqL-pt x y i j k))
       (sh-comp-sqLB x y (ptSn (suc n)))
       refl
       (spokeB-pt _ _) (sh-comp-center-ptB x y)
       (spokeB-pt _ _)
        (congP (λ _ → symP) (spokeB-pt _ _))


    sh-comp-sqR-ptB : ∀ x y →  CubeP (λ i j k → B (sh-comp-sqR-pt x y i j k))
       (sh-comp-sqRB x y (ptSn (suc n))) refl
       (spokeB-pt _ _) (sh-comp-center-ptB x y)
       (spokeB-pt _ _)
        (congP (λ _ → symP) (spokeB-pt _ _))


    
   go : ∀ x → B x
   go (σ x) = σB x
   go (spoke m r s i) = spokeB m r s i
   go (spoke-pt m r i i₁) = spokeB-pt m r i i₁
   go (sh-comp-center x y s i) = sh-comp-centerB x y s i
   go (sh-comp-sqL x y s i i₁) = sh-comp-sqLB x y s i i₁
   go (sh-comp-sqR x y s i i₁) = sh-comp-sqRB x y s i i₁
   go (sh-comp-center-pt x y i i₁) = sh-comp-center-ptB x y i i₁
   go (sh-comp-sqL-pt x y i i₁ i₂) = sh-comp-sqL-ptB x y i i₁ i₂
   go (sh-comp-sqR-pt x y i i₁ i₂) = sh-comp-sqR-ptB x y i i₁ i₂
   
  record ShRec {ℓ} (B : Type ℓ) : Type ℓ where
   field
    σB : ⟨ A∙ ⟩ → B
    spokeB : ∀ m r s → σB (fst (fst obj→evS₊∙ m) s) ≡ σB (snd A∙)
    spokeB-pt : ∀ m r → Square
     (spokeB m r (ptSn (suc n))) refl
     (cong σB (snd (fst obj→evS₊∙ m))) refl
        
    sh-comp-centerB : ∀ x y s →
     σB (snd A∙) ≡ σB (fst (fst obj→evS₊∙ (Iso.fun middleIso (x ⊙ y) .fst)) s)

    sh-comp-sqLB : ∀ x y s → Square
      (spokeB (Iso.fun middleIso x .fst) (Iso.fun middleIso x .snd .fst) s)
      (sh-comp-centerB x y s)
      (spokeB (Iso.fun middleIso x .fst) (middle x .snd .snd) s)
      (sym (spokeB (Iso.fun middleIso (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst) s) )
    sh-comp-sqRB : ∀ x y s → Square
      (spokeB (Iso.fun middleIso y .fst) (Iso.fun middleIso y .snd .snd) s)
      (sh-comp-centerB x y s)
      (spokeB (Iso.fun middleIso y .fst) (Iso.fun middleIso y .snd .fst) s)
      (sym (spokeB (Iso.fun middleIso (x ⊙ y) .fst) (Iso.fun middleIso (x ⊙ y) .snd .snd) s) )
    sh-comp-center-ptB : ∀ x y → Square
      (sh-comp-centerB x y (ptSn (suc n))) (λ _ → σB (snd A∙))
      (λ i → σB (snd A∙))
       λ i → σB (snd (fst obj→evS₊∙ (Iso.fun middleIso (x ⊙ y) .fst)) i)    
    sh-comp-sqL-ptB : ∀ x y → PreludeCube
      (sh-comp-sqLB x y (S₊∙ (suc n) .snd)) refl
      (spokeB-pt _ _) (sh-comp-center-ptB x y)
      (spokeB-pt _ _) (congP (λ _ → sym) (spokeB-pt _ _))

    sh-comp-sqR-ptB : ∀ x y → PreludeCube
      (sh-comp-sqRB x y (ptSn (suc n))) refl
      (spokeB-pt _ _) (sh-comp-center-ptB x y)
      (spokeB-pt _ _) (congP (λ _ → sym) (spokeB-pt _ _))
    
   goR : ShElim (λ _ → B)
   goR .ShElim.σB = σB
   goR .ShElim.spokeB = spokeB
   goR .ShElim.spokeB-pt = spokeB-pt
   goR .ShElim.sh-comp-centerB = sh-comp-centerB
   goR .ShElim.sh-comp-sqLB = sh-comp-sqLB
   goR .ShElim.sh-comp-sqRB = sh-comp-sqRB
   goR .ShElim.sh-comp-center-ptB = sh-comp-center-ptB
   goR .ShElim.sh-comp-sqL-ptB = sh-comp-sqL-ptB
   goR .ShElim.sh-comp-sqR-ptB = sh-comp-sqR-ptB

   go : Sh → B
   go = ShElim.go goR


  record ShElim-sn {ℓ} (B : Sh → Type ℓ) : Type ℓ where
   field
    σB : ∀ a → B (σ a)
    spokeB : ∀ m r s →
     PathP (λ i → B (spoke m r s i))
       (σB (evS₊ m s)) (σB (pt A∙))
    spokeB-pt : ∀ m r → SquareP (λ i i₁ → B (spoke-pt m r i i₁))
        (spokeB m r (ptSn (suc n)))
        refl
        (cong σB (evS₊pt m))
        refl    
    hLevelB : ∀ x → isOfHLevel (suc (suc (suc n))) (B x)





   CompPartΣ : (x y : obj (suc n)) (s : S₊ (suc n)) → Type ℓ
   CompPartΣ x y s =
     Σ (Σ[ center ∈
         (PathP (λ i → B (sh-comp-center x y s i))
        (σB (pt A∙))
        (σB (evS₊ (middle (x ⊙ y) .fst) s)))         ]
       SquareP (λ i j → B (sh-comp-sqL x y s i j))
       (spokeB (middle x .fst) (middle x .snd .fst)
         s)
       (center)
       (spokeB (middle x .fst) (middle x .snd .snd)
         s)
       (symP (spokeB
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
         s))) λ (center , _) → 
        SquareP (λ i j → B (sh-comp-sqR x y s i j))
       (spokeB (middle y .fst) (middle y .snd .snd)
         s)
       (center)
       (spokeB (middle y .fst) (middle y .snd .fst)
         s)
       (symP (spokeB
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
         s))


   hLevelCompPartΣ : ∀ x y (s : S₊ (suc n)) →
     isOfHLevel (suc n) (CompPartΣ x y s)
   hLevelCompPartΣ x y s =
      isOfHLevelΣ (suc n) (isContr→isOfHLevel (suc n) (isContrSinglP _ _))
       λ _ → isOfHLevelPathP' (suc n)
               (isOfHLevelPathP' (suc (suc n)) (hLevelB _) _ _ ) _ _


   CompPartΣ' : (x y : obj (suc n)) → CompPartΣ x y (ptSn (suc n)) → Type ℓ
   CompPartΣ' x y ((p , s) , s') =
     Σ[ centerP ∈ (SquareP
     (λ i i₁ → B (sh-comp-center-pt x y i i₁))
     p
     refl
     refl
     (cong σB (evS₊pt (middle (x ⊙ y) .fst)))) ]
       (CubeP (λ i j k → B (sh-comp-sqL-pt x y i j k))
       s
       refl
       (spokeB-pt _ _) centerP
       (spokeB-pt _ _)
        (congP (λ _ → symP) (spokeB-pt _ _)))
       ×
       (CubeP (λ i j k → B (sh-comp-sqR-pt x y i j k))
       s' refl
       (spokeB-pt _ _) centerP
       (spokeB-pt _ _)
        (congP (λ _ → symP) (spokeB-pt _ _)))

   CompPartΣP : (x y : obj (suc n)) → singl (CompPartΣ x y (ptSn (suc n))) 
   CompPartΣP x y = _ , λ i' → Σ (Σ[ center ∈
         PathP (λ i → (B (sh-comp-center-pt x y i' i)))
          _ _ ]
       SquareP (λ i j → B (sh-comp-sqL-pt x y i' i j))
      ((spokeB-pt (middle x .fst) (middle x .snd .fst)) i')
      center
      ((spokeB-pt (middle x .fst) (middle x .snd .snd)) i')
      ((symP
       (spokeB-pt (middle (x ⊙ y) .fst)
        (middle (x ⊙ y) .snd .fst) i')))) λ (center , _) → 
        SquareP (λ i j → B (sh-comp-sqR-pt x y i' i j))
      ((spokeB-pt (middle y .fst) (middle y .snd .snd)) i')
      center
      ((spokeB-pt (middle y .fst) (middle y .snd .fst)) i')
      (symP 
       (spokeB-pt (middle (x ⊙ y) .fst)
        (middle (x ⊙ y) .snd .snd) i'))

   compPartΣP : ∀ x y → singlP (λ i → snd (CompPartΣP x y) (~ i))
    ((refl ,
     refl) ,
      refl)
   compPartΣP x y = fst (isContrSinglP _ _)
   
   compPartΣSt : ∀ x y → Σ (CompPartΣ x y (ptSn (suc n))) (CompPartΣ' x y)
   compPartΣSt x y = fst (compPartΣP x y) ,
     congP (λ _ → fst ∘ fst) (symP (snd (compPartΣP x y))) ,
     (congP (λ _ → snd ∘ fst) (symP (snd (compPartΣP x y))) ,
     congP (λ _ → snd) (symP (snd (compPartΣP x y))))
   
   compPartΣ : ∀ x y s → CompPartΣ x y s
   compPartΣ x y = Sn.sphereElim n (hLevelCompPartΣ x y)
    (fst (compPartΣSt x y))

   compPartΣβ : ∀ x y → _ ≡ _  
   compPartΣβ x y = Sn.sphereElim-ptSn n (hLevelCompPartΣ x y)
    (fst (compPartΣSt x y))


   goR : ShElim B
   goR .ShElim.σB = σB
   goR .ShElim.spokeB = spokeB
   goR .ShElim.spokeB-pt = spokeB-pt
   goR .ShElim.sh-comp-centerB x y s = fst (fst (compPartΣ x y s))
   goR .ShElim.sh-comp-sqLB x y s = snd (fst (compPartΣ x y s))
   goR .ShElim.sh-comp-sqRB x y s = snd (compPartΣ x y s)
   goR .ShElim.sh-comp-center-ptB x y =
     cong (fst ∘ fst) (compPartΣβ x y) ◁ fst (snd (compPartΣSt x y))
   goR .ShElim.sh-comp-sqL-ptB x y i j k =
      hcomp
        (λ z → primPOr (~ i) (i ∨ ~ j ∨ k ∨ ~ k)
          (λ { (i = i0) → snd (fst (compPartΣβ x y (~ z))) j k})
           λ _ → (fst (snd (snd (compPartΣSt x y))) i j k))
        (fst (snd (snd (compPartΣSt x y))) i j k)
   goR .ShElim.sh-comp-sqR-ptB x y i j k =
    hcomp
        (λ z → primPOr (~ i) (i ∨ ~ j ∨ k ∨ ~ k)
          (λ { (i = i0) → snd (compPartΣβ x y (~ z)) j k})
           λ _ → (snd (snd (snd (compPartΣSt x y))) i j k))
        (snd (snd (snd (compPartΣSt x y))) i j k)

   go : ∀ x → B x
   go = ShElim.go goR

  record ShRec-sn {ℓ} (B : Type ℓ) : Type ℓ where
   field
    σB : ∀ a → B
    spokeB : ∀ m r s → σB (fst (fst obj→evS₊∙ m) s) ≡ σB (snd A∙)
    spokeB-pt : (m : obj n) (r : unit ≋ m) →
      (spokeB m r (ptSn (suc n))) ≡ (cong σB (evS₊pt m))
    hLevelB : isOfHLevel (suc (suc (suc n))) B

   goR : ShElim-sn (λ _ → B)
   goR .ShElim-sn.σB = σB
   goR .ShElim-sn.spokeB = spokeB
   goR .ShElim-sn.spokeB-pt m r =
    spokeB-pt m r ◁ λ i j → σB (snd (fst obj→evS₊∙ m) (j ∨ i))
   goR .ShElim-sn.hLevelB _ = hLevelB
   
   go : Sh → B
   go = ShElim-sn.go goR

  -- record ShRec-sn∙ {ℓ} (B : Pointed ℓ) : Type ℓ where
  --  field
  --   σ∙ : (m : obj n) → (unit ≋ m) →
  --     S₊∙ (suc n) →∙ (A B 
    
  --  goR : ShRec-sn ⟨ B ⟩
  --  goR .ShRec-sn.σB = {!!}
  --  goR .ShRec-sn.spokeB = {!!}
  --  goR .ShRec-sn.spokeB-pt = {!!}
  --  goR .ShRec-sn.hLevelB = {!!}
   
  --  go∙ : Sh∙ →∙ B
  --  fst go∙ = ShRec-sn.go goR
  --  snd go∙ = {!!}


  record ShElim-n {ℓ} (B : Sh → Type ℓ) : Type ℓ where
   field
    σB : ∀ a →  (B (σ a))
    hLevelB : ∀ x → isOfHLevel (suc (suc n)) (B x)



   spokeB-pt : ∀ m r →
     PathP (λ i → B (spoke m r (ptSn (suc n)) i))
      (σB (evS₊ m (ptSn (suc n)))) (σB (pt A∙))
   spokeB-pt m r i =
     comp (λ j → B (spoke-pt m r (~ j) i))
       (λ j → λ {
         (i = i0) → σB (evS₊pt m (~ j))
        ;(i = i1) → σB (pt A∙)
        }) (σB (snd A∙))    


   goR : ShElim-sn B
   goR .ShElim-sn.σB = σB
   goR .ShElim-sn.spokeB m r =
     Sn.sphereElim n
      (λ _ → isOfHLevelPathP' (suc n) (hLevelB _) _ _)
      (spokeB-pt m r)

   goR .ShElim-sn.spokeB-pt m r =
    sphereElim-ptSn n
      (λ _ → isOfHLevelPathP' (suc n) (hLevelB _) _ _)
      (spokeB-pt m r) ◁
       λ ~j i →
          fill (λ j → B (spoke-pt m r (~ j) i))
       (λ j → λ {
         (i = i0) → σB (evS₊pt m (~ j))
        ;(i = i1) → σB (pt A∙)
        }) (inS (σB (snd A∙))) (~ ~j)  
     
   goR .ShElim-sn.hLevelB x =
    isOfHLevelSuc (suc (suc n)) (hLevelB x)

   go : ∀ x → (B x)
   go = ShElim-sn.go goR

--   record ShElimProp {ℓ} (B : Sh → Type ℓ) : Type ℓ where
--    field
--     σB : ∀ a → B (σ a)
--     isPropB : ∀ x → isProp (B x)


--    go-r : ShElim-n (λ z → B z)
--    go-r .ShElim-n.σB = σB
--    go-r .ShElim-n.hLevelB a =
--     isOfHLevelPlus' {n = suc n} 1 (isPropB a)
   
--    go : ∀ x → B x
--    go = ShElim-n.go go-r


--   record ShElimSet {ℓ} (B : Sh → Type ℓ) : Type ℓ where
--    field
--     σB : ∀ a → B (σ a)
--     isSetB : ∀ x → isSet (B x)


--    go-r : ShElim-n (λ z → B z)
--    go-r .ShElim-n.σB = σB
--    go-r .ShElim-n.hLevelB a =
--     isOfHLevelPlus' {n = n} 2 (isSetB a)
   
--    go : ∀ x → B x
--    go = ShElim-n.go go-r


--   -- evS₊-suc/≃ : Iso
--   --     (obj/ (suc n))
--   --     ∥ (S₊∙ (suc (suc n)) P.→∙ Sh∙) ∥₂
--   -- evS₊-suc/≃ =
--   --   compIso (compIso (middleIso/ n)
--   --    zz)
--   --     (setTruncIso (Σ-cong-iso-fst funSpaceSuspIso))
--   --  where
--   --   zzz : ∀ a → _
--   --   zzz a = SQ.Rec.go zzzz 
--   --    where
--   --    zzzz : Rec
--   --            ∥
--   --            Σ
--   --            (Σ-syntax (Sh∙ .fst)
--   --             (λ x → Σ-syntax (Sh∙ .fst) (λ y → S₊ (suc n) → x ≡ y)))
--   --            ((λ f → f (S₊∙ (suc (suc n)) .snd) ≡ Sh∙ .snd) ∘
--   --             Iso.fun funSpaceSuspIso)
--   --            ∥₂
--   --    zzzz .Rec.isSetB = ST.squash₂
--   --    zzzz .Rec.f (u≋a₀ , u≋a₁) =
--   --      ∣ (((hub _ u≋a₀) , hub _ u≋a₁ ,
--   --        λ s →
--   --          (spoke _ u≋a₀ s
--   --       ∙∙ (λ _ → σ (evS₊ a s)) ∙∙
--   --        sym (spoke _ u≋a₁ s))) , spoke _ u≋a₀ (ptSn (suc n)) ∙
--   --             cong σ (evS₊pt a)) ∣₂
--   --    zzzz .Rec.f∼ b b' (r , r') =
--   --      cong ∣_∣₂ (ΣPathP
--   --        ((ΣPathP ({!!}
--   --          , {!!})) , {!!}))

--   --   zzzP : {a b : obj n} (r : a ≋ b) → _
--   --   zzzP {a} {b} r = funExtDep λ {x₀} {x₁} → zzzPP {x₀} {x₁}
--   --    where
--   --     zzzPP : ∀ {x₀} {x₁} p → _
--   --     zzzPP {x₀} {x₁} p = SQ.ElimProp.go zzzP' x₀
--   --      where
--   --      zzzP' : ElimProp (λ x₀ → zzz a x₀ ≡ zzz b x₁)
--   --      zzzP' .ElimProp.isPropB _ = ST.squash₂ _ _
--   --      zzzP' .ElimProp.f = {!!}
--   --   zz : Iso
--   --         ∥
--   --         Σ (obj n // ER≋.transitive)
--   --         ((λ r → fst r) ∘
--   --          RelOver.A/R→Type
--   --          (RelOver× (_≋_ unit) _≋_ (isEquivRel≋ n) (reflOver≋ n)))
--   --         ∥₂
--   --         ∥
--   --         Σ
--   --         (Σ-syntax (Sh∙ .fst)
--   --          (λ x → Σ-syntax (Sh∙ .fst) (λ y → S₊ (suc n) → x ≡ y)))
--   --         ((λ f → f (S₊∙ (suc (suc n)) .snd) ≡ Sh∙ .snd) ∘
--   --          Iso.fun funSpaceSuspIso)
--   --         ∥₂
--   --   zz .Iso.fun =
--   --    ST.rec ST.squash₂
--   --      (uncurry (GQ.elimSet ER≋.transitive
--   --       (λ _ → isSet→ ST.squash₂)
--   --       zzz zzzP)) 
     
     
--   --   zz .Iso.inv = {!!}
--   --   zz .Iso.rightInv = {!!}
--   --   zz .Iso.leftInv = {!!}

  Trunc-Sh : Iso (∥ ⟨ A∙ ⟩ ∥ (2 ℕ.+ n)) (∥ Sh ∥ (2 ℕ.+ n))
  Trunc-Sh = w
   where

   ww : ShElim-n (λ _ → ∥ ⟨ A∙ ⟩ ∥ (2 ℕ.+ n))
   ww .ShElim-n.σB = ∣_∣
   ww .ShElim-n.hLevelB _ = isOfHLevelTrunc (suc (suc n))

   w : Iso (∥ ⟨ A∙ ⟩ ∥ (2 ℕ.+ n)) (∥ Sh ∥ (2 ℕ.+ n))
   w .Iso.fun = T.map σ
   w .Iso.inv = T.rec (isOfHLevelTrunc (suc (suc n))) (ShElim-n.go ww)
   w .Iso.rightInv = T.elim
     (λ _ →  isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _)
      (ShElim-n.go www)
           
    where
    www : ShElim-n _
    www .ShElim-n.σB _ = refl
    www .ShElim-n.hLevelB _ =
     isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _
   w .Iso.leftInv =
     T.elim
     (λ _ →  isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _)
      λ _ → refl

  -- Trunc-Sh≤ : ∀ m → m ℕ.≤ (2 ℕ.+ n) → Iso (∥ A ∥ m) (∥ Sh ∥ m)
  -- Trunc-Sh≤ m m≤2+n = w
  --  where

  --  w : Iso (∥ A ∥ m) (∥ Sh ∥ m)
  --  w = compIso {!!} {!!}

  module _ (hLevelA : isOfHLevel (2 ℕ.+ n) ⟨ A∙ ⟩) where

   from-Sh : ShElim-n (λ _ → ⟨ A∙ ⟩)
   from-Sh .ShElim-n.σB a = a
   from-Sh .ShElim-n.hLevelB _ = hLevelA
   
   from-Sh-trunc : ∥ Sh ∥ (2 ℕ.+ n) → ⟨ A∙ ⟩
   from-Sh-trunc = T.rec hLevelA (ShElim-n.go from-Sh)

   sh-right-inv : section (∣_∣ ∘S σ) from-Sh-trunc
   sh-right-inv = T.elim
     (λ _ →  isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _)
     (ShElim-n.go ww)
    where
    ww : ShElim-n _
    ww .ShElim-n.σB _ = refl
    ww .ShElim-n.hLevelB _ =
     isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _ 
    
   sh-left-inv : retract (λ x → ∣ σ x ∣) from-Sh-trunc
   sh-left-inv a = refl
   
   Sh-trunc : Iso ⟨ A∙ ⟩ (∥ Sh ∥ (2 ℕ.+ n))
   Sh-trunc .Iso.fun = ∣_∣ ∘S σ
   Sh-trunc .Iso.inv = from-Sh-trunc
   Sh-trunc .Iso.rightInv = sh-right-inv
   Sh-trunc .Iso.leftInv = sh-left-inv


--  --  module _ (x y : _) where
--  --   opaque 
--  --    evS₊-suc-comp-sq : ∀ (a : S₊ (suc n)) → Square
--  --      (cong (fst (HG.∙Π {A = (Sh , σ (pt A∙))} {n = suc (suc n)}
--  --        (evS₊-suc x  , evS₊pt-suc _)
--  --        (evS₊-suc y  , evS₊pt-suc _))) (merid a))
--  --      ((spoke (middle (x ⊙ y) .fst) (fst (snd (middle (x ⊙ y))))
--  --           a
--  --           ∙∙ (λ _ → σ (evS₊ (middle (x ⊙ y) .fst) a)) ∙∙
--  --           (λ i₁ →
--  --              spoke (middle (x ⊙ y) .fst) (snd (snd (middle (x ⊙ y)))) a (~ i₁))))
--  --      (cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙' sym (spoke _ _ _))
--  --      (cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙' sym (spoke _ _ _))
--  --    evS₊-suc-comp-sq a =

--  --      compPathR→PathP∙∙
--  --        (     cong₂ _∙_
--  --             (evS₊-suc-sq-hlp x a)
--  --             (evS₊-suc-sq-hlp y a) ∙
--  --              (λ j → (λ i → evS₊-suc-sq-hlp x a i1 (j ∧ i))
--  --                 ∙∙ (λ i → evS₊-suc-sq-hlp x a i1 (i ∨ j))
--  --                  ∙∙ evS₊-suc-sq-hlp y a i1 ) ◁

--  --          {!!} ∙
--  --         λ j →
--  --           ((
--  --           (cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙'
--  --            sym
--  --            (spoke (middle (x ⊙ y) .fst) (fst (snd (middle (x ⊙ y))))
--  --             (ptSn (suc n))))
--  --           )
--  --        ∙∙
--  --        (λ i → spoke (middle (x ⊙ y) .fst) (fst (snd (middle (x ⊙ y)))) a i) ∙∙
--  --        (λ _ → σ (evS₊ (middle (x ⊙ y) .fst) a)) ∙∙
--  --        (λ i →
--  --           spoke (middle (x ⊙ y) .fst) (snd (snd (middle (x ⊙ y)))) a (~ i))
--  --        ∙∙
--  --        sym
--  --        (
--  --           (cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙'
--  --            sym
--  --            (spoke (middle (x ⊙ y) .fst) (snd (snd (middle (x ⊙ y))))
--  --             (ptSn (suc n))))
--  --           )))

--  --    evS₊-suc-comp : ∀ s →
--  --      fst (HG.∙Π {A = (Sh , σ (pt A∙))}
--  --        (evS₊-suc x  , evS₊pt-suc _)
--  --        (evS₊-suc y  , evS₊pt-suc _)) s ≡
--  --        (evS₊-suc (x ⊙ y)) s
--  --    evS₊-suc-comp north = cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙' sym (spoke _ _ _)
--  --    evS₊-suc-comp south = cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙' sym (spoke _ _ _)
--  --    evS₊-suc-comp (merid a i) j = evS₊-suc-comp-sq a j i

--  -- open Sh using (σ)


--  -- T0 : Type
--  -- T0 = Sh.Sh (suc zero)
--  --       (Sh0.Sh)
--  --       (σ (obj₋₁-unit))
--  --       Sh0.evS₊-suc --(Sh.evS₊-suc zero obj₋₁ obj₋₁-unit obj₋₁-ev obj₋₁-pt)
--  --       {!Sh0.evS₊pt-suc!}

--  --   where
--  --    module Sh0 = Sh zero obj₋₁ obj₋₁-unit obj₋₁-ev obj₋₁-pt

--  -- -- Shₙ : ℕ → Type
--  -- -- Shₙ-pre : ℕ → Type
--  -- -- Shₙ-pre-pt : ∀ n → Shₙ-pre n
--  -- -- Shₙ-eval : ∀ n → obj n → S₊ (suc n) → Shₙ-pre n
--  -- -- Shₙ-eval-pt : ∀ n → (x : obj n) → Shₙ-eval n x (ptSn (suc n)) ≡ Shₙ-pre-pt n
--  -- -- -- Shₙ zero = Sh.Sh zero obj₋₁ obj₋₁-unit obj₋₁-ev obj₋₁-pt  
--  -- -- -- Shₙ (suc n) = Sh.Sh (suc n) (Shₙ n)
--  -- -- --   (Shₙ-pt n) {!!} {!!}

--  -- -- Shₙ n = Sh.Sh n (Shₙ-pre n) (Shₙ-pre-pt n) (Shₙ-eval n) (Shₙ-eval-pt n)


--  -- -- Shₙ-pre zero = obj₋₁
--  -- -- Shₙ-pre (suc n) = Shₙ n

--  -- -- Shₙ-pre-pt zero = obj₋₁-unit
--  -- -- Shₙ-pre-pt (suc n) = σ (Shₙ-pre-pt n)

--  -- -- -- Shₙ-eval = {!!}

--  -- -- Shₙ-eval zero  = obj₋₁-ev
--  -- -- Shₙ-eval (suc n) = Sh.evS₊-suc n
--  -- --   (Shₙ-pre n) (Shₙ-pre-pt n) (Shₙ-eval n) (Shₙ-eval-pt n)

--  -- -- Shₙ-eval-pt zero = obj₋₁-pt
--  -- -- Shₙ-eval-pt (suc n) x = {!!}

