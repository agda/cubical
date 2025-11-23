{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.Shape where

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
import Cubical.Foundations.Pointed as P

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

 module Sh (n : ℕ) (A : Type) (ptA : A)
           (evS₊ : obj n → S₊ (suc n) → A)
           (evS₊pt : ∀ x → evS₊ x (ptSn (suc n)) ≡ ptA )
           
            where

  

  data Sh  : Type where
   σ : A → Sh
   hub : (m : obj n) → unit ≋ m → Sh
   spoke : ∀ m r (s : S₊ (suc n)) → hub m r ≡ σ (evS₊ m s)
   spoke-hub-spoke-pt :
      ∀ (m : obj n) → (r : unit ≋ m) → (s : S₊ (suc n)) →
        σ (evS₊ m s) ≡ σ ptA


   spoke-hub-sq : ∀ m r s → Square
     (spoke-hub-spoke-pt m r s)
     (spoke m r (ptSn (suc n)))
     (sym (spoke m r s))
     (cong σ (sym (evS₊pt m))) 

   spoke-hub-spoke-pt-refl : ∀ m r →
     (spoke-hub-spoke-pt m r (ptSn (suc n))) ≡ cong σ (evS₊pt m)
   spoke-hub-sq-pt : ∀ m r →
     PreludeCube
       (spoke-hub-sq m r (ptSn (suc n))) (λ i j → σ (evS₊pt m (~ i ∧ j)))
       (spoke-hub-spoke-pt-refl m r) (λ i j → spoke m r (ptSn (suc n)) (j ∨ i))
       (λ i j → spoke m r (ptSn (suc n)) (~ j ∨ i))
       refl

   

   sh-comp-center : ∀ (x y : obj (suc n)) s →
     (Sh.σ ptA ≡ Sh.σ (evS₊ (middle (x ⊙ y) .fst) s))
   sh-comp-sqL : ∀ (x y : obj (suc n)) s →
     Square
       (spoke-hub-spoke-pt (middle x .fst) (middle x .snd .fst)
         s)
       (sh-comp-center x y s)
       (spoke-hub-spoke-pt (middle x .fst) (middle x .snd .snd)
         s)
       (sym (spoke-hub-spoke-pt
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
         s))
   sh-comp-sqR : ∀ (x y : obj (suc n)) s →
     Square
       (spoke-hub-spoke-pt (middle y .fst) (middle y .snd .snd)
         s)
       (sh-comp-center x y s)
       (spoke-hub-spoke-pt (middle y .fst) (middle y .snd .fst)
         s)
       (sym (spoke-hub-spoke-pt
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
         s))
         
   sh-comp-pt-inv-fill-cap : ∀ (m m' : obj n) →
    Square
      (cong σ (evS₊pt m)) (sym (cong σ (evS₊pt m')))
      (cong σ (evS₊pt m))
      (sym (cong σ (evS₊pt m')))

   sh-comp-pt-inv-fill : ∀ (m m' : obj n) →
     PreludeCube
       (sh-comp-pt-inv-fill-cap m m') refl
       (λ i j → σ (evS₊pt m (j ∨ i))) (λ i j → σ (evS₊pt m' (~ j ∨ i)))
         (λ i j → σ (evS₊pt m (j ∨ i))) λ i j → σ (evS₊pt m' (~ j ∨ i))

   sh-comp-center-refl : ∀ (x y : obj (suc n)) →
     sh-comp-center x y (ptSn (suc n)) ≡
      (cong σ (sym $ evS₊pt (middle (x ⊙ y) .fst)))


   sh-comp-sqL-pt : ∀ (x y : obj (suc n)) →
     PreludeCube
       (sh-comp-sqL x y (ptSn (suc n)))
       (sh-comp-pt-inv-fill-cap _ _)
       (spoke-hub-spoke-pt-refl _ _) (sh-comp-center-refl x y)
       (spoke-hub-spoke-pt-refl _ _) (cong sym (spoke-hub-spoke-pt-refl _ _))

   sh-comp-sqR-pt : ∀ (x y : obj (suc n)) →
     PreludeCube
       (sh-comp-sqR x y (ptSn (suc n))) (sh-comp-pt-inv-fill-cap _ _)
       (spoke-hub-spoke-pt-refl _ _) (sh-comp-center-refl x y)
       (spoke-hub-spoke-pt-refl _ _) (cong sym (spoke-hub-spoke-pt-refl _ _))


--   spoke-hub-spoke-pt-refl : ∀ m r →
--      spoke-hub-spoke-pt m r (ptSn (suc n)) ≡
--       cong σ (evS₊pt m)
--   spoke-hub-spoke-pt-refl m r =
--     PathP→compPathR (spoke-hub-sq m r (ptSn (suc n))) ∙
--      (assoc _ _ _ ∙ cong (_∙ (λ i → σ (evS₊pt m i)))
--       (lCancel (spoke m r (ptSn (suc n))))
--       ∙ sym (lUnit (cong σ (evS₊pt m))))

--   sh-comp-center-refl : ∀ m r →
--      sh-comp-center m r (ptSn (suc n))
--       ≡ cong σ (sym (evS₊pt (middle (m ⊙ r) .fst)))
--   sh-comp-center-refl m r =
--      PathP→compPathR∙∙ (symP (sh-comp-sqR m r (ptSn (suc n))))
--       ∙ cong₃ _∙∙_∙∙_
--         (cong sym (spoke-hub-spoke-pt-refl
--            (middle r .fst) (middle r .snd .fst)))
--         (spoke-hub-spoke-pt-refl
--            (middle r .fst) (middle r .snd .snd))
--         (cong sym
--            (spoke-hub-spoke-pt-refl
--              (middle (m ⊙ r) .fst) (middle (m ⊙ r) .snd .snd)))
--         ∙ λ i j →  
--             hcomp
--               (λ k →
--                 λ { (i = i1) → σ $ evS₊pt (middle (m ⊙ r) .fst) (~ k ∨ ~ j)
--                   ; (j = i0) → σ $ evS₊pt (middle r .fst) (k ∨ i)
--                   ; (j = i1) → σ $ evS₊pt (middle (m ⊙ r) .fst) (~ k)
--                   })
--               (σ $ evS₊pt (middle r .fst) (j ∨ i))


  -- sh-comp-sqL-refl : ∀ x y →
  --    PathP (λ i →
  --      Square
  --      (spoke-hub-spoke-pt-refl (middle x .fst) (middle x .snd .fst)
  --        i)
  --      (sh-comp-center-refl x y i)
  --      (spoke-hub-spoke-pt-refl (middle x .fst) (middle x .snd .snd)
  --        i)
  --      (sym (spoke-hub-spoke-pt-refl
  --        (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
  --        i)))
  --      (sh-comp-sqL x y (ptSn (suc n)))
  --      (symP (invSides-filler _ _))
  -- sh-comp-sqL-refl = {!!}
  IsEquivEvS₊ : Type
  IsEquivEvS₊ = isEquiv (∣_∣₂ ∘ evS₊)
  
  ptSh : Sh
  ptSh = σ ptA

  Sh∙ : P.Pointed₀
  Sh∙ = Sh , ptSh


  evS₊-suc : obj (suc n) → S₊ (suc (suc n)) → Sh
  evS₊-suc x north = hub _ (fst (snd (middle x)))
  evS₊-suc x south = hub _ (snd (snd (middle x)))
  evS₊-suc x (merid a i) =
    (spoke _ (fst (snd (middle x))) a
     ∙∙ (λ _ → σ (evS₊ (middle x .fst) a)) ∙∙
      sym (spoke _ (snd (snd (middle x))) a)) i

  evS₊pt-suc : ∀ x → evS₊-suc x (ptSn (suc (suc n))) ≡ σ ptA
  evS₊pt-suc x = spoke _ _ _ ∙ cong σ (evS₊pt (middle x .fst))


  evS₊-suc-sq-hlp : (x : obj (suc n)) (a : S₊ (suc n)) →
     ((λ i → evS₊pt-suc x (~ i)) ∙∙
      cong (evS₊-suc x) (merid a ∙ (λ i → merid (ptSn (suc n)) (~ i))) ∙∙
      evS₊pt-suc x)
      ≡ sym (spoke-hub-spoke-pt (middle x .fst) (fst (snd (middle x))) a)
             ∙ spoke-hub-spoke-pt (middle x .fst) (snd (snd (middle x))) a
  evS₊-suc-sq-hlp x a =
   (cong ((sym (evS₊pt-suc x)) ∙∙_∙∙ (evS₊pt-suc x))
              (cong-∙ (evS₊-suc x) (merid a) (sym (merid _)))
             ∙ (λ j → ((sym (cong σ (evS₊pt (middle x .fst)))
                         ∙∙ sym (spoke _ (fst (snd (middle x))) _)
                           ∙∙ (λ i → spoke _ (fst (snd (middle x))) a (i ∧ j))) ∙∙ 
                    (((λ i → spoke _ (fst (snd (middle x))) a (i ∨ j))
                       ∙∙ refl ∙∙
                        sym (spoke _ (snd (snd (middle x))) a))) ∙
                    ((spoke _ (snd (snd (middle x))) (ptSn (suc n))
                       ∙∙ refl ∙∙
                        (λ i → spoke _ (fst (snd (middle x))) (ptSn (suc n))
                         (~ i ∨ j))))
                    ∙∙
                    ((λ i → spoke _ (fst (snd (middle x))) (ptSn (suc n)) (i ∨ j))
                      ∙ cong σ (evS₊pt (middle x .fst)))))
             ∙ cong₃ _∙∙_∙∙_
                 refl
                 (cong₂ _∙_ (sym (lUnit _)) (cong sym (sym (lUnit _)) ))
                 (sym (lUnit _)) ∙ doubleCompPath≡compPath _ _ _
                  ∙ cong₂ _∙_ refl (
                    sym (assoc _ _ _) ∙
                    sym (doubleCompPath≡compPath
                      _
                      _ _))
                    ∙ cong₂ _∙_ (sym (PathP→compPathR∙∙
                        (congP (λ _ → symP) (spoke-hub-sq
                         (middle x .fst) (fst (snd (middle x))) a))))
                       (sym (PathP→compPathR∙∙
                        (spoke-hub-sq (middle x .fst) (snd (snd (middle x))) a))))


  record ShElim {ℓ} (B : Sh → Type ℓ) : Type ℓ where
   field
    σB : ∀ a → B (σ a)
    hubB : ∀ m r → B (hub m r)
    spokeB : ∀ m r s →
     PathP (λ i → B (spoke m r s i))
       (hubB m r) (σB (evS₊ m s))
    spoke-hub-spokeB : ∀ m r s →
     PathP (λ i → B (spoke-hub-spoke-pt m r s i))
       (σB (evS₊ m s)) (σB ptA)
    spoke-hub-sqB : ∀ m r s →
       SquareP (λ i i₁ →
         B (spoke-hub-sq m r s i i₁))
         (spoke-hub-spokeB m r s)
         (spokeB m r (ptSn (suc n)))
         (symP (spokeB m r s))
         (cong σB (sym (evS₊pt m)))
    sh-comp-centerB : ∀ x y s →
      PathP (λ i → B (sh-comp-center x y s i))
        (σB ptA)
        (σB (evS₊ (middle (x ⊙ y) .fst) s))
    sh-comp-sqLB : ∀ x y s →
       SquareP (λ i j → B (sh-comp-sqL x y s i j))
       (spoke-hub-spokeB (middle x .fst) (middle x .snd .fst)
         s)
       (sh-comp-centerB x y s)
       (spoke-hub-spokeB (middle x .fst) (middle x .snd .snd)
         s)
       (symP (spoke-hub-spokeB
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
         s))

    sh-comp-sqRB : ∀ x y s →
       SquareP (λ i j → B (sh-comp-sqR x y s i j))
       (spoke-hub-spokeB (middle y .fst) (middle y .snd .snd)
         s)
       (sh-comp-centerB x y s)
       (spoke-hub-spokeB (middle y .fst) (middle y .snd .fst)
         s)
       (symP (spoke-hub-spokeB
         (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
         s))

    spoke-hub-spoke-pt-reflB : ∀ m m' →
      SquareP (λ i j → B (spoke-hub-spoke-pt-refl m m' i j))
        (spoke-hub-spokeB m m' (ptSn (suc n)))
         (cong σB (evS₊pt m))
        refl refl
    
    spoke-hub-sq-ptB : ∀ m r → CubeP
      (λ i j k → B (spoke-hub-sq-pt m r i j k))
                    (spoke-hub-sqB m r (ptSn (suc n)))
                    (congP (λ _ → cong σB) (λ i i₁ → evS₊pt m (~ i ∧ i₁)))
                    (spoke-hub-spoke-pt-reflB m r)
                     ((λ i j → spokeB m r (ptSn (suc n)) (j ∨ i)))
                    ((λ i j → spokeB m r (ptSn (suc n)) (~ j ∨ i))) refl
    
    sh-comp-pt-inv-fill-capB : ∀ m m' →
      SquareP (λ i j → B (sh-comp-pt-inv-fill-cap m m' i j))
        (cong σB _) (cong σB _)
        (cong σB _) (cong σB _)
        
    sh-comp-pt-inv-fillB : ∀ m m'  → CubeP
      (λ i j k → B (sh-comp-pt-inv-fill m m' i j k))
                    (sh-comp-pt-inv-fill-capB m m') refl
                    (congP (λ _ → cong σB) _ ) (congP (λ _ → cong σB) _)
                    (congP (λ _ → cong σB) _) (congP (λ _ → cong σB) _)
    sh-comp-center-reflB : ∀ x y →
     SquareP (λ i j → B (sh-comp-center-refl x y i j))
      (sh-comp-centerB _ _ (ptSn (suc n))) ((cong σB _))
      refl refl

    sh-comp-sqL-ptB : ∀ x y → CubeP (λ i j k → B (sh-comp-sqL-pt x y i j k))
       (sh-comp-sqLB x y (ptSn (suc n)))
       (sh-comp-pt-inv-fill-capB _ _)
       (spoke-hub-spoke-pt-reflB _ _) (sh-comp-center-reflB x y)
       (spoke-hub-spoke-pt-reflB _ _)
        (congP (λ _ → symP) (spoke-hub-spoke-pt-reflB _ _))


    sh-comp-sqR-ptB : ∀ x y →  CubeP (λ i j k → B (sh-comp-sqR-pt x y i j k))
       (sh-comp-sqRB x y (ptSn (suc n))) (sh-comp-pt-inv-fill-capB _ _)
       (spoke-hub-spoke-pt-reflB _ _) (sh-comp-center-reflB x y)
       (spoke-hub-spoke-pt-reflB _ _)
        (congP (λ _ → symP) (spoke-hub-spoke-pt-reflB _ _))


    
   go : ∀ x → B x
   go (σ x) = σB x
   go (hub m x) = hubB m x
   go (spoke m r s i) = spokeB m r s i
   go (spoke-hub-spoke-pt m r s i) = spoke-hub-spokeB m r s i
   go (spoke-hub-sq m r s i i₁) = spoke-hub-sqB m r s i i₁
   go (sh-comp-center x y s i) = sh-comp-centerB x y s i
   go (sh-comp-sqL x y s i i₁) = sh-comp-sqLB x y s i i₁
   go (sh-comp-sqR x y s i i₁) = sh-comp-sqRB x y s i i₁
   
   go (spoke-hub-spoke-pt-refl m r i i₁) =
    spoke-hub-spoke-pt-reflB m r i i₁
   go (spoke-hub-sq-pt m r i i₁ i₂) =
    spoke-hub-sq-ptB m r i i₁ i₂
   go (sh-comp-pt-inv-fill-cap m m' i i₁) =
    sh-comp-pt-inv-fill-capB m m' i i₁
   go (sh-comp-pt-inv-fill m m' i i₁ i₂) =
     sh-comp-pt-inv-fillB m m' i i₁ i₂
   go (sh-comp-center-refl x y i i₁) =
    sh-comp-center-reflB x y i i₁
   go (sh-comp-sqL-pt x y i i₁ i₂) =
    sh-comp-sqL-ptB x y i i₁ i₂
   go (sh-comp-sqR-pt x y i i₁ i₂) =
    sh-comp-sqR-ptB x y i i₁ i₂

  record ShRec {ℓ} (B : Type ℓ) : Type ℓ where
   field
    σB : A → B
    hubB : (m : obj n) → unit ≋ m → B
    spokeB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
      hubB m r ≡ σB (evS₊ m s)
    spoke-hub-spokeB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
      σB (evS₊ m s) ≡ σB ptA
    spoke-hub-sqB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
      Square
        (spoke-hub-spokeB m r s)
        (spokeB m r (ptSn (suc n)))
        (sym (spokeB m r s))
        (cong σB (sym (evS₊pt m)))
    sh-comp-centerB : (x y : obj (suc n)) (s : S₊ (suc n)) →
      σB ptA ≡ σB (evS₊ (middle (x ⊙ y) .fst) s)
    sh-comp-sqLB : (x y : obj (suc n)) (s : S₊ (suc n)) →
      Square
      (spoke-hub-spokeB (middle x .fst) (middle x .snd .fst) s)
      (sh-comp-centerB x y s)
      (spoke-hub-spokeB (middle x .fst) (middle x .snd .snd) s)
      (sym
       (spoke-hub-spokeB (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
        s))
    sh-comp-sqRB : (x y : obj (suc n)) (s : S₊ (suc n)) →
      Square
      (spoke-hub-spokeB (middle y .fst) (middle y .snd .snd) s)
      (sh-comp-centerB x y s)
      (spoke-hub-spokeB (middle y .fst) (middle y .snd .fst) s)
      (sym
       (spoke-hub-spokeB (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
        s))
        
    spoke-hub-spoke-pt-reflB : ∀ m m' →
      Square 
        (spoke-hub-spokeB m m' (ptSn (suc n)))
         (cong σB (evS₊pt m))
        refl refl
    
    spoke-hub-sq-ptB : ∀ m r → PreludeCube

                    (spoke-hub-sqB m r (ptSn (suc n)))
                    (congP (λ _ → cong σB) (λ i i₁ → evS₊pt m (~ i ∧ i₁)))
                    (spoke-hub-spoke-pt-reflB m r)
                     ((λ i j → spokeB m r (ptSn (suc n)) (j ∨ i)))
                    ((λ i j → spokeB m r (ptSn (suc n)) (~ j ∨ i)))
                    (refl)
    
    sh-comp-pt-inv-fill-capB : ∀ m m' →
      Square
        (cong σB (λ i → evS₊pt m i))
      (cong σB (λ i → evS₊pt m' (~ i))) (cong σB (λ i → evS₊pt m i))
      (cong σB (λ i → evS₊pt m' (~ i)))
        
    sh-comp-pt-inv-fillB : ∀ m m'  → PreludeCube
      (sh-comp-pt-inv-fill-capB m m') refl
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
    sh-comp-center-reflB : ∀ x y →
     Square 
      (sh-comp-centerB _ _ (ptSn (suc n))) ((cong σB _))
      refl refl

    sh-comp-sqL-ptB : ∀ x y → PreludeCube 
       (sh-comp-sqLB x y (ptSn (suc n)))
       (sh-comp-pt-inv-fill-capB _ _)
       (spoke-hub-spoke-pt-reflB _ _) (sh-comp-center-reflB x y)
       (spoke-hub-spoke-pt-reflB _ _)
        (congP (λ _ → symP) (spoke-hub-spoke-pt-reflB _ _))


    sh-comp-sqR-ptB : ∀ x y →  PreludeCube 
       (sh-comp-sqRB x y (ptSn (suc n))) (sh-comp-pt-inv-fill-capB _ _)
       (spoke-hub-spoke-pt-reflB _ _) (sh-comp-center-reflB x y)
       (spoke-hub-spoke-pt-reflB _ _)
        (congP (λ _ → symP) (spoke-hub-spoke-pt-reflB _ _))
    
   goR : ShElim (λ _ → B)
   goR .ShElim.σB = σB
   goR .ShElim.hubB = hubB
   goR .ShElim.spokeB = spokeB
   goR .ShElim.spoke-hub-spokeB = spoke-hub-spokeB
   goR .ShElim.spoke-hub-sqB = spoke-hub-sqB
   goR .ShElim.sh-comp-centerB = sh-comp-centerB
   goR .ShElim.sh-comp-sqLB = sh-comp-sqLB
   goR .ShElim.sh-comp-sqRB = sh-comp-sqRB
   goR .ShElim.spoke-hub-spoke-pt-reflB = spoke-hub-spoke-pt-reflB
   goR .ShElim.spoke-hub-sq-ptB = spoke-hub-sq-ptB
   goR .ShElim.sh-comp-pt-inv-fill-capB = sh-comp-pt-inv-fill-capB
   goR .ShElim.sh-comp-pt-inv-fillB = sh-comp-pt-inv-fillB
   goR .ShElim.sh-comp-center-reflB  = sh-comp-center-reflB
   goR .ShElim.sh-comp-sqL-ptB = sh-comp-sqL-ptB
   goR .ShElim.sh-comp-sqR-ptB = sh-comp-sqR-ptB
   
   go : Sh → B
   go = ShElim.go goR

  -- record ShRec' {ℓ} (B : Type ℓ) : Type ℓ where
  --  field
  --   σB : A → B
  --   spoke-hub-spokeB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
  --     σB (evS₊ m s) ≡ σB ptA
  --   spoke-hub-spoke-pt-reflB : ∀ m m' →
  --     Square 
  --       (spoke-hub-spokeB m m' (ptSn (suc n)))
  --        (cong σB (evS₊pt m))
  --       refl refl
    
    
    -- spokeB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
    --   hubB m r ≡ σB (evS₊ m s)
    -- spoke-hub-spokeB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
    --   σB (evS₊ m s) ≡ σB ptA
    -- spoke-hub-sqB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
    --   Square
    --     (spoke-hub-spokeB m r s)
    --     (spokeB m r (ptSn (suc n)))
    --     (sym (spokeB m r s))
    --     (cong σB (sym (evS₊pt m)))
    -- sh-comp-centerB : (x y : obj (suc n)) (s : S₊ (suc n)) →
    --   σB ptA ≡ σB (evS₊ (middle (x ⊙ y) .fst) s)
    -- sh-comp-sqLB : (x y : obj (suc n)) (s : S₊ (suc n)) →
    --   Square
    --   (spoke-hub-spokeB (middle x .fst) (middle x .snd .fst) s)
    --   (sh-comp-centerB x y s)
    --   (spoke-hub-spokeB (middle x .fst) (middle x .snd .snd) s)
    --   (sym
    --    (spoke-hub-spokeB (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
    --     s))
    -- sh-comp-sqRB : (x y : obj (suc n)) (s : S₊ (suc n)) →
    --   Square
    --   (spoke-hub-spokeB (middle y .fst) (middle y .snd .snd) s)
    --   (sh-comp-centerB x y s)
    --   (spoke-hub-spokeB (middle y .fst) (middle y .snd .fst) s)
    --   (sym
    --    (spoke-hub-spokeB (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
    --     s))



   -- spoke-hub-sq-ptB : ∀ (m : obj n) (r : unit ≋ m) →
   --     Σ _ λ s → PreludeCube

   --                  (spoke-hub-sqB m r (ptSn (suc n)))
   --                  (congP (λ _ → cong σB) (λ i j → evS₊pt m (~ i ∧ j)))
   --                  s
   --                   (λ i j → spokeB m r (ptSn (suc n)) (j ∨ i))
   --                  (λ i j → spokeB m r (ptSn (suc n)) (~ j ∨ i))
   --                   (refl {x = cong σB (sym (evS₊pt m))})
   -- spoke-hub-sq-ptB m r = _ ,
   --  λ i k j → hfill (λ ~k →
   --     λ {  (i = i0) → spoke-hub-sqB m r (ptSn (suc n)) (~ ~k) j
   --        ; (i = i1) → σB (evS₊pt m (~k ∧ j))
   --        ; (j = i0) → spokeB m r (ptSn (suc n)) (~k ∨ i)
   --        ; (j = i1) → σB (evS₊pt m ~k)
   --        }) (inS (spokeB m r (ptSn (suc n)) (j ∨ i))) (~ k)

   -- sh-comp-pt-inv-fillB : ∀ m m'  → Σ _ λ s → PreludeCube
   --    s refl
   --    (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
   --    (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
   --    (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
   --    (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
   -- sh-comp-pt-inv-fillB m m'  = _ ,
   --   λ k i j →  hfill (λ ~k →
   --     λ {  (i = i0) → σB (evS₊pt m (~ ~k ∨ j))
   --        ; (i = i1) → σB (evS₊pt m' (~ ~k ∨ ~ j))
   --        ; (j = i0) → σB (evS₊pt m (~ ~k ∨ i))
   --        ; (j = i1) → σB (evS₊pt m' (~ ~k ∨ ~ i))
   --        }) (inS (σB ptA)) (~ k)

   -- sh-comp-sqL-ptB : (x y : obj (suc n)) →
   --    Σ _ λ s →
   --     (PreludeCube 
   --     (sh-comp-sqLB x y (ptSn (suc n)))
   --     (fst (sh-comp-pt-inv-fillB _ _))
   --     (fst (spoke-hub-sq-ptB _ _))
   --     s
   --     (fst (spoke-hub-sq-ptB _ _))
   --      (congP (λ _ → symP) (fst (spoke-hub-sq-ptB _ _)))
   --     × PreludeCube 
   --     (sh-comp-sqRB x y (ptSn (suc n))) (fst (sh-comp-pt-inv-fillB _ _))
   --     (fst (spoke-hub-sq-ptB _ _))
   --     s
   --     (fst (spoke-hub-sq-ptB _ _))
   --      (congP (λ _ → symP) (fst (spoke-hub-sq-ptB _ _))))
   -- sh-comp-sqL-ptB x y = _ ,
   --  ( (λ i k j → hcomp
   --     (λ z → λ
   --        { (k = i1) → {!!}
   --        ; (k = i0)(i = i1) → {!!}
   --        ; (k = i0)(j = i0) → _
   --        ; (k = i0)(j = i1) → σB (evS₊pt (middle (x ⊙ y) .fst) (z))
   --        ; (j = i0)(i = i1) → σB (evS₊pt (middle x .fst) ((z) ∧ k))
   --        ; (j = i1)(i = i1) → σB (evS₊pt (middle (x ⊙ y) .fst) ((z) ∧ ~ k))
   --        ; (i = i0) → {!!}
   --        })
   --     {!!})
   --  , λ i k j → hcomp
   --     (λ z → λ
   --        { (k = i1) → {!!}
   --        ; (k = i0)(i = i1) → {!!}
   --        ; (k = i0)(j = i0) → _
   --        ; (k = i0)(j = i1) → _
   --        ; (j = i0)(i = i1) → _
   --        ; (j = i1)(i = i1) → _
   --        ; (i = i0) → {!!}
   --        })
   --     {!!})

   -- spoke-hub-sqB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
   --    Square
   --      (spoke-hub-spokeB m r s)
   --      (sym (spoke-hub-spokeB m r (ptSn (suc n))))
   --      (spoke-hub-spokeB m r s)
   --      (cong σB (sym (evS₊pt m)))
   -- spoke-hub-sqB m r s i j =
   --   hcomp (λ z → λ {
   --       (i = i0) → spoke-hub-spokeB m r s (j ∨ ~ z)
   --      ;(i = i1) → spoke-hub-spoke-pt-reflB m r (~ z) (~ j)
   --      ;(j = i0) → spoke-hub-spokeB m r s (i ∨ ~ z) 
   --      ;(j = i1) → σB (sym (evS₊pt m) i)
   --      })
   --      (σB ((evS₊pt m) (~ i ∨ ~ j)))

   -- spoke-hub-sqB= : (m : obj n) (r : unit ≋ m) →
   --    Path (Square
   --      (spoke-hub-spokeB m r (ptSn (suc n)))
   --      (sym (spoke-hub-spokeB m r (ptSn (suc n))))
   --      (spoke-hub-spokeB m r (ptSn (suc n)))
   --      (cong σB (sym (evS₊pt m))))
   --         (spoke-hub-sqB m r (ptSn (suc n)))
   --         λ i j →
   --           hcomp ((λ z → λ {
   --       (i = i0) → spoke-hub-spoke-pt-reflB m r (~ z) j
   --      ;(i = i1) → spoke-hub-spokeB m r (ptSn (suc n)) (~ j ∧ z)
   --      ;(j = i0) → spoke-hub-spokeB m r (ptSn (suc n)) (i ∧ z) 
   --      ;(j = i1) → σB (sym (evS₊pt m) i)
   --      }))
   --      ((σB (evS₊pt m (~ i ∧ j))))
   -- spoke-hub-sqB= m r = {!!}
     

   -- spoke-hub-sq-ptB : ∀ m r → PreludeCube

   --                  (spoke-hub-sqB m r (ptSn (suc n)))
   --                  (congP (λ _ → cong σB) (λ i i₁ → evS₊pt m (~ i ∧ i₁)))
   --                  (spoke-hub-spoke-pt-reflB m r)
   --                   ((λ i j → spoke-hub-spokeB m r (ptSn (suc n)) (~ j ∧ ~ i)))
   --                  ((λ i j → spoke-hub-spokeB m r (ptSn (suc n)) (j ∧ ~ i)))
   --                  (refl)
   -- spoke-hub-sq-ptB m r =
   --   spoke-hub-sqB= m r ◁ λ z i j →
   --     hfill ((λ ~z → λ {
   --       (i = i0) → spoke-hub-spoke-pt-reflB m r (~ ~z) j
   --      ;(i = i1) → spoke-hub-spokeB m r (ptSn (suc n)) (~ j ∧ ~z)
   --      ;(j = i0) → spoke-hub-spokeB m r (ptSn (suc n)) (i ∧ ~z) 
   --      ;(j = i1) → σB (sym (evS₊pt m) i)
   --      }))
   --      (inS (σB (evS₊pt m (~ i ∧ j)))) (~ z) 

   -- sh-comp-pt-inv-fillB : ∀ m m'  → Σ _ λ s → PreludeCube
   --    s refl
   --    (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
   --    (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
   --    (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
   --    (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
   -- sh-comp-pt-inv-fillB m m'  = _ ,
   --   λ k i j →  hfill (λ ~k →
   --     λ {  (i = i0) → σB (evS₊pt m (~ ~k ∨ j))
   --        ; (i = i1) → σB (evS₊pt m' (~ ~k ∨ ~ j))
   --        ; (j = i0) → σB (evS₊pt m (~ ~k ∨ i))
   --        ; (j = i1) → σB (evS₊pt m' (~ ~k ∨ ~ i))
   --        }) (inS (σB ptA)) (~ k)


   -- goR : ShRec B
   -- goR .ShRec.σB = σB
   -- goR .ShRec.hubB _ _ = σB ptA
   -- goR .ShRec.spokeB m r s = sym (spoke-hub-spokeB m r s)
   -- goR .ShRec.spoke-hub-spokeB = spoke-hub-spokeB
   -- goR .ShRec.spoke-hub-sqB = spoke-hub-sqB
   -- goR .ShRec.sh-comp-centerB x y s = sym (spoke-hub-spokeB _
   --  (middle (x ⊙ y) .snd .fst) s)
   -- goR .ShRec.sh-comp-sqLB = {! !}
   -- goR .ShRec.sh-comp-sqRB = {! !}
   -- goR .ShRec.spoke-hub-spoke-pt-reflB = spoke-hub-spoke-pt-reflB
   -- goR .ShRec.spoke-hub-sq-ptB = spoke-hub-sq-ptB 
   -- goR .ShRec.sh-comp-pt-inv-fill-capB m m' = fst (sh-comp-pt-inv-fillB m m')
   -- goR .ShRec.sh-comp-pt-inv-fillB m m' = snd (sh-comp-pt-inv-fillB m m')
   -- goR .ShRec.sh-comp-center-reflB _ _ = cong sym (spoke-hub-spoke-pt-reflB _ _)
   -- goR .ShRec.sh-comp-sqL-ptB = {!!}
   -- goR .ShRec.sh-comp-sqR-ptB = {!!}
   
   -- go : Sh → B
   -- go = ShRec.go goR


--   -- record ShRec' {ℓ} (B : Type ℓ) : Type ℓ where
--   --  field
--   --   σB : A → B
--   --   hubB : (m : obj n) → unit ≋ m → B
--   --   spokeB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
--   --     hubB m r ≡ σB (evS₊ m s)
--   --   spoke-hub-spokeB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
--   --     σB (evS₊ m s) ≡ σB ptA
--   --   spoke-hub-sqB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
--   --     Square
--   --       (spoke-hub-spokeB m r s)
--   --       (spokeB m r (ptSn (suc n)))
--   --       (sym (spokeB m r s))
--   --       (cong σB (sym (evS₊pt m)))
--   --   sh-comp-centerB : (x y : obj (suc n)) (s : S₊ (suc n)) →
--   --     σB ptA ≡ σB (evS₊ (middle (x ⊙ y) .fst) s)
--   --   sh-comp-sqLB : (x y : obj (suc n)) (s : S₊ (suc n)) →
--   --     Square
--   --     (spoke-hub-spokeB (middle x .fst) (middle x .snd .fst) s)
--   --     (sh-comp-centerB x y s)
--   --     (spoke-hub-spokeB (middle x .fst) (middle x .snd .snd) s)
--   --     (sym
--   --      (spoke-hub-spokeB (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
--   --       s))
--   --   sh-comp-sqRB : (x y : obj (suc n)) (s : S₊ (suc n)) →
--   --     Square
--   --     (spoke-hub-spokeB (middle y .fst) (middle y .snd .snd) s)
--   --     (sh-comp-centerB x y s)
--   --     (spoke-hub-spokeB (middle y .fst) (middle y .snd .fst) s)
--   --     (sym
--   --      (spoke-hub-spokeB (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
--   --       s))
         
--   --  spoke-hub-sq-ptB : ∀ (m : obj n) (r : unit ≋ m) →
--   --      Σ _ λ s → PreludeCube

--   --                   (spoke-hub-sqB m r (ptSn (suc n)))
--   --                   (congP (λ _ → cong σB) (λ i j → evS₊pt m (~ i ∧ j)))
--   --                   s
--   --                    (λ i j → spokeB m r (ptSn (suc n)) (j ∨ i))
--   --                   (λ i j → spokeB m r (ptSn (suc n)) (~ j ∨ i))
--   --                    (refl {x = cong σB (sym (evS₊pt m))})
--   --  spoke-hub-sq-ptB m r = _ ,
--   --   λ i k j → hfill (λ ~k →
--   --      λ {  (i = i0) → spoke-hub-sqB m r (ptSn (suc n)) (~ ~k) j
--   --         ; (i = i1) → σB (evS₊pt m (~k ∧ j))
--   --         ; (j = i0) → spokeB m r (ptSn (suc n)) (~k ∨ i)
--   --         ; (j = i1) → σB (evS₊pt m ~k)
--   --         }) (inS (spokeB m r (ptSn (suc n)) (j ∨ i))) (~ k)

--   --  sh-comp-pt-inv-fillB : ∀ m m'  → Σ _ λ s → PreludeCube
--   --     s refl
--   --     (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
--   --     (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
--   --     (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
--   --     (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
--   --  sh-comp-pt-inv-fillB m m'  = _ ,
--   --    λ k i j →  hfill (λ ~k →
--   --      λ {  (i = i0) → σB (evS₊pt m (~ ~k ∨ j))
--   --         ; (i = i1) → σB (evS₊pt m' (~ ~k ∨ ~ j))
--   --         ; (j = i0) → σB (evS₊pt m (~ ~k ∨ i))
--   --         ; (j = i1) → σB (evS₊pt m' (~ ~k ∨ ~ i))
--   --         }) (inS (σB ptA)) (~ k)

--   --  sh-comp-sqL-ptB : (x y : obj (suc n)) →
--   --     Σ _ λ s →
--   --      (PreludeCube 
--   --      (sh-comp-sqLB x y (ptSn (suc n)))
--   --      (fst (sh-comp-pt-inv-fillB _ _))
--   --      (fst (spoke-hub-sq-ptB _ _))
--   --      s
--   --      (fst (spoke-hub-sq-ptB _ _))
--   --       (congP (λ _ → symP) (fst (spoke-hub-sq-ptB _ _)))
--   --      × PreludeCube 
--   --      (sh-comp-sqRB x y (ptSn (suc n))) (fst (sh-comp-pt-inv-fillB _ _))
--   --      (fst (spoke-hub-sq-ptB _ _))
--   --      s
--   --      (fst (spoke-hub-sq-ptB _ _))
--   --       (congP (λ _ → symP) (fst (spoke-hub-sq-ptB _ _))))
--   --  sh-comp-sqL-ptB x y = _ ,
--   --   ( (λ i k j → hcomp
--   --      (λ z → λ
--   --         { (k = i1) → {!!}
--   --         ; (k = i0)(i = i1) → {!!}
--   --         ; (k = i0)(j = i0) → _
--   --         ; (k = i0)(j = i1) → σB (evS₊pt (middle (x ⊙ y) .fst) (z))
--   --         ; (j = i0)(i = i1) → σB (evS₊pt (middle x .fst) ((z) ∧ k))
--   --         ; (j = i1)(i = i1) → σB (evS₊pt (middle (x ⊙ y) .fst) ((z) ∧ ~ k))
--   --         ; (i = i0) → {!!}
--   --         })
--   --      {!!})
--   --   , λ i k j → hcomp
--   --      (λ z → λ
--   --         { (k = i1) → {!!}
--   --         ; (k = i0)(i = i1) → {!!}
--   --         ; (k = i0)(j = i0) → _
--   --         ; (k = i0)(j = i1) → _
--   --         ; (j = i0)(i = i1) → _
--   --         ; (j = i1)(i = i1) → _
--   --         ; (i = i0) → {!!}
--   --         })
--   --      {!!})



--   --  goR : ShRec B
--   --  goR .ShRec.σB = σB
--   --  goR .ShRec.hubB = hubB
--   --  goR .ShRec.spokeB = spokeB
--   --  goR .ShRec.spoke-hub-spokeB = spoke-hub-spokeB
--   --  goR .ShRec.spoke-hub-sqB = spoke-hub-sqB
--   --  goR .ShRec.sh-comp-centerB = sh-comp-centerB
--   --  goR .ShRec.sh-comp-sqLB = sh-comp-sqLB
--   --  goR .ShRec.sh-comp-sqRB = sh-comp-sqRB
--   --  goR .ShRec.spoke-hub-spoke-pt-reflB m r = fst (spoke-hub-sq-ptB m r)
--   --  goR .ShRec.spoke-hub-sq-ptB m r = snd (spoke-hub-sq-ptB m r) 
--   --  goR .ShRec.sh-comp-pt-inv-fill-capB m m' = fst (sh-comp-pt-inv-fillB m m')
--   --  goR .ShRec.sh-comp-pt-inv-fillB m m' = snd (sh-comp-pt-inv-fillB m m')
--   --  goR .ShRec.sh-comp-center-reflB = {!!}
--   --  goR .ShRec.sh-comp-sqL-ptB = {!!}
--   --  goR .ShRec.sh-comp-sqR-ptB = {!!}
   
--   --  go : Sh → B
--   --  go = ShRec.go goR



--   -- record ShRec-spoke {ℓ} (B : Type ℓ) : Type ℓ where
--   --  field
--   --   σB : A → B
--   --   hubB : (m : obj n) (r : unit ≋ m) → B
--   --   spokeB : (m : obj n) (r : unit ≋ m) (s : S₊ (suc n)) →
--   --     hubB m r ≡ σB (evS₊ m s)

--   --  goR : ShElim (λ _ → B)
--   --  goR .ShElim.σB = σB
--   --  goR .ShElim.hubB = hubB
--   --  goR .ShElim.spokeB = spokeB
--   --  goR .ShElim.spoke-hub-spokeB m r s =
--   --      sym ( spokeB m r s) ∙∙ spokeB m r (ptSn (suc n)) ∙∙ cong σB (evS₊pt m) 
--   --  goR .ShElim.spoke-hub-sqB m r s =
--   --    symP (doubleCompPath-filler _ _ _)
--   --  goR .ShElim.sh-comp-centerB = {!!}
--   --  goR .ShElim.sh-comp-sqLB = {!!}
--   --  goR .ShElim.sh-comp-sqRB = {!!}
  
--   --  go : ∀ x → B
--   --  go = ShElim.go goR


-- --   -- δ : Sh → A
-- --   -- δ = ShRec-spoke.go w
-- --   --  where
-- --   --  w : ShRec-spoke A
-- --   --  w .ShRec-spoke.σB a = a
-- --   --  w .ShRec-spoke.hubB _ _ = ptA
-- --   --  w .ShRec-spoke.spokeB m r s = {!!}
  
-- --   record ShElim-spoke {ℓ} (B : Sh → Type ℓ) : Type ℓ where
-- --    field
-- --     σB : ∀ a → B (σ a)
-- --     hubB : ∀ m r → B (hub m r)
-- --     spokeB : ∀ m r s →
-- --      PathP (λ i → B (spoke m r s i))
-- --        (hubB m r) (σB (evS₊ m s))

-- --    spokeBpathP : ∀ (m : obj n)
-- --     (r : unit ≋ m) (s : S₊ (suc n)) →
-- --       PathP (λ i → B (spoke-hub-spoke-pt m r s i))
-- --        (σB (evS₊ m s))
-- --       (σB ptA)
-- --    spokeBpathP m r s i =  
-- --       comp (λ j → B (spoke-hub-sq m r s (~ j) i))
-- --        (λ j → λ { (i = i0) → spokeB m r s j
-- --                 ; (i = i1) → σB (sym (evS₊pt m) (~ j))
-- --                 })
-- --         (spokeB m r (ptSn (suc n)) i)

-- --    goR : ShElim B
-- --    goR .ShElim.σB = σB
-- --    goR .ShElim.hubB = hubB
-- --    goR .ShElim.spokeB = spokeB
-- --    goR .ShElim.spoke-hub-spokeB = spokeBpathP
-- --    goR .ShElim.spoke-hub-sqB m r s j i =
-- --      fill (λ j → B (spoke-hub-sq m r s (~ j) (i)))
-- --      (λ j → λ {
-- --         (i = i0) → spokeB m r s j
-- --        ;(i = i1) → σB (sym (evS₊pt m) (~ j))
-- --          })
-- --       (inS (spokeB m r (ptSn (suc n)) i)) (~ j) 
   
-- --    go : ∀ x → B x
-- --    go = ShElim.go goR

  record ShElim-sn {ℓ} (B : Sh → Type ℓ) : Type ℓ where
   field
    σB : ∀ a → B (σ a)
    hubB : ∀ m r → B (hub m r)
    spokeB : ∀ m r s →
     PathP (λ i → B (spoke m r s i))
       (hubB m r) (σB (evS₊ m s))

    hLevelB : ∀ x → isOfHLevel (suc (suc (suc n))) (B x)

   spoke-hub-spokeB : ∀ m r s →
    PathP (λ i → B (spoke-hub-spoke-pt m r s i))
      (σB (evS₊ m s)) (σB ptA)
   spoke-hub-spokeB m r s i = 
     comp (λ j → B (spoke-hub-sq m r s (~ j) i))
       (λ j → λ { (i = i0) → spokeB m r s j
                ; (i = i1) → σB (sym (evS₊pt m) (~ j))
                })
        (spokeB m r (ptSn (suc n)) i)

   spoke-hub-sqB : ∀ m r s →
      SquareP (λ i i₁ →
        B (spoke-hub-sq m r s i i₁))
        (spoke-hub-spokeB m r s)
        (spokeB m r (ptSn (suc n)))
        (symP (spokeB m r s))
        (cong σB (sym (evS₊pt m)))
   spoke-hub-sqB m r s j i =
     fill (λ j → B (spoke-hub-sq m r s (~ j) (i)))
     (λ j → λ {
        (i = i0) → spokeB m r s j
       ;(i = i1) → σB (sym (evS₊pt m) (~ j))
         })
      (inS (spokeB m r (ptSn (suc n)) i)) (~ j) 




   spoke-hub-spoke-pt-reflB  : (m : obj n) (m' : unit ≋ m) →
      SquareP (λ i j → B (spoke-hub-spoke-pt-refl m m' i j))
      (spoke-hub-spokeB m m' (ptSn (suc n))) (cong σB (evS₊pt m)) refl
      refl
   spoke-hub-spoke-pt-reflB m m' i j =
      comp (λ z → B (spoke-hub-sq-pt m m' i (~ z) j))
        ((λ z → 
               λ { 
                   (i = i1) → σB (evS₊pt m (z ∧ j))
                 ; (j = i0) → spokeB m m' (ptSn (suc n)) (z ∨ i)
                 ; (j = i1) → σB (evS₊pt m z)}))
        (spokeB m m' (ptSn (suc n)) (j ∨ i))

   spoke-hub-sq-ptB : (m : obj n) (r : unit ≋ m) →
      CubeP (λ i j k → B (spoke-hub-sq-pt m r i j k))
      (spoke-hub-sqB m r (ptSn (suc n)))
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (~ i ∧ i₁)))
      (spoke-hub-spoke-pt-reflB m r) (λ i j → spokeB m r (ptSn (suc n)) (j ∨ i))
      (λ i j → spokeB m r (ptSn (suc n)) (~ j ∨ i)) refl
   spoke-hub-sq-ptB m r i k j =
     fill ((λ z → B (spoke-hub-sq-pt m r i (~ z) j)))
      ((λ z → 
               λ { (j = i0) → spokeB m r (ptSn (suc n)) (z ∨ i)
                 ; (i = i1) → σB (evS₊pt m (z ∧ j))
                 ; (j = i0) → spokeB m r (ptSn (suc n)) (z ∨ i)
                 ; (j = i1) → σB (evS₊pt m z)}))
                  (inS (spokeB m r (ptSn (suc n)) (j ∨ i))) (~ k)


   sh-comp-pt-inv-fill-capB : (m m' : obj n) →
      SquareP (λ i j → B (sh-comp-pt-inv-fill-cap m m' i j))
      (cong σB (λ i → evS₊pt m i)) (cong σB (λ i → evS₊pt m' (~ i)))
      (cong σB (λ i → evS₊pt m i)) (cong σB (λ i → evS₊pt m' (~ i)))
   sh-comp-pt-inv-fill-capB m m' i j =
     comp (λ z → B (sh-comp-pt-inv-fill m m' (~ z) i j))
      (λ z → 
               λ { (i = i0) → σB (evS₊pt m (j ∨ ~ z))
                 ; (i = i1) → σB (evS₊pt m' (~ j ∨ ~ z))
                 ; (j = i0) → σB (evS₊pt m (~ z ∨ i))
                 ; (j = i1) → σB (evS₊pt m' (~ z ∨ ~ i))}) (σB ptA)
                 

   sh-comp-pt-inv-fillB : (m m' : obj n) →
      CubeP (λ i j k → B (sh-comp-pt-inv-fill m m' i j k))
      (sh-comp-pt-inv-fill-capB m m') refl
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m (i₁ ∨ i)))
      (congP (λ z → cong σB) (λ i i₁ → evS₊pt m' (~ i₁ ∨ i)))
   sh-comp-pt-inv-fillB m m' z i j =
     fill (λ z → B (sh-comp-pt-inv-fill m m' (~ z) i j))
      (λ z → 
               λ { (i = i0) → σB (evS₊pt m (j ∨ ~ z))
                 ; (i = i1) → σB (evS₊pt m' (~ j ∨ ~ z))
                 ; (j = i0) → σB (evS₊pt m (~ z ∨ i))
                 ; (j = i1) → σB (evS₊pt m' (~ z ∨ ~ i))}) (inS (σB ptA))
                  (~ z)

   CompPartΣ : (x y : obj (suc n)) (s : S₊ (suc n)) → Type ℓ
   CompPartΣ x y s =
     Σ (Σ[ center ∈
         PathP (λ i → B (sh-comp-center x y s i)) (σB ptA)
         (σB (evS₊ (middle (x ⊙ y) .fst) s)) ]
       SquareP (λ i j → B (sh-comp-sqL x y s i j))
      (spoke-hub-spokeB (middle x .fst) (middle x .snd .fst) s)
      center
      (spoke-hub-spokeB (middle x .fst) (middle x .snd .snd) s)
      (symP
       (spoke-hub-spokeB (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .fst)
        s))) λ (center , _) → 
        SquareP (λ i j → B (sh-comp-sqR x y s i j))
      (spoke-hub-spokeB (middle y .fst) (middle y .snd .snd) s)
      center
      (spoke-hub-spokeB (middle y .fst) (middle y .snd .fst) s)
      (symP
       (spoke-hub-spokeB (middle (x ⊙ y) .fst) (middle (x ⊙ y) .snd .snd)
        s))


   hLevelCompPartΣ : ∀ x y (s : S₊ (suc n)) →
     isOfHLevel (suc n) (CompPartΣ x y s)
   hLevelCompPartΣ x y s =
      isOfHLevelΣ (suc n) (isContr→isOfHLevel (suc n) (isContrSinglP _ _))
       λ _ → isOfHLevelPathP' (suc n)
               (isOfHLevelPathP' (suc (suc n)) (hLevelB _) _ _ ) _ _


   CompPartΣ' : (x y : obj (suc n)) → CompPartΣ x y (ptSn (suc n)) → Type ℓ
   CompPartΣ' x y ((p , s) , s') =
     Σ[ centerP ∈ (SquareP (λ i j → B (sh-comp-center-refl x y i j))
      p
      (cong σB (λ i → (sym $ evS₊pt (middle (x ⊙ y) .fst)) i)) refl refl) ]
       CubeP (λ i j k → B (sh-comp-sqL-pt x y i j k))
      s
      (sh-comp-pt-inv-fill-capB (middle x .fst) (middle (x ⊙ y) .fst))
      (spoke-hub-spoke-pt-reflB (middle x .fst) (middle x .snd .fst))
      centerP
      (spoke-hub-spoke-pt-reflB (middle x .fst) (middle x .snd .snd))
      (congP (λ z → symP)
       (spoke-hub-spoke-pt-reflB (middle (x ⊙ y) .fst)
        (middle (x ⊙ y) .snd .fst)))
       × CubeP (λ i j k → B (sh-comp-sqR-pt x y i j k))
      s'
      (sh-comp-pt-inv-fill-capB (middle y .fst) (middle (x ⊙ y) .fst))
      (spoke-hub-spoke-pt-reflB (middle y .fst) (middle y .snd .snd))
      centerP
      (spoke-hub-spoke-pt-reflB (middle y .fst) (middle y .snd .fst))
      (congP (λ z → symP)
       (spoke-hub-spoke-pt-reflB (middle (x ⊙ y) .fst)
        (middle (x ⊙ y) .snd .snd)))

   CompPartΣP : (x y : obj (suc n)) → singl (CompPartΣ x y (ptSn (suc n))) 
   CompPartΣP x y = _ , λ i' → Σ (Σ[ center ∈
         PathP (λ i → (B (sh-comp-center-refl x y i' i)))
           (σB ptA)
         (σB (evS₊ (middle (x ⊙ y) .fst) (ptSn (suc n)))) ]
       SquareP (λ i j → B (sh-comp-sqL-pt x y i' i j))
      ((spoke-hub-spoke-pt-reflB (middle x .fst) (middle x .snd .fst)) i')
      center
      ((spoke-hub-spoke-pt-reflB (middle x .fst) (middle x .snd .snd)) i')
      ((symP
       (spoke-hub-spoke-pt-reflB (middle (x ⊙ y) .fst)
        (middle (x ⊙ y) .snd .fst) i')))) λ (center , _) → 
        SquareP (λ i j → B (sh-comp-sqR-pt x y i' i j))
      ((spoke-hub-spoke-pt-reflB (middle y .fst) (middle y .snd .snd)) i')
      center
      ((spoke-hub-spoke-pt-reflB (middle y .fst) (middle y .snd .fst)) i')
      (symP 
       (spoke-hub-spoke-pt-reflB (middle (x ⊙ y) .fst)
        (middle (x ⊙ y) .snd .snd) i'))

   compPartΣP : ∀ x y → singlP (λ i → snd (CompPartΣP x y) (~ i))
    (((cong σB (λ i → (sym $ evS₊pt (middle (x ⊙ y) .fst)) i)) ,
     (sh-comp-pt-inv-fill-capB (middle x .fst) (middle (x ⊙ y) .fst))) ,
      (sh-comp-pt-inv-fill-capB (middle y .fst) (middle (x ⊙ y) .fst)))
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
   goR .ShElim.hubB = hubB
   goR .ShElim.spokeB = spokeB
   goR .ShElim.spoke-hub-spokeB = spoke-hub-spokeB
   goR .ShElim.spoke-hub-sqB = spoke-hub-sqB
   goR .ShElim.sh-comp-centerB x y s = fst (fst (compPartΣ x y s))
   goR .ShElim.sh-comp-sqLB x y s = snd (fst (compPartΣ x y s))
   goR .ShElim.sh-comp-sqRB x y s = snd (compPartΣ x y s)
   goR .ShElim.spoke-hub-spoke-pt-reflB = spoke-hub-spoke-pt-reflB
   goR .ShElim.spoke-hub-sq-ptB = spoke-hub-sq-ptB
   goR .ShElim.sh-comp-pt-inv-fill-capB = sh-comp-pt-inv-fill-capB
   goR .ShElim.sh-comp-pt-inv-fillB = sh-comp-pt-inv-fillB
   goR .ShElim.sh-comp-center-reflB x y =
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

--   record ShRec-sn {ℓ} (B : Type ℓ) : Type ℓ where
--    field
--     σB : ∀ a → B
--     hubB : ∀ m r → B
--     spokeB : ∀ m r s →
     
--        (hubB m r) ≡ (σB (evS₊ m s))

--     hLevelB : isOfHLevel (suc (suc (suc n))) B

--    goR : ShElim-sn (λ _ → B)
--    goR .ShElim-sn.σB = σB
--    goR .ShElim-sn.hubB = hubB
--    goR .ShElim-sn.spokeB = spokeB
--    goR .ShElim-sn.hLevelB _ = hLevelB
   
--    go : Sh → B
--    go = ShElim-sn.go goR

--   record ShElim-n {ℓ} (B : Sh → Type ℓ) : Type ℓ where
--    field
--     σB : ∀ a →  (B (σ a))

--     hLevelB : ∀ x → isOfHLevel (suc (suc n)) (B x)



--    spokeBpathP' : ∀ m r → _
--    spokeBpathP' m r i = transp
--     (λ u → B (spoke m r (ptSn (suc n)) (~ u ∨  i))) i
--       (σB (evS₊ m (ptSn (suc n))))
      
--    spokeBpathP : ∀ m r → _
--    spokeBpathP m r = 
--          Sn.sphereElim n
--       (λ _ → isOfHLevelPathP' (suc n) (hLevelB _) _ _)
--       (spokeBpathP' m r)

--    goR : ShElim-sn B
--    goR .ShElim-sn.σB = σB
--    goR .ShElim-sn.hubB m r =
--      transport⁻ (λ i → B (spoke m r (ptSn (suc n)) i))
--        (σB (evS₊ m (ptSn (suc n))))
--    goR .ShElim-sn.spokeB = spokeBpathP
--    goR .ShElim-sn.hLevelB = isOfHLevelSuc (suc (suc n)) ∘ hLevelB

--    go : ∀ x → (B x)
--    go = ShElim-sn.go goR

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

--   Trunc-Sh : Iso (∥ A ∥ (2 ℕ.+ n)) (∥ Sh ∥ (2 ℕ.+ n))
--   Trunc-Sh = w
--    where

--    ww : ShElim-n (λ _ → ∥ A ∥ (2 ℕ.+ n))
--    ww .ShElim-n.σB = ∣_∣
--    ww .ShElim-n.hLevelB _ = isOfHLevelTrunc (suc (suc n))

--    w : Iso (∥ A ∥ (2 ℕ.+ n)) (∥ Sh ∥ (2 ℕ.+ n))
--    w .Iso.fun = T.map σ
--    w .Iso.inv = T.rec (isOfHLevelTrunc (suc (suc n))) (ShElim-n.go ww)
--    w .Iso.rightInv = T.elim
--      (λ _ →  isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _)
--       (ShElim-n.go www)
           
--     where
--     www : ShElim-n _
--     www .ShElim-n.σB _ = refl
--     www .ShElim-n.hLevelB _ =
--      isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _
--    w .Iso.leftInv =
--      T.elim
--      (λ _ →  isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _)
--       λ _ → refl

--   -- Trunc-Sh≤ : ∀ m → m ℕ.≤ (2 ℕ.+ n) → Iso (∥ A ∥ m) (∥ Sh ∥ m)
--   -- Trunc-Sh≤ m m≤2+n = w
--   --  where

--   --  w : Iso (∥ A ∥ m) (∥ Sh ∥ m)
--   --  w = compIso {!!} {!!}

--   module _ (hLevelA : isOfHLevel (2 ℕ.+ n) A) where

--    from-Sh : ShElim-n (λ _ → A)
--    from-Sh .ShElim-n.σB a = a
--    from-Sh .ShElim-n.hLevelB _ = hLevelA
   
--    from-Sh-trunc : ∥ Sh ∥ (2 ℕ.+ n) → A
--    from-Sh-trunc = T.rec hLevelA (ShElim-n.go from-Sh)

--    sh-right-inv : section (∣_∣ ∘S σ) from-Sh-trunc
--    sh-right-inv = T.elim
--      (λ _ →  isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _)
--      (ShElim-n.go ww)
--     where
--     ww : ShElim-n _
--     ww .ShElim-n.σB _ = refl
--     ww .ShElim-n.hLevelB _ =
--      isOfHLevelPath (suc (suc n)) (isOfHLevelTrunc (suc (suc n))) _ _ 
    
--    sh-left-inv : retract (λ x → ∣ σ x ∣) from-Sh-trunc
--    sh-left-inv a = refl
   
--    Sh-trunc : Iso A (∥ Sh ∥ (2 ℕ.+ n))
--    Sh-trunc .Iso.fun = ∣_∣ ∘S σ
--    Sh-trunc .Iso.inv = from-Sh-trunc
--    Sh-trunc .Iso.rightInv = sh-right-inv
--    Sh-trunc .Iso.leftInv = sh-left-inv


-- --  --  module _ (x y : _) where
-- --  --   opaque 
-- --  --    evS₊-suc-comp-sq : ∀ (a : S₊ (suc n)) → Square
-- --  --      (cong (fst (HG.∙Π {A = (Sh , σ ptA)} {n = suc (suc n)}
-- --  --        (evS₊-suc x  , evS₊pt-suc _)
-- --  --        (evS₊-suc y  , evS₊pt-suc _))) (merid a))
-- --  --      ((spoke (middle (x ⊙ y) .fst) (fst (snd (middle (x ⊙ y))))
-- --  --           a
-- --  --           ∙∙ (λ _ → σ (evS₊ (middle (x ⊙ y) .fst) a)) ∙∙
-- --  --           (λ i₁ →
-- --  --              spoke (middle (x ⊙ y) .fst) (snd (snd (middle (x ⊙ y)))) a (~ i₁))))
-- --  --      (cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙' sym (spoke _ _ _))
-- --  --      (cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙' sym (spoke _ _ _))
-- --  --    evS₊-suc-comp-sq a =

-- --  --      compPathR→PathP∙∙
-- --  --        (     cong₂ _∙_
-- --  --             (evS₊-suc-sq-hlp x a)
-- --  --             (evS₊-suc-sq-hlp y a) ∙
-- --  --              (λ j → (λ i → evS₊-suc-sq-hlp x a i1 (j ∧ i))
-- --  --                 ∙∙ (λ i → evS₊-suc-sq-hlp x a i1 (i ∨ j))
-- --  --                  ∙∙ evS₊-suc-sq-hlp y a i1 ) ◁

-- --  --          {!!} ∙
-- --  --         λ j →
-- --  --           ((
-- --  --           (cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙'
-- --  --            sym
-- --  --            (spoke (middle (x ⊙ y) .fst) (fst (snd (middle (x ⊙ y))))
-- --  --             (ptSn (suc n))))
-- --  --           )
-- --  --        ∙∙
-- --  --        (λ i → spoke (middle (x ⊙ y) .fst) (fst (snd (middle (x ⊙ y)))) a i) ∙∙
-- --  --        (λ _ → σ (evS₊ (middle (x ⊙ y) .fst) a)) ∙∙
-- --  --        (λ i →
-- --  --           spoke (middle (x ⊙ y) .fst) (snd (snd (middle (x ⊙ y)))) a (~ i))
-- --  --        ∙∙
-- --  --        sym
-- --  --        (
-- --  --           (cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙'
-- --  --            sym
-- --  --            (spoke (middle (x ⊙ y) .fst) (snd (snd (middle (x ⊙ y))))
-- --  --             (ptSn (suc n))))
-- --  --           )))

-- --  --    evS₊-suc-comp : ∀ s →
-- --  --      fst (HG.∙Π {A = (Sh , σ ptA)}
-- --  --        (evS₊-suc x  , evS₊pt-suc _)
-- --  --        (evS₊-suc y  , evS₊pt-suc _)) s ≡
-- --  --        (evS₊-suc (x ⊙ y)) s
-- --  --    evS₊-suc-comp north = cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙' sym (spoke _ _ _)
-- --  --    evS₊-suc-comp south = cong σ (sym (evS₊pt (middle (x ⊙ y) .fst))) ∙' sym (spoke _ _ _)
-- --  --    evS₊-suc-comp (merid a i) j = evS₊-suc-comp-sq a j i

-- --  -- open Sh using (σ)


-- --  -- T0 : Type
-- --  -- T0 = Sh.Sh (suc zero)
-- --  --       (Sh0.Sh)
-- --  --       (σ (obj₋₁-unit))
-- --  --       Sh0.evS₊-suc --(Sh.evS₊-suc zero obj₋₁ obj₋₁-unit obj₋₁-ev obj₋₁-pt)
-- --  --       {!Sh0.evS₊pt-suc!}

-- --  --   where
-- --  --    module Sh0 = Sh zero obj₋₁ obj₋₁-unit obj₋₁-ev obj₋₁-pt

-- --  -- -- Shₙ : ℕ → Type
-- --  -- -- Shₙ-pre : ℕ → Type
-- --  -- -- Shₙ-pre-pt : ∀ n → Shₙ-pre n
-- --  -- -- Shₙ-eval : ∀ n → obj n → S₊ (suc n) → Shₙ-pre n
-- --  -- -- Shₙ-eval-pt : ∀ n → (x : obj n) → Shₙ-eval n x (ptSn (suc n)) ≡ Shₙ-pre-pt n
-- --  -- -- -- Shₙ zero = Sh.Sh zero obj₋₁ obj₋₁-unit obj₋₁-ev obj₋₁-pt  
-- --  -- -- -- Shₙ (suc n) = Sh.Sh (suc n) (Shₙ n)
-- --  -- -- --   (Shₙ-pt n) {!!} {!!}

-- --  -- -- Shₙ n = Sh.Sh n (Shₙ-pre n) (Shₙ-pre-pt n) (Shₙ-eval n) (Shₙ-eval-pt n)


-- --  -- -- Shₙ-pre zero = obj₋₁
-- --  -- -- Shₙ-pre (suc n) = Shₙ n

-- --  -- -- Shₙ-pre-pt zero = obj₋₁-unit
-- --  -- -- Shₙ-pre-pt (suc n) = σ (Shₙ-pre-pt n)

-- --  -- -- -- Shₙ-eval = {!!}

-- --  -- -- Shₙ-eval zero  = obj₋₁-ev
-- --  -- -- Shₙ-eval (suc n) = Sh.evS₊-suc n
-- --  -- --   (Shₙ-pre n) (Shₙ-pre-pt n) (Shₙ-eval n) (Shₙ-eval-pt n)

-- --  -- -- Shₙ-eval-pt zero = obj₋₁-pt
-- --  -- -- Shₙ-eval-pt (suc n) x = {!!}

