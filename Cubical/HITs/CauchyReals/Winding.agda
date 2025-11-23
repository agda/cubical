{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.Winding where

open import Cubical.Foundations.Prelude
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
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyReals.Circle
open import Cubical.HITs.CauchyReals.CircleMore
import Cubical.HITs.S1 as S1
open import Cubical.HITs.Susp
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.Categories.Category

open import Cubical.WildCat.Base

open import Cubical.Algebra.Group.ZAction

open import Cubical.Structures.Pointed
open import Cubical.Structures.Product

import Cubical.Homotopy.Loopspace as Lsp
import Cubical.Homotopy.Group.Base as HG

private
 variable
  ℓ ℓ' : Level


-- module _ (A : MetricSpace ℓ) (B : MetricSpace ℓ') where
 
--  module MA = MetricSpaceStr (snd A)
--  module MB = MetricSpaceStr (snd B)


--  uniformMertric : MetricSpaceStr (UContMap A B)  
--  uniformMertric =
--    {!!} 
--   -- where


uniformMertric : ∀ {ℓ ℓ'}
  → MetricSpace ℓ
  → MetricSpace ℓ'
  → MetricSpace (ℓ-max ℓ ℓ')  
uniformMertric A B =
 (UContMap A B) , mss 
 where
  module MA = MetricSpaceStr (snd A)
  module MB = MetricSpaceStr (snd B)

  mss : MetricSpaceStr (UContMap A B)
  mss .MetricSpaceStr.𝑑[_,_] f g = {!!}
  mss .MetricSpaceStr.isMetric = {!!}

intLoopCircle : ℤ → Circle → Circle
intLoopCircle k = SQ.Rec.go w
  where
  w : Rec Circle
  w .Rec.isSetB = isSetCircle
  w .Rec.f a = [ rat [ k / 1 ] ·ᵣ a ]/
  w .Rec.f∼ a a' (z , p) =
    eq/ _ _ (k ℤ.· z , sym (𝐑'.·DistR- _ _ _)
     ∙ cong₂ _·ᵣ_ refl p
     ∙ sym (rat·ᵣrat _ _))


Circle→distCircle∘injCircle-groupHom :
 ∀ x y →
  Circle→distCircle
       (injCircle x) ℝS¹.+ Circle→distCircle
       (injCircle y)
   ≡
   Circle→distCircle
       (injCircle (x +ᵣ y))
Circle→distCircle∘injCircle-groupHom x y =
  distCircle≡ 
    ((circle+-X (Circle→distCircle (injCircle x))
       (Circle→distCircle (injCircle y)))
     ∙∙ sym (cosOfSum _ _)
     ∙∙ cong cos (sym (·DistR+ _ _ _)))
    (circle+-Y (Circle→distCircle (injCircle x))
       (Circle→distCircle (injCircle y))
        ∙ solve! ℝring
     ∙∙ sym (sinOfSum _ _)
     ∙∙ cong sin (sym (·DistR+ _ _ _)))


GroupHom-Circle→distCircle∘injCircle :
  IsGroupHom (snd +Groupℝ) (Circle→distCircle ∘ injCircle)
   (snd (AbGroup→Group ℝS¹AbGroup))
GroupHom-Circle→distCircle∘injCircle =
 makeIsGroupHom λ x y → sym (Circle→distCircle∘injCircle-groupHom x y)

opaque
 intLoop' : ℤ → distCircle → distCircle
 intLoop' k x = k ℤ[ AbGroup→Group ℝS¹AbGroup ]· x

 ℤ·ᵣ-hlp : ∀ k x → k ℤ[ ℝ , snd +Groupℝ ]· x ≡ rat [ k / 1 ] ·ᵣ x
 ℤ·ᵣ-hlp (pos zero) x = solve! ℝring
 ℤ·ᵣ-hlp (pos (suc n)) x =
  cong₂ _+ᵣ_ (sym (·IdL _)) (ℤ·ᵣ-hlp (pos n) x)
  ∙ sym (·DistR+ _ _ _) ∙ cong (_·ᵣ _) (+ᵣ-rat  _ _ ∙
   cong rat (ℚ.ℕ+→ℚ+ 1 n))
 ℤ·ᵣ-hlp (ℤ.negsuc zero) x = -ᵣ≡[-1·ᵣ] x
 ℤ·ᵣ-hlp (ℤ.negsuc (suc n)) x =
    cong₂ _+ᵣ_ (-ᵣ≡[-1·ᵣ] x) (ℤ·ᵣ-hlp (ℤ.negsuc n) x)
  ∙ sym (·DistR+ _ _ _)
  ∙ cong (_·ᵣ _)
     (+ᵣ-rat _ _ ∙ cong rat ((ℚ.ℤ+→ℚ+ -1 (ℤ.negsuc n))
      ∙ cong [_/ 1 ] (ℤ.+Comm -1 (ℤ.negsuc n)) ))
 
 intLoop'hom : ∀ x k →
   Circle→distCircle (injCircle (rat [ k / 1 ] ·ᵣ x)) ≡
    (k ℤ[ AbGroup→Group ℝS¹AbGroup ]·
     (Circle→distCircle (injCircle x)))
 intLoop'hom x k =
     sym (cong (Circle→distCircle ∘ injCircle) (ℤ·ᵣ-hlp k x))
   ∙ homPresℤ· (_ , GroupHom-Circle→distCircle∘injCircle) x k


 intLoop : ℤ → distCircle → distCircle
 intLoop k =
      Circle→distCircle
   ∘S intLoopCircle k
   ∘S invEq Circle≃distCircle


 intLoop≡intLoop : ∀ k x →
   intLoop k x ≡ intLoop' k x 
 intLoop≡intLoop k x = 
    SQ.ElimProp.go w (invEq Circle≃distCircle x)
      ∙ cong (intLoop' k) (secEq Circle≃distCircle x)
  where
  w : ElimProp
       (λ z →
          Circle→distCircle (intLoopCircle k z) ≡
          intLoop' k (Circle→distCircle z))
  w .ElimProp.isPropB _ = isSetDistCircle _ _
  w .ElimProp.f x = intLoop'hom x k


 intLoop-unwind : ∀ k →
   ∀ x → intLoop k (Circle→distCircle (injCircle x)) ≡ intLoop k circle0 ℝS¹.+
     Circle→distCircle (injCircle (rat [ k / 1 ] ·ᵣ x))
 intLoop-unwind k x =
     h _
   ∙ cong (intLoop k circle0 ℝS¹.+_) (sym (intLoop'hom x k))

  where
  h : ∀ x → intLoop k x ≡
      intLoop k circle0 ℝS¹.+
      (k ℤ[ AbGroup→Group ℝS¹AbGroup ]· x)
  h x = intLoop≡intLoop k x ∙
       sym (ℝS¹.+IdL _)
     ∙ cong₂ (ℝS¹._+_) (sym (rUnitℤ· (AbGroup→Group ℝS¹AbGroup) k)
       ∙ sym (intLoop≡intLoop k circle0)) refl
    


∃ℚ₊SmallerThanℝ₊
           : (x : ℝ₊) → ∃-syntax ℚ₊ (λ q → rat (fst q) <ᵣ fst x)
∃ℚ₊SmallerThanℝ₊ (x , 0<x) =
 PT.map
  (λ (q , 0<q , q<x) →
    (q , ℚ.<→0< q (<ᵣ→<ℚ _ _ 0<q)) ,
    q<x)
  (denseℚinℝ _ _ 0<x)

∃rationalApprox∈Interval : ∀ a b → a <ᵣ b → ∀ u
   → u ∈ intervalℙ a b → (ε : ℚ₊) →
    ∃[ q ∈ ℚ ] (absᵣ (rat q -ᵣ u) <ᵣ rat (fst ε)) × (rat q ∈ intervalℙ a b)
∃rationalApprox∈Interval a b a<b u u∈ ε =
 PT.rec squash₁
  (⊎.rec
    (λ u<b →
      PT.map (map-snd
         λ {q} ( <q , q<) →
          isTrans≤<ᵣ _ _ _
            (isTrans≤ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                (absᵣPos _ (x<y→0<y-x _ _ <q))
                (a≤c+b⇒a-c≤b _ _ _ (<ᵣWeaken≤ᵣ _ _ q<)))
              (min≤ᵣ (rat (fst (/2₊ ε))) (b -ᵣ u)))
           (<ℚ→<ᵣ (fst (/2₊ ε)) _ (x/2<x ε))
           , (isTrans≤ᵣ _ _ _ (fst u∈) (<ᵣWeaken≤ᵣ _ _ <q) )
           , isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ q<)
             (b≤c-b⇒a+b≤c _ _ _ (isTrans≡≤ᵣ _ _ _ (minᵣComm _ _) (min≤ᵣ _ _))))
        (denseℚinℝ u ((u +ᵣ minᵣ (rat (fst (/2₊ ε))) (b -ᵣ u)))
          (isTrans≡<ᵣ _ _ _
            (sym (+IdR _))
              (<ᵣ-o+ _ _ _
               (snd (minᵣ₊ (ℚ₊→ℝ₊ (/2₊ ε)) (_ , x<y→0<y-x _ _ u<b)))))))
    (λ a<u →
      PT.map (map-snd
         λ {q} ( <q , q<) →
           isTrans≤<ᵣ _ _ _
             (isTrans≤ᵣ _ _ _
               ((isTrans≡≤ᵣ _ _ _
                 (minusComm-absᵣ _ _ ∙
                  absᵣPos _ (x<y→0<y-x _ _ q<))
                 (a-b≤c⇒a-c≤b _ _ _ (<ᵣWeaken≤ᵣ _ _ <q))))
               (min≤ᵣ (rat (fst (/2₊ ε))) (u -ᵣ a)))
             (<ℚ→<ᵣ (fst (/2₊ ε)) _ (x/2<x ε))
            ,
              ((isTrans≤ᵣ _ _ _
             (a≤b-c⇒c≤b-a _ _ _
              (isTrans≡≤ᵣ _ _ _ (minᵣComm _ _) (min≤ᵣ _ _)))
             (<ᵣWeaken≤ᵣ _ _ <q))
             , (isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ q<) (snd u∈)))
             )
        (denseℚinℝ (u -ᵣ minᵣ (rat (fst (/2₊ ε))) (u -ᵣ a)) u
                     (isTrans<≡ᵣ _ _ _
                       (<ᵣ-o+ _ _ _
                        (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _
                            (snd (minᵣ₊ (ℚ₊→ℝ₊ (/2₊ ε))
                             (_ , x<y→0<y-x _ _ a<u)))) (-ᵣ-rat 0))) (+IdR _))))
     )
   (Dichotomyℝ' a u b a<b)
 
IsUContMap≡ : ∀ {ℓ} (A : MetricSpace ℓ) 
  a b → a <ᵣ b →
   (f₀ f₁ : UContMap (Interval[ a , b ]MetricSpace) A)
   → (∀ q q∈ → fst f₀ (rat q , q∈)
             ≡ fst f₁ (rat q , q∈)) 
   → ∀ x x∈ → (fst f₀ (x , x∈)) ≡ (fst f₁ (x , x∈))
IsUContMap≡ (A , AM) a b a<b f₀ f₁ p x x∈ =
   M.𝑑-zero→≡ _ _
    (invEq (eqℝ≃< _ _) (PT.rec (isProp<ᵣ _ _) (idfun _) ∘ w))


 where
 module M = MetricSpaceStr AM
 
 w : (ε : ℚ₊) →
      ∥ absᵣ (0 -ᵣ M.𝑑[ fst f₀ (x , x∈) , fst f₁ (x , x∈) ]) <ᵣ rat (fst ε) ∥₁
 w ε = do
  (δ₀ , δ₀<) ← PT.map (_$ /2₊ ε) (snd f₀)
  (δ₁ , δ₁<) ← PT.map (_$ /2₊ ε) (snd f₁)
  (q , ∣q-x|<δ₀⊔δ₁ , q∈) ← ∃rationalApprox∈Interval a b a<b x x∈
    (ℚ.min₊ δ₀ δ₁)
  ∣ isTrans≡<ᵣ _ _ _
    (cong absᵣ (+IdL _) ∙ sym (-absᵣ _) ∙ absᵣNonNeg _ (M.𝑑-nonNeg _ _))
     (isTrans≤<ᵣ _ _ _
       (M.𝑑-triangle _ (fst f₀ (rat q , q∈)) _ )
       (isTrans<≡ᵣ _ _ _
         (<ᵣMonotone+ᵣ _ _ _ _
          (δ₀< _ _ (isTrans<≤ᵣ _ _ _
            (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) ∣q-x|<δ₀⊔δ₁)
             (
              (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst (δ₀ )) (fst (δ₁ ))))
               )) )
          ((isTrans≡<ᵣ _ _ _
           (cong (M.𝑑[_, fst f₁ (x , x∈) ])
            (p q q∈))
            ((δ₁< _ _ (isTrans<≤ᵣ _ _ _
            (∣q-x|<δ₀⊔δ₁)
             ((≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst (δ₀ )) (fst (δ₁ ))))
               )) )))))
         (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst ε))))) ∣₁

opaque
 IsUContMap≡With<cases : ∀ {ℓ} x₀ (A : MetricSpace ℓ) 
   a b → a <ᵣ b →
    (f₀ f₁ : UContMap (Interval[ a , b ]MetricSpace) A)
    → (∀ x x∈ → (x ≤ᵣ x₀) ⊎ (x₀ ≤ᵣ x) → fst f₀ (x , x∈) ≡ fst f₁ (x , x∈)) 
    → ∀ x x∈ → (fst f₀ (x , x∈)) ≡ (fst f₁ (x , x∈))
 IsUContMap≡With<cases x₀ A a b a<b f₀ f₁ p x x∈ =
  cong (fst f₀) (Σ≡Prop (∈-isProp (intervalℙ _ _)) (sym (𝐑'.minusPlus _ _)))
   ∙∙ w ∙∙
   cong (fst f₁) (Σ≡Prop (∈-isProp (intervalℙ _ _)) ((𝐑'.minusPlus _ _)))


  where

  f-cont-Δ : (f : UContMap (Interval[ a , b ]MetricSpace) A) →
       UContMap Interval[ a -ᵣ x₀ , b -ᵣ x₀ ]MetricSpace A
  f-cont-Δ f₀ = ((λ (x , x∈) → fst f₀ (x +ᵣ x₀ ,
          isTrans≡≤ᵣ _ _ _ (sym (𝐑'.minusPlus _ _))
            (≤ᵣ-+o _ _ x₀ (fst x∈)) ,
             isTrans≤≡ᵣ _ _ _
               (≤ᵣ-+o _ _ x₀ (snd x∈))
               (𝐑'.minusPlus _ _))) ,
                  PT.map
                    (λ X →
                     map-snd
                      (λ {δ} Y (u , u∈) (v , v∈) δ< →
                        (Y (u +ᵣ x₀ ,
                            isTrans≡≤ᵣ _ _ _ (sym (𝐑'.minusPlus _ _))
                              (≤ᵣ-+o _ _ x₀ (fst u∈)) ,
                             isTrans≤≡ᵣ _ _ _
                             (≤ᵣ-+o _ _ x₀ (snd u∈))
                             (𝐑'.minusPlus _ _)  )
                             (v +ᵣ x₀ ,
                             isTrans≡≤ᵣ _ _ _ (sym (𝐑'.minusPlus _ _))
                              (≤ᵣ-+o _ _ x₀ (fst v∈)) ,
                             isTrans≤≡ᵣ _ _ _
                             (≤ᵣ-+o _ _ x₀ (snd v∈))
                             (𝐑'.minusPlus _ _))
                           (isTrans≡<ᵣ _ _ _
                             (cong absᵣ (solve! ℝring))
                            δ<)))
                      ∘ X)
                    (snd f₀))

  w : fst (f-cont-Δ f₀)
       (x -ᵣ x₀ , ≤ᵣ-+o a x (-ᵣ x₀) (fst x∈) , ≤ᵣ-+o x b (-ᵣ x₀) (snd x∈))
       ≡
       fst (f-cont-Δ f₁)
       (x -ᵣ x₀ , ≤ᵣ-+o a x (-ᵣ x₀) (fst x∈) , ≤ᵣ-+o x b (-ᵣ x₀) (snd x∈))
  w = IsUContMap≡ A (a -ᵣ x₀) (b -ᵣ x₀) (<ᵣ-+o _ _ _ a<b)
        (f-cont-Δ f₀) (f-cont-Δ f₁)

        (λ q q∈ →
          p (rat q +ᵣ x₀)
           _ (⊎.map
                (flip (isTrans≤≡ᵣ _ _ _) (+IdL _) ∘S ≤ᵣ-+o _ _ x₀ ∘S ≤ℚ→≤ᵣ q 0)
                (isTrans≡≤ᵣ _ _ _ (sym (+IdL _))  ∘S ≤ᵣ-+o _ _ x₀ ∘S ≤ℚ→≤ᵣ 0 q)
               (ℚ.≤cases q 0) ))
        (x -ᵣ x₀)
        (≤ᵣ-+o _ _ _ (fst x∈) , ≤ᵣ-+o _ _ _ (snd x∈))



IsIsometryℝS¹+ : ∀ a → IsIsometry
 distCircleMetricSpaceStr
 (a ℝS¹.+_)
IsIsometryℝS¹+ a x y =
 sym ((cong₂ M.𝑑[_,_] (ℝS¹.+Comm _ _) (ℝS¹.+Comm _ _))
     ∙ cong (fst ∘ nth-rootNonNeg 2)
     (ℝ₀₊≡ ( cong₂ _+ᵣ_
       ((x^²=x·x _) ∙ sym (x·x≡∣x∣·∣x∣ _))
       ((x^²=x·x _) ∙ sym (x·x≡∣x∣·∣x∣ _))  
       ∙  sym (rotationEquivPresDist x y a) ∙
       cong₂ _+ᵣ_ (x·x≡∣x∣·∣x∣ _ ∙ sym (x^²=x·x _))
        (x·x≡∣x∣·∣x∣ _ ∙ sym (x^²=x·x _))) ))

 where
  module M = MetricSpaceStr distCircleMetricSpaceStr



IsUContMapℝS¹+ : ∀ a → IsUContMap
 distCircleMetricSpaceStr
 (a ℝS¹.+_)
 distCircleMetricSpaceStr
IsUContMapℝS¹+ a ε = ε ,
  λ x y 𝑑<ε → isTrans≡<ᵣ _ _ _
    (sym (IsIsometryℝS¹+ a x y))
    𝑑<ε 
 where
  module M = MetricSpaceStr distCircleMetricSpaceStr


-- ∣sin[x]∣≤sin∣x∣ : ∀ x → absᵣ (sin x) ≤ᵣ sin (absᵣ x)
-- ∣sin[x]∣≤sin∣x∣ = {!!}

π-number/4₊ : ℝ₊
π-number/4₊ = π-number/2₊ ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ] , _)


cos[π/4]≡sin[π/4] : cos (fst π-number/4₊) ≡ sin (fst π-number/4₊)
cos[π/4]≡sin[π/4] = cos[x]=-sin[x-π/2] _ ∙
  sin-odd _ ∙ cong sin (-[x-y]≡y-x _ _
    ∙ cong (_-ᵣ fst π-number/4₊)
     ((sym (𝐑'.·IdR' _ _ (sym (rat·ᵣrat 2 [ 1 / 2 ]) ∙ cong rat (ℚ.x·invℚ₊[x] 2))
       ) ∙ ·ᵣAssoc _ _ _ ∙
        cong₂ _·ᵣ_ (·ᵣComm _ _ ∙ sym (x+x≡2x _)) refl ) ∙ ·DistR+ _ _ _)
     ∙ 𝐑'.plusMinus _ _)

π-number/4≤π-number/2 : fst π-number/4₊ <ᵣ π-number/2
π-number/4≤π-number/2 =
  isTrans<≡ᵣ _ _ _
    (<ᵣ-o·ᵣ _ _ π-number/2₊
     decℚ<ᵣ?)
   (·IdR _)

cos[π/4]=√½ : cos (fst π-number/4₊) ≡ fst √½
cos[π/4]=√½ =
 cong fst (invEq (equivAdjointEquiv (_ , isEquiv-₊^ⁿ 2)
   {a = _ , 0≤x<π/2→0<cos[x] (fst π-number/4₊)
     (<ᵣWeaken≤ᵣ _ _ (snd π-number/4₊))
     π-number/4≤π-number/2})
  (ℝ₊≡ w))
 where
  w : (cos (fst π-number/4₊) ^ⁿ 2) ≡ rat [ 1 / 2 ]
  w = (sym (𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
    ∙ sym (·ᵣAssoc _ _ _)) ∙ cong ((rat [ 1 / 2 ]) ·ᵣ_) (sym (x+x≡2x _)
    ∙ cong₂ _+ᵣ_ (cong (_^ⁿ 2) cos[π/4]≡sin[π/4])
      refl ∙ sin²+cos²=1 (fst π-number/4₊)) ∙ ·IdR _

sin[π/4]=√½ : sin (fst π-number/4₊) ≡ fst √½
sin[π/4]=√½ = sym cos[π/4]≡sin[π/4] ∙ cos[π/4]=√½

-- TODO: strenghten by using Integral'-<

π-number/4≤1 : fst π-number/4₊ ≤ᵣ 1
π-number/4≤1 =
  invEq (z≤x≃y₊·z≤y₊·x _ _ √½) $ isTrans≤≡ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _
     (cong (fst √½ ·ᵣ_) (sym (cong (_-ᵣ fst π-number/4₊)
     ((sym (𝐑'.·IdR' _ _ (sym (rat·ᵣrat 2 [ 1 / 2 ]) ∙ cong rat (ℚ.x·invℚ₊[x] 2))
       ) ∙ ·ᵣAssoc _ _ _ ∙
        cong₂ _·ᵣ_ (·ᵣComm _ _ ∙ sym (x+x≡2x _)) refl ) ∙ ·DistR+ _ _ _)
     ∙ 𝐑'.plusMinus _ _)))
     (Integral'-≤ (fst π-number/4₊) π-number/2
      (<ᵣWeaken≤ᵣ _ _ (π-number/4≤π-number/2)) (const (fst √½)) sin
       _
        (cos (fst π-number/4₊) -ᵣ cos π-number/2)
         (λ x x∈ →
          isTrans≡≤ᵣ _ _ _  (sym (sin[π/4]=√½))
            (sin-firstQuarter-Monotone _ _
             (<ᵣWeaken≤ᵣ _ _ (snd π-number/4₊) ,
              (<ᵣWeaken≤ᵣ _ _ (π-number/4≤π-number/2)))
              ((isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd π-number/4₊)) (fst x∈)) ,
               (snd x∈)) (fst x∈)) )
      ((Integral'Const _ _ ((<ᵣWeaken≤ᵣ _ _ (π-number/4≤π-number/2)))  _))
      (invEq (clampᵣ-IntegralOf (fst π-number/4₊) π-number/2
      (<ᵣWeaken≤ᵣ _ _ (π-number/4≤π-number/2)) sin _)
       (∫sin (fst π-number/4₊) π-number/2
        (<ᵣWeaken≤ᵣ _ _ (π-number/4≤π-number/2))))
      ))
      (cong₂ _-ᵣ_ cos[π/4]=√½ cos[π/2]≡0 ∙ 𝐑'.+IdR' _ _ (-ᵣ-rat 0) ∙
       sym (·IdR _))

 
π-number/2≤2 : π-number/2  ≤ᵣ 2
π-number/2≤2 = (invEq (z≤x≃y₊·z≤y₊·x _ _
   (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)))
    (subst2 _≤ᵣ_ (·ᵣComm _ _)
     (decℚ≡ᵣ? ∙ rat·ᵣrat _ 2)
     π-number/4≤1)) 

π-number≤4 : π-number  ≤ᵣ 4
π-number≤4 = 
 isTrans≤≡ᵣ _ _ _
  (fst (z≤x≃y₊·z≤y₊·x _ _ 2) π-number/2≤2)
   (sym (rat·ᵣrat _ _))

2π-number≤8 : 2 ·ᵣ π-number  ≤ᵣ 8
2π-number≤8 =  isTrans≤≡ᵣ _ _ _
  (fst (z≤x≃y₊·z≤y₊·x _ _ 2) π-number≤4)
   (sym (rat·ᵣrat _ _))

x₊²+y₊²<[x₊+y₊]² : (x y : ℝ₊)
 → ( fst x ^ⁿ 2) +ᵣ ( fst y ^ⁿ 2) <ᵣ ((fst x +ᵣ fst y)  ^ⁿ 2)
x₊²+y₊²<[x₊+y₊]² x y =
  0<y-x→x<y _ _ (isTrans<≡ᵣ _ _ _
   (snd ((x ₊·ᵣ y) ₊+ᵣ (x ₊·ᵣ y)) )
   (solve! ℝring ∙ cong₂ _-ᵣ_ (sym (x^²=x·x _))
    (cong₂ _+ᵣ_ (sym (x^²=x·x _)) (sym (x^²=x·x _)))))

IsUContMap-ℝ→distCircle : IsUContMap (ℝMetricSpace .snd)
 (Circle→distCircle ∘ injCircle)
 distCircleMetricSpaceStr
IsUContMap-ℝ→distCircle ε = 

 (([ 1 / 16 ] , _) ℚ₊· ε) ,
 λ x y <δ →
  let z : absᵣ (x ·ᵣ (2 ·ᵣ π-number) -ᵣ y ·ᵣ (2 ·ᵣ π-number)) ≤ᵣ
           rat (fst (/2₊ ε))
      z = isTrans≡≤ᵣ _ _ _
           (cong absᵣ (sym (𝐑'.·DistL- _ _ _)) ∙
           ·absᵣ _ _ ∙ cong₂ _·ᵣ_ refl
            (absᵣPos _ (snd (2 ₊·ᵣ π-number₊))))
           (isTrans≤ᵣ _ _ _ (≤ᵣ-o·ᵣ _ _ _ (0≤absᵣ _)
             2π-number≤8)
            (isTrans≡≤ᵣ _ _ _
              (·ᵣComm _ _) (isTrans≤≡ᵣ _ _ _
               (fst (z≤x≃y₊·z≤y₊·x _ _ 8) (<ᵣWeaken≤ᵣ _ _ <δ))
                (sym (rat·ᵣrat _ _) ∙ cong rat
                  (ℚ.·Assoc 8 [ 1 / 16 ] (fst ε) ∙
                    
                   ℚ.·Comm _ (fst ε) ∙ cong (ℚ._·_ (fst ε))
                     (ℚ.decℚ? {8 ℚ.· [ 1 / 16 ]} {[ 1 / 2 ]})
                     )))))
  in isTrans<≡ᵣ _ _ _
    (nth-rootNonNegMonotoneStrict 2 _ _
      (isTrans≤<ᵣ _
        ((rat (fst (/2₊ ε)) ^ⁿ 2)
         +ᵣ
         ((rat (fst (/2₊ ε)) ^ⁿ 2))) _
        (≤ᵣMonotone+ᵣ _ _ _ _
          (^ⁿ-Monotone 2 (0≤absᵣ _)
             (isTrans≤ᵣ _ _ _
               (cosDiffBound _ (y ·ᵣ (2 ·ᵣ π-number)))
               z))
          (^ⁿ-Monotone 2 (0≤absᵣ _)
             (isTrans≤ᵣ _ _ _
               (sinDiffBound _ (y ·ᵣ (2 ·ᵣ π-number)))
               z)))
        (x₊²+y₊²<[x₊+y₊]² (ℚ₊→ℝ₊ (/2₊ ε)) (ℚ₊→ℝ₊ (/2₊ ε)))))
    (cong fst (Iso.leftInv (nth-pow-root-iso₀₊ 2)
      (map-snd (<ᵣWeaken≤ᵣ _ _) ((ℚ₊→ℝ₊ (/2₊ ε)) ₊+ᵣ (ℚ₊→ℝ₊ (/2₊ ε))))) ∙
       (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst ε))))




-- -- 𝐿ₚ-Metric : ∀ {ℓ}
-- --   → ℕ₊₁
-- --   → ∀ a b → a ≤ᵣ b
-- --   → (A : MetricSpace ℓ)  
-- --   → UContMap Interval[ a , b ]MetricSpace A
-- --   → UContMap Interval[ a , b ]MetricSpace A
-- --   → ℝ 
-- -- 𝐿ₚ-Metric p a b a≤b A (f , fuc) (g , guc) =
-- --  fst (nth-rootNonNeg p -- IntegratedℙPropℙ
-- --       let z : (Σ ℝ
-- --                (on[_,_]IntegralOf_is_ a b
-- --                 (curry ∘ (λ x x∈ → MA.𝑑[ f (x , x∈) , g (x , x∈) ]))))
-- --           z = PT.rec2 (IntegratedℙPropℙ a b a≤b _)
-- --                (λ (fuc : ∀ ε' → Σ _ _) (guc : ∀ ε' → Σ _ _) →
-- --                  Integrate-UContinuousℙ a b a≤b
-- --                (λ x x∈ → MA.𝑑[ f (x , x∈) , g (x , x∈) ])
-- --                λ ε →
-- --                 let (δf , f<) = fuc (/2₊ ε)
-- --                     (δg , g<) = guc (/2₊ ε)
-- --                 in (δf ℚ₊+ δg) ,
-- --                      λ u v u∈ v∈ →
-- --                        (λ <δ → invEq (∼≃abs<ε _ _ _ )
-- --                          {!!})
-- --                          ∘ fst (∼≃abs<ε _ _ _ ))
-- --                 fuc guc
            
-- --           z0 = Integrate-UContinuousℙ a b a≤b _
-- --               (IsUContinuousℙ-const (intervalℙ a b) 0)
-- --       in fst z ,
-- --           isTrans≡≤ᵣ _ _ _
-- --             (sym (𝐑'.0LeftAnnihilates _)
-- --              ∙ sym (IntegralConst a b a≤b 0 (IsUContinuousConst 0)))
-- --             (Integral-≤ a b a≤b
-- --              _ _ _ _
-- --               (λ _ _ _ →
-- --                 MA.𝑑-nonNeg _ _)
-- --               (snd z0) (snd z)))

-- --  where
-- --   module MA = MetricSpaceStr (snd A)



-- 𝐈^-metricSpaceStr : ∀ n → MetricSpaceStr (𝐈^ n)
-- 𝐈^-metricSpaceStr n = {!!}

-- mb, : Σ _ (_∈ intervalℙ 0 1) → ∀ n → (𝐈^ (predℕ n)) → 𝐈^ n
-- mb, r zero x = _
-- mb, r (suc n) x = r , x






-- fst-ucm : ∀ {ℓ} {ℓ'} n n< (X : MetricSpace ℓ) (Y : MetricSpace ℓ')
--    → UContMap (_ , 𝒑-norm-× n n< (snd X) (snd Y))
--               X 
-- fst-ucm = {!!}



module RealHomotopy {ℓ} {ℓ'} (X : MetricSpace ℓ) (Y : MetricSpace ℓ') where

 open BinaryRelation


 _∼m_ : (⟨ X ⟩ → ⟨ Y ⟩) → (⟨ X ⟩ → ⟨ Y ⟩) → Type (ℓ-max ℓ ℓ')
 f₀ ∼m f₁  = Σ[ h ∈ UContMap
       (_ , (𝒑-norm-× 
          (snd X) (UnitIntervalMetricSpace .snd) 1 (ℕ.≤-solver 1 2))) Y  ]
     ((∀ x → fst h (x , (0 , (decℚ≤ᵣ? , decℚ≤ᵣ?))) ≡ f₀ x)
     × (∀ x → fst h (x , (1 , (decℚ≤ᵣ? , decℚ≤ᵣ?))) ≡ f₁ x))


 _∼_ : (UContMap X Y) → (UContMap X Y) → Type (ℓ-max ℓ ℓ')
 f₀ ∼ f₁  = fst f₀ ∼m fst f₁

 opaque
  isSym∼ : isSym _∼m_ 
  isSym∼ _ _ ((h , uc) , h0 , h1) = {!!}
     -- (UContMap∘ (h , uc) {!!}) , {!!}
   -- (UContMap∘ {!!} {!reversalMap!}) , {!!}
    -- ((λ (x , (r , 0≤r , r≤1)) →
    --   h (x , 1 -ᵣ r , 
    --    isTrans≡≤ᵣ _ _ _
    --      (sym (+-ᵣ _)) (≤ᵣ-o+ _ _ 1 (-ᵣ≤ᵣ _ _ r≤1)) ,
    --    isTrans≤≡ᵣ _ _ _ (≤ᵣ-o+ _ _ 1 (-ᵣ≤ᵣ _ _ 0≤r)) (-ᵣ-rat₂ _ _ ∙ decℚ≡ᵣ?)))
    --     ,
    --   PT.map (flip (isUContMap∘ _ {!!}) {!reversalMap!}) uc) , (λ {x} → cong (h ∘ (x ,_))
    --    (Σ≡Prop (∈-isProp (intervalℙ 0 1)) (-ᵣ-rat₂ _ _ ∙ decℚ≡ᵣ?)) ∙_) ∘ h1
    --    , (λ {x} → cong (h ∘ (x ,_))
    --    (Σ≡Prop (∈-isProp (intervalℙ 0 1)) (-ᵣ-rat₂ _ _ ∙ decℚ≡ᵣ?)) ∙_) ∘ h0


 opaque
  isTrans∼ : isTrans _∼m_ 
  isTrans∼ _ _ _ ((hL , ucL) , hL0 , hL1) ((hR , ucR) , hR0 , hR1) =
    (h , {!!})
    , (λ x →
     S.stichSetFns-x< x 0 decℚ<ᵣ? ∙
      cong (hL ∘ (x ,_)) (Σ≡Prop (∈-isProp (intervalℙ 0 1))
        (cong (clampᵣ _ _) (sym (rat·ᵣrat _ _))
         ∙ clampᵣ-rat _ _ _ ))
       ∙ hL0 x ) ,
        λ x → S.stichSetFns-<x x 1 decℚ<ᵣ? ∙
          cong (hR ∘ (x ,_)) (Σ≡Prop (∈-isProp (intervalℙ 0 1))
            ((cong (clampᵣ _ _)
              (cong₂ _-ᵣ_ (sym (rat·ᵣrat _ _)) refl ∙ -ᵣ-rat₂ _ _)
               ∙ clampᵣ-rat _ _ _ ∙ decℚ≡ᵣ? )))
           ∙ hR1 x

   where
    module MY = MetricSpaceStr (snd Y)
    module _ (x : ⟨ X ⟩) where
     module S = Stiching.hLev2 (Y .fst) (rat [ 1 / 4 ]) (rat [ 3 / 4 ])
          decℚ<ᵣ?
           (λ r _ →
             hL (x , clampᵣ 0 1 (4 ·ᵣ r) ,
               clampᵣ∈ℚintervalℙ 0 1 decℚ≤ᵣ? (4 ·ᵣ r)))
           (λ r _ →
             hR (x , clampᵣ 0 1 ((4 ·ᵣ r) -ᵣ 3 ) ,
               clampᵣ∈ℚintervalℙ 0 1 decℚ≤ᵣ? (4 ·ᵣ r -ᵣ 3)))
               MY.is-set
               (λ r r< <r →
           cong (hL ∘ (x ,_)) (Σ≡Prop (∈-isProp (intervalℙ 0 1))
            (≤x→clampᵣ≡ 0 1 _ decℚ≤ᵣ?
             (fst (z/y≤x₊≃z≤y₊·x r 1 4)
              (isTrans≡≤ᵣ _ _ _
                (·IdL _ ∙ invℝ₊-rat 4)
               (<ᵣWeaken≤ᵣ _ _ <r)))))
           ∙∙ hL1 x ∙ sym (hR0 x) ∙∙
           cong (hR ∘ (x ,_)) (Σ≡Prop (∈-isProp (intervalℙ 0 1))
            (sym (x≤→clampᵣ≡ 0 1 _ decℚ≤ᵣ?
             (isTrans≤≡ᵣ _ _ _
               (≤ᵣ-+o _ _ (-ᵣ 3)
               (≤ᵣ-o· _ _ 4 (ℚ.decℚ≤? {0} {4}) (<ᵣWeaken≤ᵣ _ _ r<)))
               (cong₂ _-ᵣ_ (sym (rat·ᵣrat _ _)) refl
                ∙ -ᵣ-rat₂ _ _ ∙ decℚ≡ᵣ?))) )))

    h : X .fst × UnitIntervalMetricSpace .fst → Y .fst
    h (x , r , 0≤r , r≤1) =
      S.stichSetFns x r 

 eval∼m : ∀ f g → f ∼m g → ⟨ X ⟩ →
  UContMap UnitIntervalMetricSpace Y 
 eval∼m f g (h , _) x =
   UContMap∘ {A = UnitIntervalMetricSpace}
             {B = _ , 𝒑-norm-× (snd X)
    (snd UnitIntervalMetricSpace) one (ℕ.≤-solver 1 2)}
             {C = Y}
     h (pair-ucm one (ℕ.≤-solver 1 2)
     X UnitIntervalMetricSpace x)


 _∼≻_ : Type (ℓ-max ℓ ℓ')
 _∼≻_ = UContMap X Y SQ./ _∼_



unwindDistCirclePathConcat :
  ∀ {a b c} a<b b<c 
   → ((f , _)  : UContMap (Interval[ a , c ]MetricSpace) distCircleMetricSpace)
   → Σ ((fst (Interval[ a , b ]MetricSpace)) → ℝ)
     (λ g → ((∀ x x∈ → f (fst x , x∈) ≡
        f ((a , (≤ᵣ-refl a ,
         isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a<b) (<ᵣWeaken≤ᵣ _ _ b<c)))) ℝS¹.+
       Circle→distCircle (injCircle (g x))) ×
        ((g (a , (≤ᵣ-refl a , (<ᵣWeaken≤ᵣ _ _ a<b))) ≡ 0))))
   → Σ ((fst (Interval[ b , c ]MetricSpace)) → ℝ)
     (λ g → ((∀ x x∈ → f (fst x , x∈) ≡ f (b ,
       ((<ᵣWeaken≤ᵣ _ _ a<b) , (<ᵣWeaken≤ᵣ _ _ b<c))) ℝS¹.+
       Circle→distCircle (injCircle (g x))) ×
        ((g (b , (≤ᵣ-refl b , (<ᵣWeaken≤ᵣ _ _ b<c))) ≡ 0))))
   → Σ ((fst (Interval[ a , c ]MetricSpace)) → ℝ)
   λ g → ((∀ x → f x ≡ f (a , (≤ᵣ-refl a ,
    isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a<b) (<ᵣWeaken≤ᵣ _ _ b<c))) ℝS¹.+
     Circle→distCircle (injCircle (g x)))
       × (g (a , (≤ᵣ-refl a , isTrans≤ᵣ _ _ _
         (<ᵣWeaken≤ᵣ _ _ a<b) (<ᵣWeaken≤ᵣ _ _ b<c))) ≡ 0))
unwindDistCirclePathConcat {a} {b} {c} a<b b<c (f , fuc)
 (gAB ,  ab= , ab=0) (gBC , bc= , bc=0) =
 g , gEq , gEq0

 where
  module M = MetricSpaceStr distCircleMetricSpaceStr
  a≤b = <ᵣWeaken≤ᵣ _ _ a<b
  b≤c = <ᵣWeaken≤ᵣ _ _ b<c
  g : fst Interval[ _ , _ ]MetricSpace → ℝ
  g (x , a≤x , x≤c) =
           gAB (minᵣ b x , ≤min-lem a b x a≤b a≤x , min≤ᵣ b x)
        +ᵣ gBC (maxᵣ b x , (≤maxᵣ b x) , max≤-lem b x c b≤c x≤c)



  fa : distCircle
  fa = f (a , ≤ᵣ-refl a , isTrans≤ᵣ a b c a≤b b≤c)


  g-≤b : ∀ x x∈ → x ≤ᵣ b →
      f (x , x∈) ≡ fa ℝS¹.+ Circle→distCircle (injCircle (g (x , x∈)))
  g-≤b x x∈ x≤b = 
        ab= (x , fst x∈ , x≤b) x∈ ∙
         cong₂ ℝS¹._+_ refl
           (cong (Circle→distCircle ∘ injCircle)
             (sym (+IdR _) 
              ∙ cong₂ _+ᵣ_
               (cong gAB (Σ≡Prop (∈-isProp (intervalℙ a b))
                 {u = _ , fst x∈ , x≤b}
                 (sym (≤→minᵣ _ _ x≤b) ∙ minᵣComm _ _)))
               (sym bc=0 ∙ cong gBC
                 ((Σ≡Prop (∈-isProp (intervalℙ b c))
                 (sym (≤→maxᵣ _ _ x≤b) ∙ maxᵣComm _ _))))))


  g-b≤ : ∀ x x∈ → b ≤ᵣ x →
    f (x , x∈) ≡
      circle+ fa
      (Circle→distCircle (injCircle (g (x , x∈))))
  g-b≤ x x∈ b≤x =
        (bc= (x , b≤x , snd x∈) x∈ ∙
          cong (ℝS¹._+ _) (ab= _ _)
          ∙ sym (ℝS¹.+Assoc _ _ _)
          )
        ∙ cong₂ ℝS¹._+_ refl
           (Circle→distCircle∘injCircle-groupHom
            (gAB (b , a≤b , ≤ᵣ-refl b))
            (gBC (x , b≤x , snd x∈))
            ∙ (cong (Circle→distCircle ∘ injCircle)
            $ cong₂ _+ᵣ_
              (cong gAB (Σ≡Prop (∈-isProp (intervalℙ a b))
                (sym (≤→minᵣ _ _ b≤x))))
                (cong gBC
                 ((Σ≡Prop (∈-isProp (intervalℙ b c))
                 (sym (≤→maxᵣ _ _ b≤x)))))))

  ucGAB : IsUContMap (Interval[ a , c ]MetricSpace .snd) f
      (distCircleMetricSpace .snd) → IsUContinuousℙ (intervalℙ a c)
      (λ x x∈ →
         gAB
         (minᵣ b x , ≤min-lem a b x a≤b (x∈ .fst) , min≤ᵣ b x))
  ucGAB fuc ε = {!isTrans∼!}
    -- map-snd (λ {δ} X u v u∈ v∈ →
    --   (λ <δ →
    --    let z = X (minᵣ b u , ≤min-lem a b u a≤b (u∈ .fst) ,
    --                isTrans≤ᵣ _ _ _ (min≤ᵣ b u) b≤c)
    --              (minᵣ b v , ≤min-lem a b v a≤b (v∈ .fst) ,
    --                isTrans≤ᵣ _ _ _ (min≤ᵣ b v) b≤c)
    --             (isTrans≤<ᵣ _ _ _
    --              (isTrans≡≤ᵣ _ _ _
    --                (cong absᵣ (cong₂ _-ᵣ_
    --                      (cong (minᵣ b)
    --                        (sym (≤→maxᵣ _ _ (min≤ᵣ u v)))
    --                       ∙ minᵣComm _ _)
    --                  (cong (minᵣ b)
    --                   (sym (≤→maxᵣ _ _
    --                    (isTrans≡≤ᵣ _ _ _ (minᵣComm _ _)
    --                      (min≤ᵣ v u))))
    --                    ∙ minᵣComm _ _)))
    --                (clampDistᵣ (minᵣ u v) b v u))
    --              <δ)
    --    in invEq (∼≃abs<ε _ _ _ )
    --              (isTrans≤<ᵣ _ _ _
    --                (isTrans≤≡ᵣ _ _ _ {!!}
    --                 ((IsIsometryℝS¹+ fa _ _)
    --               ∙ cong₂ M.𝑑[_,_]
    --                (sym (ab= (minᵣ b u ,
    --                 ≤min-lem a b u a≤b (u∈ .fst) , min≤ᵣ b u)
    --                 _))
    --                (sym (ab= (minᵣ b v ,
    --                ≤min-lem a b v a≤b (v∈ .fst) , min≤ᵣ b v)
    --                _))))
    --                z))
    --            ∘ fst (∼≃abs<ε _ _ _ )) (fuc ε)

  ucGBC : IsUContMap (Interval[ a , c ]MetricSpace .snd) f
      (distCircleMetricSpace .snd) →
       IsUContinuousℙ (intervalℙ a c)
      (λ x x∈ →
         gBC
         (maxᵣ b x , ≤maxᵣ b x , max≤-lem b x c b≤c (x∈ .snd)))
  ucGBC fuc ε = {!!}

  g-cont : ∥ IsUContMap (Interval[ a , c ]MetricSpace .snd) g (snd ℝMetricSpace) ∥₁
  g-cont = PT.map
    (λ X →
      let z = IsUContinuousℙ+ᵣ₂
            (intervalℙ a c)
             (λ x (a≤x , x≤c) →
                 gAB (minᵣ b x , ≤min-lem a b x a≤b a≤x , min≤ᵣ b x))
             (λ x (a≤x , x≤c) →
                 gBC (maxᵣ b x , (≤maxᵣ b x) , max≤-lem b x c b≤c x≤c))
                  (ucGAB X)
                  (ucGBC X)
      in map-snd (λ {δ} X _ _ <δ →
         fst (∼≃abs<ε _ _ _ )
          (X _ _ _ _ (invEq (∼≃abs<ε _ _ _ ) <δ))) ∘ z)
    fuc
    
  
  gEq : (x : Interval[ a , c ]MetricSpace .fst) →
         f x ≡ fa ℝS¹.+
         Circle→distCircle (injCircle (g x))
  gEq (x , x∈) = IsUContMap≡With<cases b distCircleMetricSpace a c
    (isTrans<ᵣ _ _ _ a<b b<c) (f , fuc)
     ((λ x → fa ℝS¹.+
         Circle→distCircle (injCircle (g x)))
      , PT.map2
        (isUContMap∘ {A = (Interval[ a , c ]MetricSpace)}
            {B = (distCircleMetricSpace)}
            {C = (distCircleMetricSpace)} (fa ℝS¹.+_) _
           )
         ∣ IsUContMapℝS¹+ fa ∣₁
         ( PT.map2
        (isUContMap∘ {A = Interval[ a , c ]MetricSpace}
            {B = ℝMetricSpace} {C = distCircleMetricSpace}
              (Circle→distCircle ∘ injCircle) g)
            ∣ IsUContMap-ℝ→distCircle ∣₁ g-cont)
         )
     (λ x x∈ → ⊎.rec (g-≤b x x∈) (g-b≤ x x∈))
     x x∈
  
  gEq0 : g (a , ≤ᵣ-refl a , isTrans≤ᵣ a b c a≤b b≤c) ≡ 0
  gEq0 = cong₂ _+ᵣ_
    (cong gAB (Σ≡Prop (∈-isProp (intervalℙ a b))
      (minᵣComm b a ∙ ≤→minᵣ _ _ a≤b)) ∙ ab=0)
    (cong gBC (Σ≡Prop (∈-isProp (intervalℙ b c))
      (maxᵣComm b a ∙ ≤→maxᵣ _ _ a≤b)) ∙ bc=0)
       ∙ +IdR _


ssn≤2·sn : ∀ n → suc (suc n) ℕ.≤ 2 ℕ.· suc n
ssn≤2·sn n = subst2 (ℕ._≤_)
  (cong (2 ℕ.+_) (ℕ.·-identityʳ n))
  (ℕ.·-comm (suc n) 2)
    (ℕ.≤-k+ {k = 2} (ℕ.≤-k· {1} {2} {n} (ℕ.≤-solver 1 2)))
    
unwindDistCirclePath :
   (f : UnitIntervalMetricSpace .fst → distCircle)
 → IsUContMap (snd UnitIntervalMetricSpace) f distCircleMetricSpaceStr
 → Σ ((fst UnitIntervalMetricSpace) → ℝ)
   λ g → ((∀ x → f x ≡ f (0 , (decℚ≤ᵣ? , decℚ≤ᵣ?)) ℝS¹.+
     Circle→distCircle (injCircle (g x)))
     × (g (0 , decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ 0))
       
unwindDistCirclePath f ucf =
 let (q , Q) = ucf 1
     (1+ N , 1/q<sN) = ℚ.ceilℚ₊ (invℚ₊ q)
     1/sN≡q : fst (invℚ₊ (fromNat (suc (suc N)))) ℚ.<
                 fst (invℚ₊ (invℚ₊ q))
     1/sN≡q = fst (ℚ.invℚ₊-<-invℚ₊ (invℚ₊ q)
               ((fromNat (suc (suc N)))))
               (ℚ.isTrans< (fst (invℚ₊ q)) _ _ 1/q<sN
                (ℚ.<ℤ→<ℚ (pos (suc N)) _
                  (invEq (ℤ.pos-<-pos≃ℕ< (suc N) (suc (suc N)))
                    (ℕ.≤-refl {suc (suc N)} ))))
                
     Q' : ∀ x y →
           fromNat (suc (suc N)) ·ᵣ 𝑑[ x , y ] ≤ᵣ 1
            → M.𝑑[ f x , f y ]  ≤ᵣ rat (fst 1)
     Q' x y ssN·d≤1 =
       <ᵣWeaken≤ᵣ _ _
         (Q x y
           ((isTrans≤<ᵣ _ _ _
         (invEq (z≤x/y₊≃y₊·z≤x 1 _ (ℚ₊→ℝ₊ (fromNat (suc (suc N)))))
            (ssN·d≤1))
           ((isTrans≡<ᵣ _ _ _
            (·IdL _ ∙ invℝ₊-rat (fromNat (suc (suc N))))
             ((isTrans<≡ᵣ _ _ _ (<ℚ→<ᵣ _
               (fst (invℚ₊ (invℚ₊ q))) 1/sN≡q)
              (cong rat (ℚ.invℚ₊-invol q) ))))))))

     (ff , QQ , QQ') = udcpₙ (suc N) 0 1 decℚ<ᵣ? f ucf
      λ x y <b-a → Q' x y (isTrans≤≡ᵣ _ _ _ <b-a (-ᵣ-rat₂ 1 0))   
 in ff , (λ x → QQ x ∙
     cong₂ ℝS¹._+_ (cong f (Σ≡Prop (∈-isProp (intervalℙ 0 1)) refl)) refl)
      , cong ff (Σ≡Prop (∈-isProp (intervalℙ 0 1)) refl) ∙ QQ'
 where
  open MetricSpaceStr (snd UnitIntervalMetricSpace)
  module M = MetricSpaceStr distCircleMetricSpaceStr

  module M[_,_] (a b : ℝ) where
   open MetricSpaceStr (snd Interval[ a , b ]MetricSpace) public

  udcpₙ : ∀ N a b → (a<b : a <ᵣ b) →  
     (f : (Interval[ a , b ]MetricSpace) .fst → distCircle)
   → IsUContMap (snd Interval[ a , b ]MetricSpace) f distCircleMetricSpaceStr
   → (∀ x y →
           fromNat (suc N) ·ᵣ M[_,_].𝑑[ a , b ] x y ≤ᵣ b -ᵣ a
            → M.𝑑[ f x , f y ]
             ≤ᵣ rat (fst 1))
   → Σ ((fst (Interval[ a , b ]MetricSpace)) → ℝ)
     λ g → (∀ x → f x ≡ f (a , ≤ᵣ-refl a , <ᵣWeaken≤ᵣ _ _ a<b) ℝS¹.+
       Circle→distCircle (injCircle (g x))) ×
        (g (a , ≤ᵣ-refl a , <ᵣWeaken≤ᵣ _ _ a<b) ≡ 0)
  udcpₙ zero a b a<b f ucf fD =
   let fD' : (x : Interval[ a , b ]MetricSpace .fst) →
              cartDist² (fst (f (a , ≤ᵣ-refl a , <ᵣWeaken≤ᵣ a b a<b)))
                (fst (f x)) <ᵣ 2
       fD' x = 
         let zz = fD ((a , ≤ᵣ-refl a , <ᵣWeaken≤ᵣ a b a<b)) x
               (isTrans≡≤ᵣ _ _ _
               (·IdL _ ∙ minusComm-absᵣ _ _ ∙
                 absᵣNonNeg _ (x≤y→0≤y-x _ _ (fst (snd x))))
                   (≤ᵣ-+o _ _ _ (snd (snd x))))
         in isTrans≤<ᵣ _ _ _
              (subst2 _≤ᵣ_
                  (cong fst (Iso.rightInv (nth-pow-root-iso₀₊ 2)
                     _) ∙ cong₂ _+ᵣ_
                      (x^²=x·x _ ∙ sym (x·x≡∣x∣·∣x∣ _))
                      (x^²=x·x _ ∙ sym (x·x≡∣x∣·∣x∣ _)))
                  (1^ⁿ 2)
                (^ⁿ-Monotone 2
                 (snd M.𝑑₊[ f (a , ≤ᵣ-refl a , <ᵣWeaken≤ᵣ a b a<b) , f x ])  zz))
              (decℚ<ᵣ? {1} {2})
 
   in unwindDistCirclePathStep' a b (<ᵣWeaken≤ᵣ a b a<b)
             f fD'
  udcpₙ (suc N) a b a<b f ucf fD =
   let (a+b/2 , a< , <b) = denseℝ a b a<b
       pp : 2 ·ᵣ (b -ᵣ a+b/2) ≡ b -ᵣ a
       pp = ·DistL+ _ _ _ ∙
              cong₂ _+ᵣ_ (sym (x+x≡2x b))
                (cong₂ _·ᵣ_ refl (cong -ᵣ_
                 (cong₂ _·ᵣ_ refl (sym (invℝ₊-rat 2)))) ∙ ·ᵣComm _ _ ∙ -ᵣ· _ _ ∙
                  cong -ᵣ_ ([x/₊y]·yᵣ _ 2))
                ∙ solve! ℝring
       pp' : rat 2 ·ᵣ (a+b/2 -ᵣ a) ≡ b -ᵣ a
       pp' = 𝐑'.·DistR- _ _ _ ∙
          cong₂ _-ᵣ_ (cong₂ _·ᵣ_ refl
            (cong₂ _·ᵣ_ refl (sym (invℝ₊-rat 2)))  ∙ ·ᵣComm _ _ ∙
             [x/₊y]·yᵣ _ 2)
           (sym (x+x≡2x a)) ∙ solve! ℝring
       (fAB , fAB= , fAB=0) = udcpₙ N _ _ a<
         (λ (x , ≤x , x≤) → f (x , ≤x , isTrans≤ᵣ _ _ _ x≤ (<ᵣWeaken≤ᵣ _ _ <b)))
         (map-snd (λ X u v <δ → X _ _ <δ) ∘ ucf)
          λ (x , ≤x , x≤) (y , ≤y , y≤) sN≤ →
            fD (x , ≤x , isTrans≤ᵣ _ _ _ x≤ (<ᵣWeaken≤ᵣ _ _ <b))
               (y , ≤y , isTrans≤ᵣ _ _ _ y≤ (<ᵣWeaken≤ᵣ _ _ <b))
               ((isTrans≤ᵣ _ _ _
                    (isTrans≤≡ᵣ _ _ _
                      (≤ᵣ-·ᵣo _ _ _
                        (snd (M[_,_].𝑑₊[ a , b ]
                          (x , ≤x , isTrans≤ᵣ _ _ _ x≤ (<ᵣWeaken≤ᵣ _ _ <b))
                          (y , ≤y , isTrans≤ᵣ _ _ _ y≤ (<ᵣWeaken≤ᵣ _ _ <b))
                          ))
                             (≤ℚ→≤ᵣ _ _
                               (ℚ.≤ℤ→≤ℚ _ _
                                 (subst (pos (suc (suc N)) ℤ.≤_)
                                   (ℤ.pos·pos 2 (suc N))
                                     (ℤ.ℕ≤→pos-≤-pos _ _
                                      (ssn≤2·sn N))))))
                      (cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl
                        ∙ sym (·ᵣAssoc _ _ _)))
                    (isTrans≤≡ᵣ _ _ _
                    (≤ᵣ-o· _ _ 2
                      (ℚ.decℚ≤? {0} {2})
                      sN≤) pp')))
       (fBC , fBC= , fBC=0) = udcpₙ N _ _ <b
          (λ (x , ≤x , x≤) → f (x , isTrans≤ᵣ _ _ _  (<ᵣWeaken≤ᵣ _ _ a<) ≤x , x≤))
          (map-snd (λ X u v <δ → X _ _ <δ) ∘ ucf)
           λ (x , ≤x , x≤) (y , ≤y , y≤) sN≤ →
            fD (x , isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a<) ≤x , x≤)
                  (y , isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a<) ≤y , y≤)
                  (isTrans≤ᵣ _ _ _
                    (isTrans≤≡ᵣ _ _ _
                      (≤ᵣ-·ᵣo _ _ _
                        (snd (M[_,_].𝑑₊[ a , b ]
                          (x ,
                           isTrans≤ᵣ a a+b/2 x
                             (<ᵣWeaken≤ᵣ a a+b/2 a<) ≤x , x≤)
                          (y ,
                           isTrans≤ᵣ a a+b/2 y
                            (<ᵣWeaken≤ᵣ a a+b/2 a<) ≤y , y≤)))
                             (≤ℚ→≤ᵣ _ _
                               (ℚ.≤ℤ→≤ℚ _ _
                                 (subst (pos (suc (suc N)) ℤ.≤_)
                                   (ℤ.pos·pos 2 (suc N))
                                     (ℤ.ℕ≤→pos-≤-pos _ _
                                      (ssn≤2·sn N))))))
                      (cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl
                        ∙ sym (·ᵣAssoc _ _ _)))
                    (isTrans≤≡ᵣ _ _ _
                    (≤ᵣ-o· _ _ 2
                      (ℚ.decℚ≤? {0} {2})
                      sN≤) pp))
            
       (fAC , fAC= , fAC=0) = unwindDistCirclePathConcat {a} {a+b/2 } {b}
             a< <b
              (f , ∣ ucf ∣₁)
               (fAB , ((λ x x∈ → (cong f
                ((Σ≡Prop (∈-isProp (intervalℙ a b)) refl)) ∙ fAB= x) ∙ cong₂ ℝS¹._+_
                  (cong f
                ((Σ≡Prop (∈-isProp (intervalℙ a b)) refl))) refl )) , fAB=0 )
               (fBC , (λ x x∈ → (cong f
                ((Σ≡Prop (∈-isProp (intervalℙ a b)) refl)) ∙ fBC= x) ∙ cong₂ ℝS¹._+_
                  (cong f
                ((Σ≡Prop (∈-isProp (intervalℙ a b)) refl))) refl ) , fBC=0)
   in fAC , (λ x → fAC= x ∙ cong₂ ℝS¹._+_
             (cong f (Σ≡Prop (∈-isProp (intervalℙ a b)) refl)) refl )
           , cong 
              fAC (Σ≡Prop (∈-isProp (intervalℙ a b)) refl) ∙ fAC=0


module ℝS₁→ℝS₁hom = RealHomotopy distCircleMetricSpace distCircleMetricSpace
module 𝐈→ℝS₁hom = RealHomotopy UnitIntervalMetricSpace distCircleMetricSpace



module ℝS₁hom = RealHomotopy trivialMetricSpace distCircleMetricSpace

interpℝ-const : ∀ x t → interpℝ x x t ≡ x
interpℝ-const x t = solve! ℝring



-- opaque
windingNrOf' : ∀ c₀
 → (h : c₀ ℝS₁hom.∼m c₀) 
 → ∃[ k ∈ ℤ ] ((fst (fst h) ∘ (_ ,_))
   𝐈→ℝS₁hom.∼m ((Circle→distCircle ∘ injCircle) ∘ (rat [ k / 1 ] ·ᵣ_) ∘ fst) )
windingNrOf' c₀ 𝒉@((h , ucH₁) , h0 , h1)  = do

 ucH ← snd (ℝS₁hom.eval∼m c₀ c₀ 𝒉 tt) --(𝒉  , ucH₁) 
  
 ∣ fst (p ucH)  , hh ucH ∣₁ 

 where
  module _ (ucH : IsUContMap (snd UnitIntervalMetricSpace) (λ x → h (tt , x))
                   distCircleMetricSpaceStr) where
   unwd : Σ (fst UnitIntervalMetricSpace → ℝ)
           (λ g →
              ((x : UnitIntervalMetricSpace .fst) →
               h (tt , x) ≡
               h (tt , 0 , decℚ≤ᵣ? , decℚ≤ᵣ?) ℝS¹.+
               Circle→distCircle (injCircle (g x)))
              × (g (0 , decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ 0)) 
   unwd = unwindDistCirclePath (h ∘ (_ ,_))
            ucH

   p : circle-rel (unwd .fst (0 , decℚ≤ᵣ? , decℚ≤ᵣ?))
                  (unwd .fst (1 , decℚ≤ᵣ? , decℚ≤ᵣ?))
   p = fromCircle≡ _ _
         (cong (injCircle) (snd (snd unwd))
         ∙ invEq (congEquiv Circle≃distCircle)
         ((injCircle0≡circle0 ∙
             sym (ℝS¹.+InvR _)) ∙ sym (ℝS¹.·CancelL _
             ( sym ((fst (snd unwd)) (1 , decℚ≤ᵣ? , decℚ≤ᵣ?))
              ∙ (sym (ℝS¹.+IdL _)
              ∙ cong₂ ℝS¹._+_ (sym (ℝS¹.+InvR _)) refl)
              ∙ sym (ℝS¹.+Assoc _ _ _)
              ∙ cong₂ ℝS¹._+_ (h1 _ ∙ sym (h0 _)) (ℝS¹.+Comm _ _)))))

   hh : (h ∘ (tt ,_)) 𝐈→ℝS₁hom.∼m
         ((Circle→distCircle ∘ injCircle) ∘
          _·ᵣ_ (rat [ fst p / 1 ]) ∘ (λ r → fst r))
   hh .fst .fst ((x , 0≤x , x≤1) , (r , 0≤r , r≤1)) =
      Circle→distCircle (injCircle
          (interpℝ (fst unwd (x , 0≤x , x≤1)) (rat [ fst p / 1 ] ·ᵣ x) r))
   hh .fst .snd = {!!}
   hh .snd .fst x = {!!}
    -- cong (Circle→distCircle ∘ injCircle)
    --   (interpℝ0 _ _ ) ∙ (sym (ℝS¹.+IdL _) ∙
    --     cong (ℝS¹._+
    --     Circle→distCircle (injCircle (unwd .fst x)))
    --      {!sym (snd (snd unwd))!}
    --      --snd (snd unwd)
    --       )
    --     ∙ sym (fst (snd unwd) x)
   hh .snd .snd (x , 0≤x , x≤1) = {!!}

-- windingNrOf'' : ∀ c₀
--  → (h : c₀ ℝS₁hom.∼m c₀) 
--  → ∃[ k ∈ ℤ ] (
--     {!!}
--    -- (fst (fst h) ∘ (_ ,_))
--    -- 𝐈→ℝS₁hom.∼m ((Circle→distCircle ∘ injCircle) ∘ (rat [ k / 1 ] ·ᵣ_) ∘ fst)
--    )
-- windingNrOf'' = {!!}

windingNrOf : ∀ c₀
 → (h : c₀ ℝS₁hom.∼m c₀) 
 → Σ[ k ∈ ℤ ] ((fst (fst h) ∘ (_ ,_))
   𝐈→ℝS₁hom.∼m ((Circle→distCircle ∘ injCircle) ∘ (rat [ k / 1 ] ·ᵣ_) ∘ fst) )
windingNrOf = {!!}

isEquivWindingNr : isEquiv {A = ℤ}
  {B = (λ _ → circle0) ℝS₁hom.∼m λ _ → circle0}
   {!!}
   -- λ k → (((Circle→distCircle ∘ injCircle) ∘ (rat [ k / 1 ] ·ᵣ_) ∘ fst ∘ snd)
   --  , _) , (λ x → {!!}) , {!!}
isEquivWindingNr =
  isEmbedding×isSurjection→isEquiv
    (injEmbedding {!!}
      {!!}
    , λ b → PT.map (map-snd
        (λ {a} x → sym {!SQ.eq/ _ _ x!}))
      (windingNrOf' (λ _ → circle0) b))


--  -- hh : ? ℝS₁hom.∼m (λ x → f0 ℝS¹.+ (intLoop (fst p) x))
--  -- hh .fst .fst (x , r , 0≤r , r≤1) =
--  --   let y : ∀ x' → x' ∈ intervalℙ 0 1 → ℝ
--  --       y = λ x' x'∈ → interpℝ (fst unwd (x' , x'∈)) (rat [ (fst p) / 1 ] ·ᵣ x' ) r
--  --   in {!snd p!}
--  -- hh .fst .snd = {!!}
--  -- hh .snd = {!!}

-- --   fst p
-- --      , {!!}

-- --  where


-- --  g : UnitIntervalMetricSpace .fst → distCircle
-- --  g x = (Circle→distCircle (injCircle (fst x)))

-- --  ucg : IsUContMap (snd UnitIntervalMetricSpace) g distCircleMetricSpaceStr
-- --  ucg ε = map-snd (λ X _ _ → X _ _) (IsUContMap-ℝ→distCircle ε)

-- --  g1≡g0 : g (1 , decℚ≤ᵣ? , decℚ≤ᵣ?) ≡
-- --          g (0 , decℚ≤ᵣ? , decℚ≤ᵣ?)
-- --  g1≡g0 = cong Circle→distCircle (eq/ _ _ (1 , -ᵣ-rat₂ _ _ ∙ decℚ≡ᵣ?))

-- --  f0 : {!!}
-- --  f0 = f (g (0 , decℚ≤ᵣ? , decℚ≤ᵣ?))

-- --  unwd : Σ (fst UnitIntervalMetricSpace → ℝ)
-- --          (λ g₁ →
-- --             ((x : UnitIntervalMetricSpace .fst) →
-- --              f (g x) ≡
-- --              f0 ℝS¹.+
-- --              Circle→distCircle (injCircle (g₁ x)))
-- --             × (g₁ (0 , decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ 0)) 
-- --  unwd = unwindDistCirclePath (f ∘ g)
-- --        (isUContMapComp (snd UnitIntervalMetricSpace) g
-- --          distCircleMetricSpaceStr f distCircleMetricSpaceStr ucg ucf)

-- --  p : circle-rel (unwd .fst (0 , decℚ≤ᵣ? , decℚ≤ᵣ?))
-- --                 (unwd .fst (1 , decℚ≤ᵣ? , decℚ≤ᵣ?))
-- --  p = (fromCircle≡ _ _
-- --   (cong (injCircle) (snd (snd unwd))
-- --   ∙ invEq (congEquiv Circle≃distCircle)
-- --   ((injCircle0≡circle0 ∙
-- --       sym (ℝS¹.+InvR _)) ∙ sym (ℝS¹.·CancelL (f (g (0 , decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- --       ( sym ((fst (snd unwd)) (1 , decℚ≤ᵣ? , decℚ≤ᵣ?))
-- --        ∙ (sym (ℝS¹.+IdL _)
-- --        ∙ cong₂ ℝS¹._+_ (sym (ℝS¹.+InvR _)) refl)
-- --        ∙ sym (ℝS¹.+Assoc _ _ _)
-- --        ∙ cong₂ ℝS¹._+_ (cong f g1≡g0) (ℝS¹.+Comm _ _))))))

-- --  hh : f ℝS₁hom.∼m (λ x → f0 ℝS¹.+ (intLoop (fst p) x))
-- --  hh .fst .fst (x , r , 0≤r , r≤1) =
-- --    let y : ∀ x' → x' ∈ intervalℙ 0 1 → ℝ
-- --        y = λ x' x'∈ → interpℝ (fst unwd (x' , x'∈)) (rat [ (fst p) / 1 ] ·ᵣ x' ) r
-- --    in {!snd p!}
-- --  hh .fst .snd = {!!}
-- --  hh .snd = {!!}


-- -- -- -- opaque
-- -- -- windingNrOf : (f : distCircle → distCircle)
-- -- --  → IsUContMap distCircleMetricSpaceStr f distCircleMetricSpaceStr
-- -- --  → Σ[ k ∈ ℤ ] (f ℝS₁hom.∼m intLoop k)
-- -- -- windingNrOf f ucf =
-- -- --   fst p
-- -- --      , {!!}

-- -- --  where


-- -- --  g : UnitIntervalMetricSpace .fst → distCircle
-- -- --  g x = (Circle→distCircle (injCircle (fst x)))

-- -- --  ucg : IsUContMap (snd UnitIntervalMetricSpace) g distCircleMetricSpaceStr
-- -- --  ucg ε = map-snd (λ X _ _ → X _ _) (IsUContMap-ℝ→distCircle ε)

-- -- --  g1≡g0 : g (1 , decℚ≤ᵣ? , decℚ≤ᵣ?) ≡
-- -- --          g (0 , decℚ≤ᵣ? , decℚ≤ᵣ?)
-- -- --  g1≡g0 = cong Circle→distCircle (eq/ _ _ (1 , -ᵣ-rat₂ _ _ ∙ decℚ≡ᵣ?))

-- -- --  f0 : {!!}
-- -- --  f0 = f (g (0 , decℚ≤ᵣ? , decℚ≤ᵣ?))

-- -- --  unwd : Σ (fst UnitIntervalMetricSpace → ℝ)
-- -- --          (λ g₁ →
-- -- --             ((x : UnitIntervalMetricSpace .fst) →
-- -- --              f (g x) ≡
-- -- --              f0 ℝS¹.+
-- -- --              Circle→distCircle (injCircle (g₁ x)))
-- -- --             × (g₁ (0 , decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ 0)) 
-- -- --  unwd = unwindDistCirclePath (f ∘ g)
-- -- --        (isUContMapComp (snd UnitIntervalMetricSpace) g
-- -- --          distCircleMetricSpaceStr f distCircleMetricSpaceStr ucg ucf)

-- -- --  p : circle-rel (unwd .fst (0 , decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --                 (unwd .fst (1 , decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --  p = (fromCircle≡ _ _
-- -- --   (cong (injCircle) (snd (snd unwd))
-- -- --   ∙ invEq (congEquiv Circle≃distCircle)
-- -- --   ((injCircle0≡circle0 ∙
-- -- --       sym (ℝS¹.+InvR _)) ∙ sym (ℝS¹.·CancelL (f (g (0 , decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- -- --       ( sym ((fst (snd unwd)) (1 , decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --        ∙ (sym (ℝS¹.+IdL _)
-- -- --        ∙ cong₂ ℝS¹._+_ (sym (ℝS¹.+InvR _)) refl)
-- -- --        ∙ sym (ℝS¹.+Assoc _ _ _)
-- -- --        ∙ cong₂ ℝS¹._+_ (cong f g1≡g0) (ℝS¹.+Comm _ _))))))

-- -- --  hh : f ℝS₁hom.∼m (λ x → f0 ℝS¹.+ (intLoop (fst p) x))
-- -- --  hh .fst .fst (x , r , 0≤r , r≤1) =
-- -- --    let y : ∀ x' → x' ∈ intervalℙ 0 1 → ℝ
-- -- --        y = λ x' x'∈ → interpℝ (fst unwd (x' , x'∈)) (rat [ (fst p) / 1 ] ·ᵣ x' ) r
-- -- --    in {!snd p!}
-- -- --  hh .fst .snd = {!!}
-- -- --  hh .snd = {!!}

-- -- -- -- windingNr : (f : distCircle → distCircle)
-- -- -- --  → IsUContMap distCircleMetricSpaceStr f distCircleMetricSpaceStr
-- -- -- --  → ℤ 
-- -- -- -- windingNr f ucf = fst (windingNrOf f ucf)
 
-- -- -- -- windingNr∼ : (f f' : distCircle → distCircle)
-- -- -- --  → (fuc : IsUContMap distCircleMetricSpaceStr f distCircleMetricSpaceStr)
-- -- -- --  → (fuc' : IsUContMap distCircleMetricSpaceStr f' distCircleMetricSpaceStr)
-- -- -- --  → f ℝS₁hom.∼m f'

-- -- -- --  → windingNr f fuc ≡ windingNr f' fuc'
 
-- -- -- -- windingNr∼ f f' fuc fuc' f∼f'@((h , uch) , h0 , h1) =
-- -- -- --   {!!}
-- -- -- --  where
-- -- -- --  zz : intLoop (windingNr f fuc)
-- -- -- --        ℝS₁hom.∼m
-- -- -- --       intLoop (windingNr f' fuc')
-- -- -- --  zz = ℝS₁hom.isTrans∼ _ _ _
-- -- -- --        (ℝS₁hom.isSym∼ _ _ (snd (windingNrOf f fuc)))
-- -- -- --        (ℝS₁hom.isTrans∼ f f' _
-- -- -- --         f∼f'
-- -- -- --         (snd (windingNrOf f' fuc')))



-- -- Iso.fun (PathIdTrunc₀Iso {b = b}) p =
-- --   transport (λ i → rec {B = TypeOfHLevel _ 1} (isOfHLevelTypeOfHLevel 1)
-- --                         (λ a → ∥ a ≡ b ∥₁ , squash₁) (p (~ i)) .fst)
-- --             ∣ refl ∣₁
-- -- Iso.inv PathIdTrunc₀Iso = pRec (squash₂ _ _) (cong ∣_∣₂)
-- -- Iso.rightInv PathIdTrunc₀Iso _ = squash₁ _ _
-- -- Iso.leftInv PathIdTrunc₀Iso _ = squash₂ _ _ _ _

-- congSq₂ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} →
--   {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
--   {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
--   {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
--   {a'₀₀ a'₀₁ : A} {a'₀₋ : a'₀₀ ≡ a'₀₁}
--   {a'₁₀ a'₁₁ : A} {a'₁₋ : a'₁₀ ≡ a'₁₁}
--   {a'₋₀ : a'₀₀ ≡ a'₁₀} {a'₋₁ : a'₀₁ ≡ a'₁₁}
--   → (f : A → A → B)
--   → Square (a₀₋) (a₁₋) (a₋₀) (a₋₁)
--   → Square (a'₀₋) (a'₁₋) (a'₋₀) (a'₋₁)
--   → Square (λ i → f (a₀₋ i) (a'₀₋ i))
--            (λ i → f (a₁₋ i) (a'₁₋ i))
--            (λ i → f (a₋₀ i) (a'₋₀ i))
--            (λ i → f (a₋₁ i) (a'₋₁ i))
-- congSq₂ f x x₁ i j = f (x i j) (x₁ i  j) 
-- {-# INLINE congSq₂ #-}

-- congSqP : ∀ {ℓ ℓ'} {A : I → I → Type ℓ} {B : I → I → Type ℓ'}
--   {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
--   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
--   {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
--   → (f : ∀ i j → A i j → B i j)
--   → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
--   → SquareP B (congP (f i0) a₀₋) (congP (f i1) a₁₋)
--               (congP (λ i → f i i0) a₋₀) (congP (λ i → f i i1) a₋₁)
-- congSqP f sq i j = f i j (sq i j)
-- {-# INLINE congSqP #-}

-- --  stichGpdFns : isGroupoid A → (∀ x x< <x → f x x< ≡ g x <x) → ℝ → A
-- --  stichGpdFns gpdA f=g x =
-- --    PT.rec→Gpd gpdA (⊎.rec (f x) (g x))
-- --     (w x)
-- --      (Dichotomyℝ' a x b a<b)
-- --   where

-- --   w-coh : ∀ x → (x₂ y z : (x <ᵣ b) ⊎ (a <ᵣ x)) →
-- --       Square (w₂ f=g x x₂ y) (w₂ f=g x x₂ z) refl (w₂ f=g x y z)
-- --   w-coh x (inl x₁) (inl x₂) (inl x₃) =
-- --     congP (λ _ → cong (f x)) (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
-- --   w-coh x (inl x₁) (inl x₂) (inr x₃) =
-- --     {!!} ▷ {!!} ∙
-- --      cong₂ _∙_ refl (λ _ j → f=g x {!isProp<ᵣ x b x₁ x₂ j  !} x₃ i1) ∙ sym (rUnit _)
-- --     -- f=g x {!!} x₃ (i ∧ j)
-- --     -- let zz = congSqP
-- --     --        (λ i j x< →
-- --     --        f=g x x< x₃ (i ∧ j))
-- --     --        (isSet→isSet' (isProp→isSet (isProp<ᵣ x b))
-- --     --           refl {!!} refl {!!})
-- --     -- in {!zz!}
-- --   w-coh x (inl x₁) (inr x₂) (inl x₃) = {!!}
-- --   w-coh x (inl x₁) (inr x₂) (inr x₃) = {!!}
-- --   w-coh x (inr x₁) (inl x₂) (inl x₃) = {!!}
-- --   w-coh x (inr x₁) (inl x₂) (inr x₃) = {!!}
-- --   w-coh x (inr x₁) (inr x₂) (inl x₃) = {!!}
-- --   w-coh x (inr x₁) (inr x₂) (inr x₃) =
-- --     congP (λ _ → cong (g x)) (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
  
-- --   w : ∀ x → 3-Constant (⊎.rec (f x) (g x))
-- --   w x .3-Constant.link = w₂ f=g x
-- --   w x .3-Constant.coh₁ = w-coh x
-- --   -- w x .3-Constant.coh₁ (inl x₁) (inl x₂) (inl x₃) =
-- --   --   congP (λ _ → cong (f x)) (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
-- --   -- w x .3-Constant.coh₁ (inl x₁) (inl x₂) (inr x₃) =
-- --   --  let z = congSqP
-- --   --          (λ i j x< →
-- --   --          f=g x x< x₃ (i ∧ j))
-- --   --          (isProp→SquareP (λ _ _ → isProp<ᵣ x b)
-- --   --            {!!}
-- --   --            {!!}
-- --   --            {!!}
-- --   --            {!!})
-- --   --  in {!z!}
-- --   --   -- congP (λ i → congP (λ j y → f=g x {!!} {!!} (i ∧ j)))
-- --   --   --      (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
-- --   -- w x .3-Constant.coh₁ (inl x₁) (inr x₂) (inl x₃) = {!!}
-- --   -- w x .3-Constant.coh₁ (inl x₁) (inr x₂) (inr x₃) = {!!}
-- --   -- w x .3-Constant.coh₁ (inr x₁) (inl x₂) (inl x₃) = {!!}
-- --   -- w x .3-Constant.coh₁ (inr x₁) (inl x₂) (inr x₃) = {!!}
-- --   -- w x .3-Constant.coh₁ (inr x₁) (inr x₂) (inl x₃) = {!!}
-- --   -- w x .3-Constant.coh₁ (inr x₁) (inr x₂) (inr x₃) =
-- --   --  congP (λ _ → cong (g x)) (isProp→SquareP (λ _ _ → isProp<ᵣ _ _) _ _ _ _)
-- -- -- stichGpdFns : ∀ {ℓ} (A : Type ℓ) → (isGroupoid A) → (a b : ℝ) → a <ᵣ b
-- -- --            → (f : ∀ x → x <ᵣ b → A)
-- -- --            → (g : ∀ x → a <ᵣ x → A)
-- -- --            → (∀ x x< <x → f x x< ≡ g x <x)
-- -- --            → ℝ → A
-- -- -- stichGpdFns A isGroupoidA a b a<b f g f=g x =
-- -- --   PT.rec→Gpd isGroupoidA
-- -- --     (⊎.rec (f x) (g x))
-- -- --     w
-- -- --    (Dichotomyℝ' a x b a<b)
-- -- --  where
-- -- --  w : 3-Constant (⊎.rec (f x) (g x))
-- -- --  w .3-Constant.link = {!!}
-- -- --  w .3-Constant.coh₁ = {!!}
-- -- --  -- w : 2-Constant (⊎.rec (f x) (g x))
-- -- --  -- w (inl u) (inl v) = cong (f x) (isProp<ᵣ _ _ u v)
-- -- --  -- w (inl u) (inr v) = f=g x u v
-- -- --  -- w (inr u) (inl v) = sym (f=g x v u)
-- -- --  -- w (inr u) (inr v) = cong (g x) (isProp<ᵣ _ _ u v)





-- record MetricSpaceStr {ℓ} (A : Type ℓ) : Type ℓ where

--   constructor metricSpaceStr

--   field
--    is-set : isSet A
--    𝑑[_,_] : A → A → ℝ
--    𝑑-nonNeg : ∀ x y → 0 ≤ᵣ 𝑑[ x , y ]
--    𝑑-sym : ∀ x y → 𝑑[ x , y ] ≡ 𝑑[ y , x ]
--    𝑑-pos : ∀ x y → (0 <ᵣ 𝑑[ x , y ]) → x ≡ y → ⊥
--    𝑑-zero→≡ : ∀ x y → 0 ≡ 𝑑[ x , y ] → x ≡ y
--    𝑑-≡→zero : ∀ x y → x ≡ y → 0 ≡ 𝑑[ x , y ]
--    𝑑-triangle : ∀ x y z → 𝑑[ x , z ] ≤ᵣ 𝑑[ x , y ] +ᵣ 𝑑[ y , z ]
   
-- MetricSpace : ∀ ℓ → Type (ℓ-suc ℓ)
-- MetricSpace ℓ = TypeWithStr ℓ MetricSpaceStr

-- MetricSpace₀ = MetricSpace ℓ-zero

-- ℝMetricSpace : MetricSpace₀
-- ℝMetricSpace .fst = ℝ
-- ℝMetricSpace .snd .MetricSpaceStr.is-set = isSetℝ
-- ℝMetricSpace .snd .MetricSpaceStr.𝑑[_,_] x y = absᵣ (x -ᵣ y)
-- ℝMetricSpace .snd .MetricSpaceStr.𝑑-nonNeg _ _ = 0≤absᵣ _
-- ℝMetricSpace .snd .MetricSpaceStr.𝑑-sym = minusComm-absᵣ
-- ℝMetricSpace .snd .MetricSpaceStr.𝑑-pos _ _ 0<d x=y =
--   ≤ᵣ→≯ᵣ (absᵣ _) 0
--    (≡ᵣWeaken≤ᵣ _ _ (cong absᵣ (𝐑'.+InvR' _ _ x=y) ∙ absᵣ0)) 0<d
-- ℝMetricSpace .snd .MetricSpaceStr.𝑑-zero→≡ _ _ 0=d =
--   𝐑'.equalByDifference _ _ (absᵣx=0→x=0 _ (sym 0=d))
-- ℝMetricSpace .snd .MetricSpaceStr.𝑑-≡→zero _ _ 0=d =
--   sym absᵣ0 ∙ cong absᵣ (sym (𝐑'.+InvR' _ _ 0=d))
-- ℝMetricSpace .snd .MetricSpaceStr.𝑑-triangle = absᵣ-triangle-midpt

-- MetricSubSpace : ∀ {ℓ} (A : Type ℓ) → (P : ℙ A)
--   → MetricSpaceStr A
--   → MetricSpaceStr (Σ A (_∈ P))
-- MetricSubSpace A P msp = w
--  where
--  open MetricSpaceStr msp
--  w : MetricSpaceStr (Σ A (_∈ P))
--  w .MetricSpaceStr.is-set = isSetΣ is-set (isProp→isSet ∘ ∈-isProp P)
--  w .𝑑[_,_] (x , _) (y , _) = 𝑑[ x , y ] 
--  w .𝑑-nonNeg _ _ = 𝑑-nonNeg _ _
--  w .𝑑-sym _ _ = 𝑑-sym _ _
--  w .𝑑-pos _ _ 0<d = 𝑑-pos _ _ 0<d ∘ cong fst
--  w .𝑑-zero→≡ _ _ 0=d = Σ≡Prop (∈-isProp P) (𝑑-zero→≡ _ _ 0=d)
--  w .𝑑-≡→zero _ _ = 𝑑-≡→zero _ _ ∘ cong fst
--  w .𝑑-triangle _ _ _ = 𝑑-triangle _ _ _


-- IsUContMap : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
--          (AM : MetricSpaceStr A) (f : A → B) (BM : MetricSpaceStr B)
--          → Type ℓ
-- IsUContMap AM f BM =
--  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
--    ∀ x y → AM.𝑑[ x , y ] <ᵣ rat (fst δ)
--          → BM.𝑑[ f x , f y ] <ᵣ rat (fst ε)
--  where
--     module AM = MetricSpaceStr AM
--     module BM = MetricSpaceStr BM

-- UContMap : ∀ {ℓ ℓ'} → MetricSpace ℓ → MetricSpace ℓ' → Type (ℓ-max ℓ ℓ')
-- UContMap (_ , A) (_ , B) = Σ _ λ f → ∥ IsUContMap A f B ∥₁



-- IntervalMetricSpace : MetricSpace₀
-- IntervalMetricSpace = _ , MetricSubSpace _  (intervalℙ 0 1) (snd ℝMetricSpace)


-- isUContMap∘ : ∀ {ℓ ℓ' ℓ''}
--   → (A : MetricSpace ℓ)
--   → (B : MetricSpace ℓ')
--   → (C : MetricSpace ℓ'')
--   → ∀ f g
--   → IsUContMap (snd B) f (snd C)
--   → IsUContMap (snd A) g (snd B)
--   → IsUContMap (snd A) (f ∘ g) (snd C)  
-- isUContMap∘ = {!!}

-- uContConstMap : ∀ {ℓ ℓ'}
--   → (A : MetricSpace ℓ)
--   → (B : MetricSpace ℓ')
--   → (b : ⟨ B ⟩) → IsUContMap (snd A) (const b) (snd B) 
-- uContConstMap A B a = (λ ε → 1 , λ _ _ _ → isTrans≡<ᵣ _ _ _ {!!} {!!} )

-- Interval²MetricSpaceStr : MetricSpaceStr
--  ((Σ ℝ (_∈ intervalℙ 0 1)) × (Σ ℝ (_∈ intervalℙ 0 1)))
-- Interval²MetricSpaceStr = {!!}

-- Interval²MetricSpace : MetricSpace₀
-- Interval²MetricSpace = (Σ ℝ (_∈ intervalℙ 0 1)) × (Σ ℝ (_∈ intervalℙ 0 1))
--   , Interval²MetricSpaceStr
--   --MetricSubSpace _  (intervalℙ 0 1) (snd ℝMetricSpace)


-- 𝐿₁-Metric : ∀ {ℓ}
--   → (A : MetricSpace ℓ)
--   → UContMap IntervalMetricSpace A
--   → UContMap IntervalMetricSpace A → ℝ 
-- 𝐿₁-Metric A f g = {!!}

-- UContMapEq : ∀ {ℓ ℓ'} → (A : MetricSpace ℓ)
--           → (A' : MetricSpace ℓ') →
--             (f g : UContMap A A')
--             → (∀ x → fst f x ≡ fst g x ) → f ≡ g
-- UContMapEq A A' f g x = Σ≡Prop (λ _ → squash₁) (funExt x)

-- 𝐿₁-MetricSpace : ∀ {ℓ}
--   → (A : MetricSpace ℓ)
--   → MetricSpaceStr (UContMap IntervalMetricSpace A) 
-- 𝐿₁-MetricSpace A = w
--  where
--  module AM = MetricSpaceStr (snd A)

--  w : MetricSpaceStr (UContMap IntervalMetricSpace A)
--  w .MetricSpaceStr.is-set =
--    isSetΣ (isSet→ AM.is-set) λ _ → isProp→isSet squash₁
--  w .MetricSpaceStr.𝑑[_,_] = 𝐿₁-Metric A
--  w .MetricSpaceStr.𝑑-nonNeg = {!!}
--  w .MetricSpaceStr.𝑑-sym = {!c!}
--  w .MetricSpaceStr.𝑑-pos = {!!}
--  w .MetricSpaceStr.𝑑-zero→≡ = {!!}
--  w .MetricSpaceStr.𝑑-≡→zero = {!!}
--  w .MetricSpaceStr.𝑑-triangle = {!!}

-- 𝐿₁-MetricSpaceⁿ :  ∀ {ℓ} → ℕ → MetricSpace ℓ → MetricSpace ℓ 
-- 𝐿₁-MetricSpaceⁿ zero A = A
-- 𝐿₁-MetricSpaceⁿ (suc n) A = _ , 𝐿₁-MetricSpace (𝐿₁-MetricSpaceⁿ n A)


-- private
--  variable
--   ℓ ℓ' : Level

-- ∙MetricSpaceStr : Type ℓ → Type ℓ
-- ∙MetricSpaceStr = ProductStructure PointedStructure MetricSpaceStr

-- ∙MetricSpace : ∀ ℓ → Type (ℓ-suc ℓ)
-- ∙MetricSpace ℓ = TypeWithStr ℓ ∙MetricSpaceStr

-- ∙MetricSpace→Pointed : ∀ {ℓ} → ∙MetricSpace ℓ → P.Pointed ℓ
-- ∙MetricSpace→Pointed (A , a , _) = (A , a)

-- ∙MetricSpace→MetricSpace : ∀ {ℓ} → ∙MetricSpace ℓ → MetricSpace ℓ
-- ∙MetricSpace→MetricSpace (_ , _ , A) = (_ , A)


-- instance
--   fromNatUnitInterval : HasFromNat (Σ _ (_∈ intervalℙ 0 1))
--   fromNatUnitInterval .HasFromNat.Constraint zero = Unit
--   fromNatUnitInterval .HasFromNat.Constraint (suc zero) = Unit
--   fromNatUnitInterval .HasFromNat.Constraint (suc (suc x)) = ⊥
--   fromNatUnitInterval .HasFromNat.fromNat zero = (0 , decℚ≤ᵣ? , decℚ≤ᵣ?)
--   fromNatUnitInterval .HasFromNat.fromNat (suc zero) = (1 , decℚ≤ᵣ? , decℚ≤ᵣ?)
--   -- record { Constraint = λ _ → Unit ; fromNat = λ n → rat [ pos n / 1 ] }


-- open BinaryRelation 


-- module ℝPaths {ℓ} (A : MetricSpace ℓ) where


--  open MetricSpaceStr (snd A)

--  data ℝPath  : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ where
--   𝕣path : (f : UContMap IntervalMetricSpace A) →
--                ℝPath   (fst f 0)
--                        (fst f 1) 


--  𝐿₁-ℝPathsMetricSpaceStr : ∀ a₀ a₁ → MetricSpaceStr (ℝPath a₀ a₁)
--  𝐿₁-ℝPathsMetricSpaceStr a₀ a₁ = {!!}
 
--  ΣℝPath : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ 
--  ΣℝPath a₀ a₁ = Σ[ f ∈ (UContMap IntervalMetricSpace A) ]
--     ((fst f 0 ≡ a₀) × (fst f 1 ≡ a₁))

--  isTransΣℝPath : isTrans ΣℝPath
--  isTransΣℝPath a b c x x₁ = {!!}
 
--  module _ (a₀ a₁ : ⟨ A ⟩) where
--   ΣℝPath→ℝPath : ΣℝPath a₀ a₁ → ℝPath a₀ a₁
--   ΣℝPath→ℝPath (f , f0 , f1) = subst2 ℝPath f0 f1 (𝕣path f)

--   ℝPath→ΣℝPath : ℝPath a₀ a₁ → ΣℝPath a₀ a₁
--   ℝPath→ΣℝPath (𝕣path f) = f , refl , refl

--   sec-IsoΣℝPathℝPath :
--     section ℝPath→ΣℝPath ΣℝPath→ℝPath
--   sec-IsoΣℝPathℝPath (f , f0 , f1) =
--     Σ≡Prop (λ _ → isProp× (is-set _ _) (is-set _ _))
--     (UContMapEq IntervalMetricSpace A _ _
--      λ x →
--        (transportRefl _ ∙ transportRefl _)
--          ∙ cong (fst f) (transportRefl _ ∙ transportRefl x))

--   IsoΣℝPathℝPath : Iso (ℝPath a₀ a₁) (ΣℝPath a₀ a₁)
--   IsoΣℝPathℝPath .Iso.fun = ℝPath→ΣℝPath
--   IsoΣℝPathℝPath .Iso.inv = ΣℝPath→ℝPath
--   IsoΣℝPathℝPath .Iso.rightInv = sec-IsoΣℝPathℝPath
--   IsoΣℝPathℝPath .Iso.leftInv (𝕣path _) = transportRefl _

--  UpToℝPath₂ : Type ℓ
--  UpToℝPath₂ = ⟨ A ⟩ / ℝPath

--  𝕣refl : ∀ x → ℝPath x x 
--  𝕣refl x = 𝕣path (const x , ∣ uContConstMap IntervalMetricSpace A x ∣₁)


--  Loops : ⟨ A ⟩ → ∙MetricSpace ℓ
--  Loops a = _ , 𝕣refl a , (𝐿₁-ℝPathsMetricSpaceStr a a)


-- module _ {ℓ} (A : MetricSpace ℓ) where

--  data Shape : Type ℓ 


--  constFromCube : ∀ n → ⟨ 𝐿₁-MetricSpaceⁿ n A ⟩ → ⟨ 𝐿₁-MetricSpaceⁿ (suc n) A ⟩
--  constFromCube n a = (λ _ → a) , {!!}
 
--  data Shape where
--   σ : ∀ n → ⟨ 𝐿₁-MetricSpaceⁿ n A ⟩ → Shape
--   σ↑ : ∀ n a x → σ n (fst a x) ≡ σ (suc n) a
--   σ≡ : ∀ n a x x' →
--           (σ↑ n (constFromCube n a) x)
--        ≡  (σ↑ n (constFromCube n a) x') 

-- --  σ-↑ : ∀ n (a : ⟨ 𝐿₁-MetricSpaceⁿ (suc (suc n)) A ⟩) →
-- --              ⟨ IntervalMetricSpace ⟩
-- --             → (x : ⟨ IntervalMetricSpace ⟩ )
-- --             → σ (suc n) (((λ t → fst (fst a t) x) , {!!})) ≡ σ (suc (suc n)) a
-- --  σ-↑ n a t₀ x =
-- --    sym (σ↑ n ((λ t → fst (fst a t) x) , _) t₀) ∙∙
-- --       σ↑ n (fst a t₀) x ∙∙ σ↑ (suc n) a t₀
 
-- --  ends-path : ∀ n → (f : ⟨ 𝐿₁-MetricSpaceⁿ (suc n) A ⟩) →
-- --         σ n (fst f 0) ≡ σ n (fst f 1)
-- --  ends-path n f = σ↑ n f 0 ∙∙
-- --     refl {x = σ (suc n) f}
-- --    ∙∙ sym (σ↑ n f 1)

-- --  ends-Σpath : ∀ n {a} {b} → ℝPaths.ΣℝPath (𝐿₁-MetricSpaceⁿ n A) a b →
-- --         σ n a ≡ σ n b
-- --  ends-Σpath n (f , f0 , f1) =
-- --     cong (σ n) (sym f0) ∙∙
-- --      ends-path n f
-- --     ∙∙ cong (σ n) f1

-- --  σ↑-comm : ∀ n (a : ⟨ 𝐿₁-MetricSpaceⁿ (suc (suc n)) A ⟩) x t₀ →
-- --     (sym (σ↑ n ((λ v → fst (fst a v) x) , _) t₀) ∙∙
-- --       σ↑ n (fst a t₀) x ∙∙ σ↑ (suc n) a t₀) ≡
-- --        sym (σ↑ n ((λ v → fst (fst a v) x) , {!!}) x)
-- --          ∙∙ σ↑ n (fst a x) x ∙∙ σ↑ (suc n) a x 
-- --  σ↑-comm = {!!}
 
-- --  sq-shape : ∀ n (f : ⟨ 𝐿₁-MetricSpaceⁿ (suc (suc n)) A ⟩)
-- --    → Square
-- --       (ends-path n (fst f 0))
-- --       (ends-path n (fst f 1))
-- --       (ends-path n ((λ x → fst (fst f x) 0) , {!!}))
-- --       (ends-path n ((λ x → fst (fst f x) 1) , {!!}))
-- --  sq-shape n f i j =
-- --    hcomp
-- --      (λ k → λ {
-- --        (i = i0) →
-- --          hcomp
-- --            (λ k' → λ {
-- --              (k = i0) → σ↑ (suc n) f 0 k'
-- --             ;(j = i0) → {!!}
-- --             ;(j = i1) → {!!}
-- --             })
-- --             (σ (suc n) (fst f 0))
-- --       ;(i = i1) →
-- --          hcomp
-- --            (λ k' → λ {
-- --              (k = i0) → σ↑ (suc n) f 1 k'
-- --             ;(j = i0) → {!!}
-- --             ;(j = i1) → {!!}
-- --             })
-- --             (σ (suc n) (fst f 1))
-- --       ;(j = i0) →
-- --           hcomp
-- --            (λ k' → λ {
-- --              (k = i0) → σ-↑ n f 0 0 k'
-- --             ;(i = i0) → {!!}
-- --             ;(i = i1) → {!!}
-- --             })
-- --             (σ-↑ n f 0 0 i0)
-- --       ;(j = i1) →
-- --           hcomp
-- --            (λ k' → λ {
-- --              (k = i0) → σ-↑ n f 0 1 k'
-- --             ;(i = i0) → {!!}
-- --             ;(i = i1) → {!!}
-- --             })
-- --             (σ-↑ n f 0 1 i0)
-- --       })
-- --      (σ (suc (suc n)) f)
-- --   where
-- --    t₀ : ⟨ IntervalMetricSpace ⟩ 
-- --    t₀ = {!!}
   
-- -- --  ends-path-comp : ∀ n a b c
-- -- --     → (f : ℝPaths.ΣℝPath (𝐿₁-MetricSpaceⁿ n A) a b)
-- -- --     → (g : ℝPaths.ΣℝPath (𝐿₁-MetricSpaceⁿ n A) b c)
-- -- --     → Square (ends-Σpath n f)
-- -- --         (ends-Σpath n
-- -- --         (ℝPaths.isTransΣℝPath (𝐿₁-MetricSpaceⁿ n A) a b c f g))
-- -- --         refl
-- -- --         (ends-Σpath n g)
-- -- --  ends-path-comp = {!!}
 
-- -- -- -- module _ where
-- -- -- --  open ℝPaths

-- -- -- --  record ElimShape {ℓ'} (A : MetricSpace ℓ) (T : Shape A → Type ℓ') :
-- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- --   field
-- -- -- --    f-σ : ∀ n a → T (σ n a)
-- -- -- --    f-σ↑ :  ∀ n a x →
-- -- -- --      PathP (λ i → T (σ↑ n a x i))
-- -- -- --        (f-σ n (fst a x))
-- -- -- --        (f-σ (suc n) a)
-- -- -- --    f-σ-refl : ∀ n a x x' →
-- -- -- --      SquareP (λ i j → T (σ-refl n a x x' i j))
-- -- -- --        (f-σ↑ n (constFromCube A n a) x)
-- -- -- --        (f-σ↑ n (constFromCube A n a) x')
-- -- -- --        refl
-- -- -- --        refl

-- -- -- --   go : ∀ x → T x
-- -- -- --   go (σ n x) = f-σ n x
-- -- -- --   go (σ↑ n a x i) = f-σ↑ n a x i
-- -- -- --   go (σ-refl n a x x' i i₁) = f-σ-refl n a x x' i i₁

-- -- -- --  record ElimShape2Groupoid {ℓ'} (A : MetricSpace ℓ)
-- -- -- --      (T : Shape A → Shape A → Type ℓ') :
-- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- --   field
-- -- -- --    isGroupoidT : ∀ x y → isGroupoid (T x y)
-- -- -- --    f-σ-σ : ∀ n a n' a' → T (σ n a) (σ n' a')
-- -- -- --    -- f-σ↑ :  ∀ n a x →
-- -- -- --    --   PathP (λ i → T (σ↑ n a x i))
-- -- -- --    --     (f-σ n (fst a x))
-- -- -- --    --     (f-σ (suc n) a)
-- -- -- --    -- f-σ-refl : ∀ n a x x' →
-- -- -- --    --   SquareP (λ i j → T (σ-refl n a x x' i j))
-- -- -- --    --     (f-σ↑ n (constFromCube A n a) x)
-- -- -- --    --     (f-σ↑ n (constFromCube A n a) x')
-- -- -- --    --     refl
-- -- -- --    --     refl

-- -- -- --   go : ∀ x y → T x y
-- -- -- --   go = ElimShape.go w
-- -- -- --    where
-- -- -- --    w : ElimShape A (λ z → (y : Shape A) → T z y)
-- -- -- --    w .ElimShape.f-σ n a = ElimShape.go ww
-- -- -- --     where
-- -- -- --     ww : ElimShape A (λ z → T (σ n a) z)
-- -- -- --     ww .ElimShape.f-σ = f-σ-σ n a
-- -- -- --     ww .ElimShape.f-σ↑ = {!!}
-- -- -- --     ww .ElimShape.f-σ-refl = {!!}
-- -- -- --    w .ElimShape.f-σ↑ = {!!}
-- -- -- --    w .ElimShape.f-σ-refl = {!!}


-- -- -- --   -- path : (p : UContMap IntervalMetricSpace A)
-- -- -- --   --          → pt (fst p 0) ≡ pt (fst p 1)
-- -- -- --   -- sq : (s : UContMap Interval²MetricSpace A)
-- -- -- --   --          → Square
-- -- -- --   --              (path ((λ x → fst s (0 , x)) , {!!}))
-- -- -- --   --              (path ((λ x → fst s (1 , x)) , {!!}))
-- -- -- --   --              (path ((λ x → fst s (x , 0)) , {!!}))
-- -- -- --   --              (path ((λ x → fst s (x , 1)) , {!!}))
-- -- -- --   -- const≡refl : ∀ a icid → path ((λ _ → a) , icid) ≡ λ _ → pt a




-- -- -- -- -- isUContMap∘ : ∀ {ℓ ℓ' ℓ''}
-- -- -- -- --   → (A : MetricSpace ℓ)
-- -- -- -- --   → (B : MetricSpace ℓ')
-- -- -- -- --   → (C : MetricSpace ℓ'')
-- -- -- -- --   → ∀ f g
-- -- -- -- --   → IsUContMap (snd B) f (snd C)
-- -- -- -- --   → IsUContMap (snd A) g (snd B)
-- -- -- -- --   → IsUContMap (snd A) (f ∘ g) (snd C)  
-- -- -- -- -- isUContMap∘ = {!!}

-- -- -- -- -- uContConstMap : ∀ {ℓ ℓ'}
-- -- -- -- --   → (A : MetricSpace ℓ)
-- -- -- -- --   → (B : MetricSpace ℓ')
-- -- -- -- --   → (b : ⟨ B ⟩) → IsUContMap (snd A) (const b) (snd B) 
-- -- -- -- -- uContConstMap A B a = (λ ε → 1 , λ _ _ _ → isTrans≡<ᵣ _ _ _ {!!} {!!} )

-- -- -- -- -- IntervalMetricSpace : MetricSpace₀
-- -- -- -- -- IntervalMetricSpace = _ , MetricSubSpace _  (intervalℙ 0 1) (snd ℝMetricSpace)

-- -- -- -- -- Interval²MetricSpaceStr : MetricSpaceStr
-- -- -- -- --  ((Σ ℝ (_∈ intervalℙ 0 1)) × (Σ ℝ (_∈ intervalℙ 0 1)))
-- -- -- -- -- Interval²MetricSpaceStr = {!!}

-- -- -- -- -- Interval²MetricSpace : MetricSpace₀
-- -- -- -- -- Interval²MetricSpace = (Σ ℝ (_∈ intervalℙ 0 1)) × (Σ ℝ (_∈ intervalℙ 0 1))
-- -- -- -- --   , Interval²MetricSpaceStr
-- -- -- -- --   --MetricSubSpace _  (intervalℙ 0 1) (snd ℝMetricSpace)


-- -- -- -- -- 𝐿₁-Metric : ∀ {ℓ}
-- -- -- -- --   → (A : MetricSpace ℓ)
-- -- -- -- --   → UContMap IntervalMetricSpace A
-- -- -- -- --   → UContMap IntervalMetricSpace A → ℝ 
-- -- -- -- -- 𝐿₁-Metric A f g = {!!}

-- -- -- -- -- UContMapEq : ∀ {ℓ ℓ'} → (A : MetricSpace ℓ)
-- -- -- -- --           → (A' : MetricSpace ℓ') →
-- -- -- -- --             (f g : UContMap A A')
-- -- -- -- --             → (∀ x → fst f x ≡ fst g x ) → f ≡ g
-- -- -- -- -- UContMapEq A A' f g x = Σ≡Prop (λ _ → squash₁) (funExt x)


-- -- -- -- -- private
-- -- -- -- --  variable
-- -- -- -- --   ℓ ℓ' : Level

-- -- -- -- -- ∙MetricSpaceStr : Type ℓ → Type ℓ
-- -- -- -- -- ∙MetricSpaceStr = ProductStructure PointedStructure MetricSpaceStr

-- -- -- -- -- ∙MetricSpace : ∀ ℓ → Type (ℓ-suc ℓ)
-- -- -- -- -- ∙MetricSpace ℓ = TypeWithStr ℓ ∙MetricSpaceStr

-- -- -- -- -- ∙MetricSpace→Pointed : ∀ {ℓ} → ∙MetricSpace ℓ → P.Pointed ℓ
-- -- -- -- -- ∙MetricSpace→Pointed (A , a , _) = (A , a)

-- -- -- -- -- ∙MetricSpace→MetricSpace : ∀ {ℓ} → ∙MetricSpace ℓ → MetricSpace ℓ
-- -- -- -- -- ∙MetricSpace→MetricSpace (_ , _ , A) = (_ , A)


-- -- -- -- -- instance
-- -- -- -- --   fromNatUnitInterval : HasFromNat (Σ _ (_∈ intervalℙ 0 1))
-- -- -- -- --   fromNatUnitInterval .HasFromNat.Constraint zero = Unit
-- -- -- -- --   fromNatUnitInterval .HasFromNat.Constraint (suc zero) = Unit
-- -- -- -- --   fromNatUnitInterval .HasFromNat.Constraint (suc (suc x)) = ⊥
-- -- -- -- --   fromNatUnitInterval .HasFromNat.fromNat zero = (0 , decℚ≤ᵣ? , decℚ≤ᵣ?)
-- -- -- -- --   fromNatUnitInterval .HasFromNat.fromNat (suc zero) = (1 , decℚ≤ᵣ? , decℚ≤ᵣ?)
-- -- -- -- --   -- record { Constraint = λ _ → Unit ; fromNat = λ n → rat [ pos n / 1 ] }

-- -- -- -- -- PathIdTrunc₁Iso : {A : Type ℓ} {a b : A} → Iso (∣ a ∣₃ ≡ ∣ b ∣₃) ∥ a ≡ b ∥₂
-- -- -- -- -- PathIdTrunc₁Iso = {!!}

-- -- -- -- -- module ℝPaths {ℓ} (A : MetricSpace ℓ) where

-- -- -- -- --  open MetricSpaceStr (snd A)

-- -- -- -- --  data ℝPath  : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ where
-- -- -- -- --   𝕣path : (f : UContMap IntervalMetricSpace A) →
-- -- -- -- --                ℝPath   (fst f 0)
-- -- -- -- --                        (fst f 1) 



-- -- -- -- --  data Pieces : Type ℓ where
-- -- -- -- --   pt : ⟨ A ⟩ → Pieces
-- -- -- -- --   path : (p : UContMap IntervalMetricSpace A)
-- -- -- -- --            → pt (fst p 0) ≡ pt (fst p 1)
-- -- -- -- --   sq : (s : UContMap Interval²MetricSpace A)
-- -- -- -- --            → Square
-- -- -- -- --                (path ((λ x → fst s (0 , x)) , {!!}))
-- -- -- -- --                (path ((λ x → fst s (1 , x)) , {!!}))
-- -- -- -- --                (path ((λ x → fst s (x , 0)) , {!!}))
-- -- -- -- --                (path ((λ x → fst s (x , 1)) , {!!}))
-- -- -- -- --   const≡refl : ∀ a icid → path ((λ _ → a) , icid) ≡ λ _ → pt a



 
-- -- -- -- --  ΣℝPath : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ 
-- -- -- -- --  ΣℝPath a₀ a₁ = Σ[ f ∈ (UContMap IntervalMetricSpace A) ]
-- -- -- -- --     ((fst f 0 ≡ a₀) × (fst f 1 ≡ a₁))

-- -- -- -- --  module _ (a₀ a₁ : ⟨ A ⟩) where
-- -- -- -- --   ΣℝPath→ℝPath : ΣℝPath a₀ a₁ → ℝPath a₀ a₁
-- -- -- -- --   ΣℝPath→ℝPath (f , f0 , f1) = subst2 ℝPath f0 f1 (𝕣path f)

-- -- -- -- --   ℝPath→ΣℝPath : ℝPath a₀ a₁ → ΣℝPath a₀ a₁
-- -- -- -- --   ℝPath→ΣℝPath (𝕣path f) = f , refl , refl

-- -- -- -- --   sec-IsoΣℝPathℝPath :
-- -- -- -- --     section ℝPath→ΣℝPath ΣℝPath→ℝPath
-- -- -- -- --   sec-IsoΣℝPathℝPath (f , f0 , f1) =
-- -- -- -- --     Σ≡Prop (λ _ → isProp× (is-set _ _) (is-set _ _))
-- -- -- -- --     (UContMapEq IntervalMetricSpace A _ _
-- -- -- -- --      λ x →
-- -- -- -- --        (transportRefl _ ∙ transportRefl _)
-- -- -- -- --          ∙ cong (fst f) (transportRefl _ ∙ transportRefl x))

-- -- -- -- --   IsoΣℝPathℝPath : Iso (ℝPath a₀ a₁) (ΣℝPath a₀ a₁)
-- -- -- -- --   IsoΣℝPathℝPath .Iso.fun = ℝPath→ΣℝPath
-- -- -- -- --   IsoΣℝPathℝPath .Iso.inv = ΣℝPath→ℝPath
-- -- -- -- --   IsoΣℝPathℝPath .Iso.rightInv = sec-IsoΣℝPathℝPath
-- -- -- -- --   IsoΣℝPathℝPath .Iso.leftInv (𝕣path _) = transportRefl _

-- -- -- -- --  UpToℝPath₂ : Type ℓ
-- -- -- -- --  UpToℝPath₂ = ⟨ A ⟩ / ℝPath

-- -- -- -- --  open BinaryRelation 

-- -- -- -- --  opaque
-- -- -- -- --   isTransℝPath : isTrans ℝPath
-- -- -- -- --   isTransℝPath a b c d x₁ = {!!}

-- -- -- -- --   isTransℝPath-const : ∀ x cid → isTransℝPath x x x (𝕣path ((λ _ → x) , cid))
-- -- -- -- --        (𝕣path ((λ _ → x) , cid))
-- -- -- -- --        ≡ 𝕣path ((λ _ → x) , cid) 
-- -- -- -- --   isTransℝPath-const = {!!}


-- -- -- -- --  𝕣path→path : ∀ {a₀ a₁} → ℝPath a₀ a₁ → pt a₀ ≡ pt a₁ 
-- -- -- -- --  𝕣path→path (𝕣path f) = path f
 
-- -- -- -- --  comp-𝕣paths : ∀ {a} {b} {c}
-- -- -- -- --    (r : ℝPath a b)
-- -- -- -- --    (s : ℝPath b c) →
-- -- -- -- --     Square
-- -- -- -- --      (𝕣path→path r )
-- -- -- -- --       (𝕣path→path (isTransℝPath _ _ _ r s))
-- -- -- -- --       refl
-- -- -- -- --       (𝕣path→path s)
-- -- -- -- --  comp-𝕣paths r s = {!r !}


-- -- -- -- --   --  cong (cong ∣_∣₃ ∘ 𝕣path→path)
-- -- -- -- --   --       (sym ((IsoΣℝPathℝPath _  _ .Iso.leftInv) r))
-- -- -- -- --   --      ◁ congP (λ _ → cong ∣_∣₃) (ww (ℝPath→ΣℝPath a b r) s) ▷
-- -- -- -- --   --         cong (cong ∣_∣₃ ∘ 𝕣path→path ∘ flip (isTransℝPath a b c) s)
-- -- -- -- --   --          ((IsoΣℝPathℝPath _  _ .Iso.leftInv) r)

-- -- -- -- --   -- where
-- -- -- -- --   -- -- w : {a b : ⟨ A ⟩} → ℝPath a b → pt a ≡ pt b
-- -- -- -- --   -- -- w (ℝPaths.𝕣path f) = (path f)

-- -- -- -- --   -- ww : {a b c : ⟨ A ⟩} (r : ΣℝPath a b) (s : ℝPath b c) →
-- -- -- -- --   --     Square (𝕣path→path (ΣℝPath→ℝPath a b r))
-- -- -- -- --   --            (𝕣path→path (isTransℝPath a b c (ΣℝPath→ℝPath a b r) s))
-- -- -- -- --   --       refl (𝕣path→path s)
-- -- -- -- --   -- ww {a} {b} {c} (f , f0 , f1) (ℝPaths.𝕣path g) =
-- -- -- -- --   --   wwwL ◁ {!!}
-- -- -- -- --   --     ▷ {!!}
-- -- -- -- --   -- -- www
-- -- -- -- --   --  where
-- -- -- -- --   --  wwwL : 𝕣path→path (subst2 ℝPath f0 f1 (𝕣path f))
-- -- -- -- --   --           ≡ (cong pt (sym f0) ∙∙
-- -- -- -- --   --                path f
-- -- -- -- --   --                ∙∙ cong pt f1)
-- -- -- -- --   --  wwwL = {!!}
-- -- -- -- --   --  www : {!!}
-- -- -- -- --   --  www = {!!}


-- -- -- -- --  UpToℝPath₃ : Type ℓ
-- -- -- -- --  UpToℝPath₃ = ⟨ A ⟩ // isTransℝPath



-- -- -- -- --  𝐿₁-ℝPathsMetricSpaceStr : ∀ a₀ a₁ → MetricSpaceStr (ℝPath a₀ a₁)
-- -- -- -- --  𝐿₁-ℝPathsMetricSpaceStr a₀ a₁ = {!!}

-- -- -- -- --  𝕣refl : ∀ x → ℝPath x x 
-- -- -- -- --  𝕣refl x = 𝕣path (const x , ∣ uContConstMap IntervalMetricSpace A x ∣₁)

-- -- -- -- --  -- 𝕣sym : ∀ x y → ℝPath x y →  ℝPath y x 
-- -- -- -- --  -- 𝕣sym x y (𝕣path (f , fc)) = 𝕣path ({!!} , {!!})

-- -- -- -- -- -- module ℝLoopspace {ℓ} (A : ∙MetricSpace ℓ) where

-- -- -- -- --  Loops : ⟨ A ⟩ → ∙MetricSpace ℓ
-- -- -- -- --  Loops a = _ , 𝕣refl a , (𝐿₁-ℝPathsMetricSpaceStr a a)

-- -- -- -- -- module _ where
-- -- -- -- --  open ℝPaths

-- -- -- -- --  record ElimPieces {ℓ'} (A : MetricSpace ℓ) (T : Pieces A → Type ℓ') :
-- -- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- -- --   field
-- -- -- -- --    pt-f : ∀ x → T (pt x) 
-- -- -- -- --    path-f : ∀ p → PathP (λ i → T (path p i))
-- -- -- -- --      (pt-f (fst p 0))
-- -- -- -- --      (pt-f (fst p 1))
-- -- -- -- --    sq-f : ∀ s →
-- -- -- -- --      SquareP (λ i j → T (sq s i j))
-- -- -- -- --        (path-f ((λ x → fst s (0 , x)) , {!!}))
-- -- -- -- --        (path-f ((λ x → fst s (1 , x)) , {!!}))
-- -- -- -- --        (path-f ((λ x → fst s (x , 0)) , {!!}))
-- -- -- -- --        (path-f ((λ x → fst s (x , 1)) , {!!}))
       
-- -- -- -- --    const≡refl-f : ∀ x cid →
-- -- -- -- --      SquareP (λ i j → T (const≡refl x cid i j))
-- -- -- -- --        (path-f ((λ _ → x) , cid))
-- -- -- -- --        refl
-- -- -- -- --        refl
-- -- -- -- --        refl

-- -- -- -- --   go : ∀ x → T x
-- -- -- -- --   go (pt x) = pt-f x
-- -- -- -- --   go (path p i) = path-f p i
-- -- -- -- --   go (sq s i j) = sq-f s i j  
-- -- -- -- --   go (const≡refl a cid i i₁) = const≡refl-f a cid i i₁

-- -- -- -- --  record ElimPiecesSet {ℓ'} (A : MetricSpace ℓ) (T : Pieces A → Type ℓ') :
-- -- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- -- --   no-eta-equality
-- -- -- -- --   field
-- -- -- -- --    pt-f : ∀ x → T (pt x) 
-- -- -- -- --    path-f : ∀ p → PathP (λ i → T (path p i))
-- -- -- -- --      (pt-f (fst p 0))
-- -- -- -- --      (pt-f (fst p 1))
-- -- -- -- --    isSetT : ∀ x → isSet (T x)

-- -- -- -- --   go : ∀ x → T x
-- -- -- -- --   go = ElimPieces.go w
-- -- -- -- --    where
-- -- -- -- --    w : ElimPieces A T
-- -- -- -- --    w .ElimPieces.pt-f = pt-f
-- -- -- -- --    w .ElimPieces.path-f = path-f
-- -- -- -- --    w .ElimPieces.sq-f s =
-- -- -- -- --      isSet→SquareP {A = λ i j → T (sq s i j)}
-- -- -- -- --       (λ i j → isSetT (sq s i j))
-- -- -- -- --        (path-f ((λ x → fst s (0 , x)) , {!!}))
-- -- -- -- --        (path-f ((λ x → fst s (1 , x)) , {!!}))
-- -- -- -- --        (path-f ((λ x → fst s (x , 0)) , {!!}))
-- -- -- -- --        (path-f ((λ x → fst s (x , 1)) , {!!})) 

-- -- -- -- --    w .ElimPieces.const≡refl-f x _ =
-- -- -- -- --      isSet→SquareP (λ _ _ → isSetT _) _ _ _ _ 

-- -- -- -- --  record ElimPiecesProp {ℓ'} (A : MetricSpace ℓ) (T : Pieces A → Type ℓ') :
-- -- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- -- --   no-eta-equality
-- -- -- -- --   field
-- -- -- -- --    pt-f : ∀ x → T (pt x) 
-- -- -- -- --    isPropT : ∀ x → isProp (T x)

-- -- -- -- --   go : ∀ x → T x
-- -- -- -- --   go = ElimPiecesSet.go w
-- -- -- -- --    where
-- -- -- -- --    w : ElimPiecesSet A (λ z → T z)
-- -- -- -- --    w .ElimPiecesSet.pt-f = pt-f
-- -- -- -- --    w .ElimPiecesSet.path-f _ = isProp→PathP (λ _ → isPropT _) _ _ 
-- -- -- -- --    w .ElimPiecesSet.isSetT _ = isProp→isSet (isPropT _)

-- -- -- -- --  record ElimPiecesSet₂ {ℓ'} (A B : MetricSpace ℓ)
-- -- -- -- --    (T : Pieces A → Pieces B → Type ℓ') :
-- -- -- -- --    Type (ℓ-max ℓ ℓ') where
-- -- -- -- --   no-eta-equality
-- -- -- -- --   field
-- -- -- -- --    pt-pt-f : ∀ a b → T (pt a) (pt b)
-- -- -- -- --    pt-path-f : ∀ a p
-- -- -- -- --      → PathP (λ i → T (pt a) (path p i))
-- -- -- -- --      (pt-pt-f a (fst p 0))
-- -- -- -- --      (pt-pt-f a (fst p 1))
-- -- -- -- --    path-pt-f : ∀ p b
-- -- -- -- --      → PathP (λ i → T (path p i) (pt b))
-- -- -- -- --      (pt-pt-f (fst p 0) b)
-- -- -- -- --      (pt-pt-f (fst p 1) b)
-- -- -- -- --    isSetT : ∀ x y → isSet (T x y)

-- -- -- -- --   go : ∀ x y → T x y
-- -- -- -- --   go = ElimPiecesSet.go w
-- -- -- -- --    where
-- -- -- -- --     w : ElimPiecesSet A (λ z → (y : Pieces B) → T z y)
-- -- -- -- --     w .ElimPiecesSet.pt-f x = ElimPiecesSet.go ww
-- -- -- -- --      where
-- -- -- -- --      ww : ElimPiecesSet B (λ z → T (pt x) z)
-- -- -- -- --      ww .ElimPiecesSet.pt-f = pt-pt-f x
-- -- -- -- --      ww .ElimPiecesSet.path-f = pt-path-f x
-- -- -- -- --      ww .ElimPiecesSet.isSetT _ = isSetT _ _

-- -- -- -- --     w .ElimPiecesSet.path-f p = funExt (ElimPiecesProp.go ww)
-- -- -- -- --      where
-- -- -- -- --      ww : ElimPiecesProp B
-- -- -- -- --            (λ z →
-- -- -- -- --               PathP (λ z₁ → T (path p z₁) z)
-- -- -- -- --               (w .ElimPiecesSet.pt-f (fst p 0) z)
-- -- -- -- --               (w .ElimPiecesSet.pt-f (fst p 1) z))
-- -- -- -- --      ww .ElimPiecesProp.pt-f b = path-pt-f p b
-- -- -- -- --      ww .ElimPiecesProp.isPropT x = isOfHLevelPathP' 1 (isSetT _ _) _ _
-- -- -- -- --     w .ElimPiecesSet.isSetT _ = isSetΠ λ _ → isSetT _ _

-- -- -- -- -- module _ (A : MetricSpace ℓ) where
-- -- -- -- --  open ℝPaths A
-- -- -- -- --  ∥Pieces∥₂→UpToℝPath⟨A⟩ : ∥ Pieces ∥₂ → UpToℝPath₂
-- -- -- -- --  ∥Pieces∥₂→UpToℝPath⟨A⟩ = ST.rec squash/
-- -- -- -- --    (ElimPiecesSet.go w)
-- -- -- -- --   where
-- -- -- -- --   w : ElimPiecesSet _ _
-- -- -- -- --   w .ElimPiecesSet.pt-f x = [ x ]/  
-- -- -- -- --   w .ElimPiecesSet.path-f p = eq/ _ _ (𝕣path p)
-- -- -- -- --   w .ElimPiecesSet.isSetT _ = squash/ 

-- -- -- -- --  UpToℝPath⟨A⟩→∥Pieces∥₂ : UpToℝPath₂ → ∥ Pieces ∥₂
-- -- -- -- --  UpToℝPath⟨A⟩→∥Pieces∥₂ = SQ.Rec.go w 
-- -- -- -- --   where
-- -- -- -- --   w : Rec _
-- -- -- -- --   w .Rec.isSetB = squash₂
-- -- -- -- --   w .Rec.f = ∣_∣₂ ∘ pt
-- -- -- -- --   w .Rec.f∼ a a' (𝕣path f) = cong ∣_∣₂ (path f)

-- -- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ : Iso ∥ Pieces ∥₂ UpToℝPath₂
-- -- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ .Iso.fun = ∥Pieces∥₂→UpToℝPath⟨A⟩
-- -- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ .Iso.inv = UpToℝPath⟨A⟩→∥Pieces∥₂
-- -- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ .Iso.rightInv =
-- -- -- -- --    SQ.ElimProp.go w
-- -- -- -- --   where
-- -- -- -- --   w : ElimProp _
-- -- -- -- --   w .ElimProp.isPropB _ = squash/ _ _
-- -- -- -- --   w .ElimProp.f _ = refl
-- -- -- -- --  IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ .Iso.leftInv =
-- -- -- -- --   ST.elim (λ _ → isProp→isSet (squash₂ _ _))
-- -- -- -- --    (ElimPiecesProp.go w)
-- -- -- -- --    where
-- -- -- -- --    w : ElimPiecesProp _ _
-- -- -- -- --    w .ElimPiecesProp.pt-f _ = refl
-- -- -- -- --    w .ElimPiecesProp.isPropT _ = squash₂ _ _

-- -- -- -- --  -- ∥Pieces∥₃→UpToℝPath⟨A⟩ : ∥ Pieces ∥₃ → UpToℝPath₃
-- -- -- -- --  -- ∥Pieces∥₃→UpToℝPath⟨A⟩ = GT.rec squash//
-- -- -- -- --  --   (ElimPieces.go w)
-- -- -- -- --  --  where
-- -- -- -- --  --  ww : ∀ p → _ ≡ _
-- -- -- -- --  --  ww p = eq// (𝕣path p)
-- -- -- -- --  --  w : ElimPieces _ _
-- -- -- -- --  --  w .ElimPieces.pt-f x = [ x ]// 
-- -- -- -- --  --  w .ElimPieces.path-f = ww
-- -- -- -- --  --  w .ElimPieces.sq-f s =
-- -- -- -- --  --    compPath→Square
-- -- -- -- --  --      (sym (comp'// _ isTransℝPath _ _) ∙∙
-- -- -- -- --  --       {!
-- -- -- -- --  --       !}
-- -- -- -- --  --       ∙∙ comp'// _ isTransℝPath _ _)
-- -- -- -- --  --  w .ElimPieces.const≡refl-f x cid =
-- -- -- -- --  --   refl≡Id isTransℝPath (𝕣path ((λ _ → x) , cid)) (isTransℝPath-const x cid) 
    
  
-- -- -- -- --  -- UpToℝPath₃⟨A⟩→∥Pieces∥₃ : UpToℝPath₃ → ∥ Pieces ∥₃
-- -- -- -- --  -- UpToℝPath₃⟨A⟩→∥Pieces∥₃ = GQ.rec
-- -- -- -- --  --   isTransℝPath
-- -- -- -- --  --   squash₃
-- -- -- -- --  --   (∣_∣₃ ∘ pt)
-- -- -- -- --  --   (cong ∣_∣₃ ∘ 𝕣path→path)
-- -- -- -- --  --   λ {a} {b} {c} r s i j →
-- -- -- -- --  --     ∣ comp-𝕣paths r s i j ∣₃

-- -- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ : Iso ∥ Pieces ∥₃ UpToℝPath₃
-- -- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ .Iso.fun = ∥Pieces∥₃→UpToℝPath⟨A⟩
-- -- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ .Iso.inv = UpToℝPath₃⟨A⟩→∥Pieces∥₃
-- -- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ .Iso.rightInv =
-- -- -- -- -- --    GQ.elimSet isTransℝPath
-- -- -- -- -- --     (λ _ → squash// _ _)
-- -- -- -- -- --     (λ _ → refl)
-- -- -- -- -- --     λ { (ℝPaths.𝕣path f) i j → eq// (𝕣path f) i }
   
-- -- -- -- -- --  IsoUpToℝPath₃⟨A⟩→∥Pieces∥₃ .Iso.leftInv =
-- -- -- -- -- --   GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- -- --    (ElimPiecesSet.go w)
   
-- -- -- -- -- --   where
-- -- -- -- -- --   w : ElimPiecesSet _ _
-- -- -- -- -- --   w .ElimPiecesSet.pt-f _ = refl
-- -- -- -- -- --   w .ElimPiecesSet.path-f p i _ = ∣ path p i ∣₃
-- -- -- -- -- --   w .ElimPiecesSet.isSetT _ = squash₃ _ _



-- -- -- -- -- {- loop space of a pointed metric space -}
-- -- -- -- -- Ω : ∙MetricSpace ℓ → ∙MetricSpace ℓ
-- -- -- -- -- Ω (_ , a , m) = ℝPaths.Loops (_ , m) a


-- -- -- -- -- Ω^_ : ∀ {ℓ} → ℕ → ∙MetricSpace ℓ → ∙MetricSpace ℓ
-- -- -- -- -- (Ω^ 0) p = p
-- -- -- -- -- (Ω^ (suc n)) p = Ω ((Ω^ n) p)

-- -- -- -- -- module _ {ℓ} (A : MetricSpace ℓ) where

-- -- -- -- --  open ℝPaths A 
 
-- -- -- -- --  ℝPathGroupoid : Category ℓ ℓ
-- -- -- -- --  ℝPathGroupoid .Category.ob = ⟨ A ⟩
-- -- -- -- --  ℝPathGroupoid .Category.Hom[_,_] x y =
-- -- -- -- --    ℝPaths.UpToℝPath₂ (_ , 𝐿₁-ℝPathsMetricSpaceStr x y)
-- -- -- -- --  ℝPathGroupoid .Category.id = [ 𝕣refl _ ]/
-- -- -- -- --  ℝPathGroupoid .Category._⋆_ = {!!}
-- -- -- -- --  ℝPathGroupoid .Category.⋆IdL = {!!}
-- -- -- -- --  ℝPathGroupoid .Category.⋆IdR = {!!}
-- -- -- -- --  ℝPathGroupoid .Category.⋆Assoc = {!!}
-- -- -- -- --  ℝPathGroupoid .Category.isSetHom = squash/

-- -- -- -- --  ℝLoopGroup : ⟨ A ⟩ → Group ℓ
-- -- -- -- --  ℝLoopGroup x .fst = ℝPaths.UpToℝPath₂ (_ , 𝐿₁-ℝPathsMetricSpaceStr x x)
-- -- -- -- --  ℝLoopGroup x .snd .GroupStr.1g = [ 𝕣refl _ ]/
-- -- -- -- --  ℝLoopGroup x .snd .GroupStr._·_ = {!!}
-- -- -- -- --  ℝLoopGroup x .snd .GroupStr.inv = {!!}
-- -- -- -- --  ℝLoopGroup x .snd .GroupStr.isGroup = {!!}
 
-- -- -- -- -- -- module n-fold-ℝLoopspace {ℓ} (A : ∙MetricSpace ℓ) where

-- -- -- -- -- πGr : ∀ {ℓ} (n : ℕ) (A : ∙MetricSpace ℓ) → Group ℓ
-- -- -- -- -- πGr n A₀ =
-- -- -- -- --  let (_ , a , A) = (Ω^ (suc n)) A₀
-- -- -- -- --  in ℝLoopGroup (_ , A) a

-- -- -- -- -- Piecesₙ : ℕ → MetricSpace ℓ → Type ℓ
-- -- -- -- -- Piecesₙ = {!!}

-- -- -- -- -- -- ℝⁿ-MetricSpaceStr : {!!}
-- -- -- -- -- -- ℝⁿ-MetricSpaceStr = {!!}

-- -- -- -- -- -- Intervalⁿ-MetricSpace : ℕ → MetricSpace₀
-- -- -- -- -- -- Intervalⁿ-MetricSpace = {!!}

-- -- -- -- -- module _ {ℓ} (A : MetricSpace ℓ) where


-- -- -- -- --  Π-seqₙ : ℕ → Type ℓ
-- -- -- -- --  Π-seqₙ n = ℝPaths.Pieces (𝐿₁-MetricSpaceⁿ n A)
-- -- -- -- --  -- UContMap (Intervalⁿ-MetricSpace n) A

-- -- -- -- --  Π-seqₙ-map : ∀ n → Π-seqₙ n → Π-seqₙ (suc n)
-- -- -- -- --  Π-seqₙ-map n = mapPieces (𝐿₁-MetricSpaceⁿ n A)
-- -- -- -- --   (𝐿₁-MetricSpaceⁿ (suc n) A)
-- -- -- -- --    ((λ x → _ ,
-- -- -- -- --     ∣ uContConstMap IntervalMetricSpace (𝐿₁-MetricSpaceⁿ n A) x ∣₁) ,
-- -- -- -- --      ∣ {!!} ∣₁)
 
-- -- -- -- --  Π-seq : Sequence ℓ
-- -- -- -- --  Π-seq .Sequence.obj = Π-seqₙ
-- -- -- -- --  Π-seq .Sequence.map = Π-seqₙ-map _

-- -- -- -- --  Π : Type ℓ 
-- -- -- -- --  Π = SeqColim Π-seq

-- -- -- -- --  ∙Π : ⟨ A ⟩ → P.Pointed ℓ
-- -- -- -- --  ∙Π a = Π , incl {n = 0} (ℝPaths.pt a)

-- -- -- -- --  -- UpToℝPath⟨A⟩→∥Π∥₂ : ∥ ? ∥₂  → ∥ Π ∥₂ 
-- -- -- -- --  -- UpToℝPath⟨A⟩→∥Π∥₂ = SQ.Rec.go w 
-- -- -- -- --  --  where
-- -- -- -- --  --  w : Rec _
-- -- -- -- --  --  w .Rec.isSetB = squash₂
-- -- -- -- --  --  w .Rec.f = ∣_∣₂ ∘ incl {n = 0} ∘ (ℝPaths.pt)
-- -- -- -- --  --  w .Rec.f∼ a a' (ℝPaths.𝕣path f) = 
-- -- -- -- --  --   cong (∣_∣₂ ∘ incl) (ℝPaths.path f)

             
                 
 
-- -- -- -- --  evalFromCubeDiag : ∀ n → ⟨ IntervalMetricSpace ⟩
-- -- -- -- --                         → UContMap (𝐿₁-MetricSpaceⁿ n A) A
-- -- -- -- --  evalFromCubeDiag zero _ = {!!}
-- -- -- -- --  evalFromCubeDiag (suc n) t = {!!}


-- -- -- -- --  liftPath : ∀ (p : UContMap IntervalMetricSpace A) → Square {A = Π}
-- -- -- -- --               (cong (incl {n = 0}) (ℝPaths.path p))
-- -- -- -- --               (cong (incl {n = 1}) (ℝPaths.path ((λ x → (λ _ → fst p x) ,
-- -- -- -- --                  {!!}) , {!!})))
-- -- -- -- --               (push (ℝPaths.pt (p .fst 0)))
-- -- -- -- --               (push (ℝPaths.pt (p .fst 1)))
-- -- -- -- --  liftPath p i j = push {n = 0} (ℝPaths.path p j ) i


-- -- -- -- --  liftPath' : ∀ (p : UContMap IntervalMetricSpace A) → Square {A = Π}
-- -- -- -- --               (cong (incl {n = 0}) (ℝPaths.path p))
-- -- -- -- --               (cong (incl {n = 1}) (ℝPaths.path ((λ x → (λ _ → fst p x) ,
-- -- -- -- --                  {!!}) , {!!})))
-- -- -- -- --               {!!}
-- -- -- -- --               {!!}
-- -- -- -- --  liftPath' p i j = {!!}


-- -- -- -- --  -- a = evalFromCubeDiag n t (fst a t)
 
-- -- -- -- --  -- ∥Πₙ∥₂→UpToℝPath⟨A⟩ : ∀ n → ∥ Π-seqₙ n ∥₂ → ℝPaths.UpToℝPath A
-- -- -- -- --  -- ∥Πₙ∥₂→UpToℝPath⟨A⟩ n = ST.rec squash/
-- -- -- -- --  --   (ElimPiecesSet.go w)
-- -- -- -- --  --  where
-- -- -- -- --  --  w : ElimPiecesSet (𝐿₁-MetricSpaceⁿ n A) (λ _ → ℝPaths.UpToℝPath A)
-- -- -- -- --  --  w .ElimPiecesSet.pt-f = [_]/ ∘ fst (evalFromCubeDiag n 0)
-- -- -- -- --  --  w .ElimPiecesSet.path-f p = eq/ _ _ (ℝPaths.𝕣path {!!})
-- -- -- -- --  --  w .ElimPiecesSet.isSetT _ = squash/ 
  
-- -- -- -- --  -- ∥Π∥₂→UpToℝPath⟨A⟩ : ∥ Π ∥₂ → ∥ ℝPaths.Pieces A ∥₂
-- -- -- -- --  -- ∥Π∥₂→UpToℝPath⟨A⟩ = ST.rec squash/
-- -- -- -- --  --   (Seq.elim _ _ (elimdata (λ {n} → ElimPiecesSet.go (w n))
-- -- -- -- --  --     {!!}))
-- -- -- -- --  --   where
-- -- -- -- --  --   w : ∀ n → ElimPiecesSet _ _
-- -- -- -- --  --   w n .ElimPiecesSet.pt-f = [_]/ ∘ fst (evalFromCubeDiag n 0)
-- -- -- -- --  --   w n .ElimPiecesSet.path-f p = eq/ _ _ (ℝPaths.𝕣path {!p!})
-- -- -- -- --  --   w n .ElimPiecesSet.isSetT _ = squash/
   
-- -- -- -- --  -- Π₁≃ : ℝPaths.UpToℝPath A ≃ ∥ Π ∥₂
-- -- -- -- --  -- Π₁≃ = isoToEquiv (invIso (IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ A)) ∙ₑ
-- -- -- -- --  --   {!!} 

-- -- -- -- --  Π-isInfGpd₂-fun : ∀ (a : ⟨ A ⟩) n →  ∥
-- -- -- -- --       ℝPaths.Pieces
-- -- -- -- --       ((Ω^ n) (fst A , a , snd A) .fst ,
-- -- -- -- --        (Ω^ n) (fst A , a , snd A) .snd .snd)
-- -- -- -- --       ∥₂ →
-- -- -- -- --       ∥ fst ((Lsp.Ω^ n) (∙Π a)) ∥₂
-- -- -- -- --  Π-isInfGpd₂-fun a zero = {!!}
-- -- -- -- --  Π-isInfGpd₂-fun a (suc n) = {!!}
 
-- -- -- -- --  Π-isInfGpd₂ : ∀ (a : ⟨ A ⟩) n → Iso ∥
-- -- -- -- --       ℝPaths.Pieces
-- -- -- -- --       ((Ω^ n) (fst A , a , snd A) .fst ,
-- -- -- -- --        (Ω^ n) (fst A , a , snd A) .snd .snd)
-- -- -- -- --       ∥₂
-- -- -- -- --       ∥ fst ((Lsp.Ω^ n) (∙Π a)) ∥₂
-- -- -- -- --  Π-isInfGpd₂ a zero = {!!}
-- -- -- -- --  Π-isInfGpd₂ a (suc n) =
-- -- -- -- --    compIso {!!}  PathIdTrunc₁Iso
  
-- -- -- -- --  Π-isInfGpd : ∀ (a : ⟨ A ⟩) n →
-- -- -- -- --    -- fst ((Ω^ n) (_ , a , snd A))
-- -- -- -- --    ℝPaths.UpToℝPath₂ (∙MetricSpace→MetricSpace ((Ω^ n) (_ , a , snd A)))
-- -- -- -- --      ≃ ∥ fst ((Lsp.Ω^ n) (∙Π a)) ∥₂
-- -- -- -- --  Π-isInfGpd a n = isoToEquiv (invIso (IsoUpToℝPath₂⟨A⟩→∥Pieces∥₂ _))
-- -- -- -- --   ∙ₑ isoToEquiv (Π-isInfGpd₂ a n)
--  {- n-fold loop space of a pointed type -}
--  Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
--  (Ω^ 0) p = p
--  (Ω^ (suc n)) p = Ω ((Ω^ n) p)



-- -- 𝐑²MetricSpaceStr : MetricSpaceStr (ℝ × ℝ)
-- -- 𝐑²MetricSpaceStr = {!!}

-- -- distCircleMetricSpaceStr : MetricSpaceStr distCircle 
-- -- distCircleMetricSpaceStr =
-- --  MetricSubSpace (ℝ × ℝ)
-- --   (λ z → (cartNorm² z ≡ 1) , isSetℝ _ _)
-- --   𝐑²MetricSpaceStr

-- -- unwindDistCirclePath :
-- --    (f : IntervalMetricSpace .fst → distCircle)
-- --  → IsUContMap (snd IntervalMetricSpace) f distCircleMetricSpaceStr
-- --  → Σ ((fst IntervalMetricSpace) → ℝ)
-- --    λ g → ∀ x → f x ≡ f (0 , (decℚ≤ᵣ? , decℚ≤ᵣ?)) ℝS¹.+
-- --      Circle→distCircle (injCircle (g x)) 
-- -- unwindDistCirclePath = {!!}


-- -- -- -- -- ℝMetricSpace

-- -- -- -- -- isEquivInjCircleRestr : ∀ c₀ →
-- -- -- -- --   isEquiv {A = Σ distCircle λ (c , _) → cartDist² c₀ c <ᵣ 2}
-- -- -- -- --           {B = Σ _ (_∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ]))}
          
-- -- -- -- --         {!!}
-- -- -- -- -- isEquivInjCircleRestr = {!!}

-- distCircleLocallyIsomorphicToInterval :
--   ∀ (x : distCircle)
--    → Iso (Σ distCircle λ x' → cartDist² (fst x) (fst x') <ᵣ 2)
--          (Σ _ (_∈ ointervalℙ -1 1)) 

-- distCircleLocallyIsomorphicToInterval x =
--   compIso (rotateToOrigin x) {!!}


-- distCircleLocallyFromℝ : ∀ x₀ →
--     Σ ℝ (_∈ ointervalℙ (x₀ -ᵣ rat [ 1 / 2 ]) (x₀ +ᵣ rat [ 1 / 2 ]))
--   → Σ distCircle (λ x → cartDist² (fst x)
--                (fst (Circle→distCircle (injCircle x₀))) <ᵣ 4)
-- distCircleLocallyFromℝ x₀ (x , x∈) .fst = Circle→distCircle (injCircle x)
-- distCircleLocallyFromℝ x₀ (x , x∈) .snd = {!!}


-- distCircleLocallyIsomorphicToInterval :
--   ∀ x₀ → isEquiv
--     {A = Σ ℝ (_∈ ointervalℙ (x₀ -ᵣ rat [ 1 / 2 ]) (x₀ +ᵣ rat [ 1 / 2 ]) )}
--     {B = Σ distCircle λ x → cartDist² (fst x)
--                (fst (Circle→distCircle (injCircle x₀))) <ᵣ 4}
--                (distCircleLocallyFromℝ x₀)

-- distCircleLocallyIsomorphicToInterval = {!!}

-- -- -- -- -- -- -- uContCircleMap : (distCircle → distCircle) → Type
-- -- -- -- -- -- -- uContCircleMap f =
-- -- -- -- -- -- --   IsUContinuousℙ (intervalℙ 0 1)
-- -- -- -- -- -- --     (const ∘ (fst ∘ fst ∘ f ∘ Circle→distCircle ∘ injCircle))
-- -- -- -- -- -- --     ×
-- -- -- -- -- -- --  IsUContinuousℙ (intervalℙ 0 1)
-- -- -- -- -- -- --     (const ∘ (snd ∘ fst ∘ f ∘ Circle→distCircle ∘ injCircle))


-- -- -- -- -- -- -- ℝ-S¹→S¹ : Type 
-- -- -- -- -- -- -- ℝ-S¹→S¹ = Σ[ f ∈ _ ] ∥ uContCircleMap f ∥₁

-- record Piecewise a b (a<b : a <ᵣ b) (p : Partition[ a , b ]) : Type where
--  field
--   fns : ∀ k x → x ∈ intervalℙ (pts' p (finj k)) (pts' p (fsuc k)) → ℝ
--   fnsEnds : ∀ k →
--     fns (finj k) (pts' p (fsuc (finj k))) ({!!} , (≤ᵣ-refl _))
--      ≡ fns (fsuc k) (pts' p (fsuc (finj k)))
--          ((≡ᵣWeaken≤ᵣ _ _ {!!}) , {!!})
--   fnsUC : ∀ k → 
--      IsUContinuousℙ (intervalℙ (pts' p (finj k)) (pts' p (fsuc k)))
--        (fns k)
   
--  piecewise : ∀ x → x ∈ intervalℙ a b → ℝ
--  piecewise = {!!}

--  piecewiseUC : IsUContinuousℙ (intervalℙ a b) piecewise
--  piecewiseUC = {!!}


  
-- -- -- -- -- -- -- const-ℝ-S¹→S¹ : ℝ-S¹→S¹
-- -- -- -- -- -- -- const-ℝ-S¹→S¹ .fst _ = circle0
-- -- -- -- -- -- -- const-ℝ-S¹→S¹ .snd =
-- -- -- -- -- -- --  ∣  IsUContinuousℙ-const (intervalℙ 0 1) _
-- -- -- -- -- -- --   , IsUContinuousℙ-const (intervalℙ 0 1) _ ∣₁




-- -- -- -- -- -- -- -- id-ℝ-S¹→S¹ : ℝ-S¹→S¹
-- -- -- -- -- -- -- -- id-ℝ-S¹→S¹ .fst x = x
-- -- -- -- -- -- -- -- id-ℝ-S¹→S¹ .snd = {!!}
--   ∣ (IsUContinuousℙ∘ℙ (intervalℙ 0 1) (intervalℙ 0 1)
--     {!!} (uContSin (intervalℙ 0 1)) {!!}) , {!!} ∣₁
-- -- (IsUContinuous∘ {!!} {!!}) , {!!}

-- homotopy between maps
-- -- -- -- -- -- -- -- _∼_ : (distCircle → distCircle) → (distCircle → distCircle) → Type
-- -- -- -- -- -- -- -- f ∼ g = ∃ (∀ t → t ∈ intervalℙ 0 1 → ℝ-S¹→S¹)
-- -- -- -- -- -- -- --    λ h → ((fst (h 0 (≤ᵣ-refl 0 , decℚ≤ᵣ? {0} {1})) ≡ f)
-- -- -- -- -- -- -- --        × (fst (h 1 (decℚ≤ᵣ? {0} {1} , ≤ᵣ-refl 1)) ≡ g))
-- -- -- -- -- -- -- --        × ((∀ x → IsUContinuousℙ (intervalℙ 0 1)
-- -- -- -- -- -- -- --            (λ t t∈ → fst (fst (fst (h t t∈) x))))
-- -- -- -- -- -- -- --          × ((∀ x → IsUContinuousℙ (intervalℙ 0 1)
-- -- -- -- -- -- -- --            (λ t t∈ → snd (fst (fst (h t t∈) x))))))


-- -- -- -- -- -- -- -- isEquivRel∼ : BinaryRelation.isEquivRel {A = ℝ-S¹→S¹}
-- -- -- -- -- -- -- --  (λ (x , _) (y , _) → x ∼ y)
-- -- -- -- -- -- -- -- isEquivRel∼ = {!!}

-- -- -- -- -- -- -- -- ℝ-S¹→S¹/∼ : Type
-- -- -- -- -- -- -- -- ℝ-S¹→S¹/∼ = ℝ-S¹→S¹ / λ (x , _) (y , _) → x ∼ y

-- -- -- -- -- -- -- -- eff-ℝ-S¹→S¹/∼ : (a b : ℝ-S¹→S¹) → [ a ]/ ≡ [ b ]/ → a .fst ∼ b .fst
-- -- -- -- -- -- -- -- eff-ℝ-S¹→S¹/∼ = SQ.effective {A = ℝ-S¹→S¹}
-- -- -- -- -- -- -- --   {R = λ (x , _) (y , _) → x ∼ y} (λ _ _ → squash₁) isEquivRel∼

-- -- -- -- -- -- -- -- S¹→S¹· : ℝ-S¹→S¹ → ℝ-S¹→S¹ → ℝ-S¹→S¹
-- -- -- -- -- -- -- -- S¹→S¹· f g = (λ x → fst f x ℝS¹.+ fst g x) ,
-- -- -- -- -- -- -- --              PT.map2 (λ cf cg → {!!}) (snd f) (snd g)



-- -- -- -- -- -- -- -- invS¹→S¹· : ℝ-S¹→S¹ → ℝ-S¹→S¹
-- -- -- -- -- -- -- -- invS¹→S¹· (f , _) .fst = f ∘ circleNeg
-- -- -- -- -- -- -- -- invS¹→S¹· (f , fc) .snd = {!!} --PT.map (λ (xC , yC) → yC , xC) fc



-- -- -- -- -- -- -- -- ℝ-π₁S¹ : AbGroup ℓ-zero
-- -- -- -- -- -- -- -- ℝ-π₁S¹ .fst = ℝ-S¹→S¹/∼
-- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .AbGroupStr.0g = [ const-ℝ-S¹→S¹ ]/
-- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .AbGroupStr._+_ = SQ.Rec2.go w
-- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- --  w : Rec2 (ℝ-π₁S¹ .fst)
-- -- -- -- -- -- -- --  w .Rec2.isSetB = squash/
-- -- -- -- -- -- -- --  w .Rec2.f x y = [ S¹→S¹· x y ]/
-- -- -- -- -- -- -- --  w .Rec2.f∼ = {!!}
-- -- -- -- -- -- -- --  w .Rec2.∼f = {!!}

-- -- -- -- -- -- -- -- AbGroupStr.- ℝ-π₁S¹ .snd = SQ.Rec.go w
-- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- --  w : Rec (ℝ-π₁S¹ .fst)
-- -- -- -- -- -- -- --  w .Rec.isSetB = squash/
-- -- -- -- -- -- -- --  w .Rec.f = [_]/ ∘ invS¹→S¹·
-- -- -- -- -- -- -- --  w .Rec.f∼ a a' = {!!} -- (h , (px , py) , (t0 , t1)) = {!!}
-- -- -- -- -- -- -- --   -- eq/ _ _
-- -- -- -- -- -- -- --   --  ((λ t t∈ → (flipCircle ∘ (fst (h t t∈))) ,
-- -- -- -- -- -- -- --   --    snd (snd (h t t∈)) , fst (snd (h t t∈)))
-- -- -- -- -- -- -- --   --    , ((funExt λ x →
-- -- -- -- -- -- -- --   --      Σ≡Prop (λ _ → isSetℝ _ _)
-- -- -- -- -- -- -- --   --      (cong₂ _,_
-- -- -- -- -- -- -- --   --      (cong (snd ∘ fst) (px ≡$ x))
-- -- -- -- -- -- -- --   --      (cong (fst ∘ fst) (px ≡$ x))))
-- -- -- -- -- -- -- --   --    , (funExt λ x →
-- -- -- -- -- -- -- --   --      Σ≡Prop (λ _ → isSetℝ _ _)
-- -- -- -- -- -- -- --   --      (cong₂ _,_
-- -- -- -- -- -- -- --   --      (cong (snd ∘ fst) (py ≡$ x))
-- -- -- -- -- -- -- --   --      (cong (fst ∘ fst) (py ≡$ x)))))
-- -- -- -- -- -- -- --   --    , {!!})
-- -- -- -- -- -- -- -- ℝ-π₁S¹ .snd .AbGroupStr.isAbGroup =
-- -- -- -- -- -- -- --   makeIsAbGroup {!!} {!!} {!!} {!!} {!!}


-- -- -- -- -- -- -- -- module ℝπ₁S¹ where
-- -- -- -- -- -- -- --  open AbGroupStr (snd ℝ-π₁S¹) public



-- ℤ→ℝ-Circle→Circle : ℤ → Circle → Circle 
-- ℤ→ℝ-Circle→Circle k = SQ.Rec.go w 
--  where
--  w : Rec Circle
--  w .Rec.isSetB = isSetCircle
--  w .Rec.f x = injCircle (rat [ k / 1 ] ·ᵣ x) 
--  w .Rec.f∼ a a' (z , p) = eq/ _ _
--    (k ℤ.· z ,
--     (sym (𝐑'.·DistR- _ _ _)
--      ∙∙ cong (rat [ k / 1 ] ·ᵣ_) p ∙∙
--      sym (rat·ᵣrat _ _)))
 




-- ℤ→ℝ-S¹→S¹/ : ℤ → ℝ-S¹→S¹/∼ 
-- ℤ→ℝ-S¹→S¹/ = _ℤ[ AbGroup→Group ℝ-π₁S¹ ]· [ id-ℝ-S¹→S¹ ]/

-- opaque
--  -- unfolding circle0
--  ℤ→ℝ-S¹→S¹* : ℤ → ℝ-S¹→S¹ 
--  ℤ→ℝ-S¹→S¹* z = (λ x → z ℤ[ AbGroup→Group ℝS¹AbGroup ]· x) , {!!}

--  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* : ∀ z → ℤ→ℝ-S¹→S¹/ z ≡ [ ℤ→ℝ-S¹→S¹* z ]/
--  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (pos zero) =
--    cong [_]/ (Σ≡Prop (λ _ → squash₁)
--     refl)
--  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (pos (suc n)) =
--    cong ([ id-ℝ-S¹→S¹ ]/ ℝπ₁S¹.+_) (ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (pos n))
--     ∙ cong [_]/ (Σ≡Prop (λ _ → squash₁)
--       (funExt λ x → distCircle≡ refl refl))
--  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (ℤ.negsuc zero) =
--   cong [_]/ (Σ≡Prop (λ _ → squash₁) refl)
--  ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (ℤ.negsuc (suc n)) =
--    cong (ℝπ₁S¹.- [ id-ℝ-S¹→S¹  ]/  ℝπ₁S¹.+_) (ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* (ℤ.negsuc n))
--     ∙ cong [_]/ (Σ≡Prop (λ _ → squash₁)
--       (funExt λ x → distCircle≡ refl refl))


-- -- -- opaque
-- -- ℝ-S¹→S¹-winding : ∀ f → uContCircleMap f →
-- --    Σ ℤ.ℤ λ k →
-- --       Σ (fromInterval→ℝ-uC) λ (g , _) → 
-- --       ((rat [ k / 1 ] ≡ g 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) -ᵣ g 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- --        × (((∀ x x∈ →  Circle→distCircle (injCircle (g x x∈)) ≡
-- --              f (Circle→distCircle (injCircle x))))
-- --              × (fst (ℤ→ℝ-S¹→S¹* k) ∼ f))) 
-- -- ℝ-S¹→S¹-winding f  (ucX , ucY) =
-- --   (fst pcwΔ) ,
-- --    ((fst pcwN , fst (snd pcwN)) ,
-- --     ((snd pcwΔ) , snd (snd pcwN) , ∼f))

-- --   where
-- --   ε : ℚ₊
-- --   ε = 1

-- --   uc-x : Σ ℚ₊ λ δ →
-- --                  (u v : ℝ) (u∈ : u ∈ intervalℙ 0 1) (v∈ : v ∈ intervalℙ 0 1) →
-- --                  u ∼[ δ ] v →
-- --                  fst (fst (f (Circle→distCircle (injCircle u)))) ∼[ ε ]
-- --                  fst (fst (f (Circle→distCircle (injCircle v))))
-- --   uc-x = ucX ε

-- --   uc-y : Σ ℚ₊ λ δ →
-- --                  (u v : ℝ) (u∈ : u ∈ intervalℙ 0 1) (v∈ : v ∈ intervalℙ 0 1) →
-- --                  u ∼[ δ ] v →
-- --                  snd (fst (f (Circle→distCircle (injCircle u)))) ∼[ ε ]
-- --                  snd (fst (f (Circle→distCircle (injCircle v))))
-- --   uc-y = ucY ε

-- --   δ : ℚ₊
-- --   δ = ℚ.min₊ 1 (ℚ.min₊ (fst uc-x) (fst uc-y))

-- --   n,n< : Σ (ℕ × ℚ)
-- --           (λ (n , q) →
-- --              (fromNat n ℚ.+ q ≡ fst (invℚ₊ δ)) × (0 ℚ.≤ q) × (q ℚ.< 1))
-- --   n,n< = ℚ.floor-fracℚ₊ (invℚ₊ δ)

-- --   n : ℕ
-- --   n = fst (fst n,n<)


-- --   pcw : ∀ k → k ℕ.≤ n →
-- --            Σ[ g ∈ (∀ x → x ∈ intervalℙ 0 (rat [ pos (suc k) / 1+ n ]) → ℝ) ]
-- --               (IsUContinuousℙ (intervalℙ 0 (rat [ pos (suc k) / 1+ n ])) g
-- --                  × (∀ x x∈ → Circle→distCircle (injCircle (g x x∈)) ≡
-- --                       f (Circle→distCircle (injCircle x))))
-- --   pcw zero x = {!!}
-- --   pcw (suc k) x = {!!}

-- --   pcwN : Σ[ g ∈ (∀ x → x ∈ intervalℙ 0 1 → ℝ) ]
-- --             ((IsUContinuousℙ (intervalℙ 0 1) g) × 
-- --               (∀ x x∈ → Circle→distCircle (injCircle (g x x∈)) ≡
-- --                       f (Circle→distCircle (injCircle x))))
-- --   pcwN = subst (λ u → Σ[ g ∈ (∀ x → x ∈ intervalℙ 0 u → ℝ) ]
-- --               (IsUContinuousℙ (intervalℙ 0 u) g
-- --                  × (∀ x x∈ → Circle→distCircle (injCircle (g x x∈)) ≡
-- --                       f (Circle→distCircle (injCircle x)))))
-- --                        (cong rat (ℚ.[/]≡· (pos (suc n)) (1+ n)
-- --                         ∙ ℚ.x·invℚ₊[x] ([ pos (suc n) / 1 ] , _)))
-- --                         (pcw n (ℕ.≤-refl {n}))

-- -- -- f (Circle→distCircle (injCircle (fst fwi x x∈)))
-- -- --              ≡ fst fwi x x∈

-- --   pcwΔ : Σ[ k ∈ ℤ ] (rat [ k / 1 ] ≡
-- --           fst pcwN 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) -ᵣ fst pcwN 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- --   pcwΔ =
-- --    let p : Circle→distCircle (injCircle (pcwN .fst 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))) ≡
-- --             Circle→distCircle (injCircle (pcwN .fst 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- --        p = (snd (snd pcwN) 0 (decℚ≤ᵣ? , decℚ≤ᵣ? ))
-- --             ∙∙ cong (f ∘ Circle→distCircle)
-- --                (eq/ _ _ (-1 , -ᵣ-rat₂ 0 1)) ∙∙
-- --             sym (snd (snd pcwN) 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- --        p' = invEq (congEquiv
-- --               {x = injCircle (pcwN .fst 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))}
-- --               {y = injCircle (pcwN .fst 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))}
-- --                Circle≃distCircle) p  
-- --        z = fromCircle≡ _ _ (sym p')
-- --    in fst z , sym (snd z)

-- --   -- 𝒈 : CircleOverlap[ ℚ₊→ℝ₊ ([ 1 / 2 ] , _) ] → distCircle
-- --   -- 𝒈 = SQ.Rec.go
-- --   --    {A = Σ-syntax ℝ
-- --   --          (λ x → x ∈ ointervalℙ 0 (1 +ᵣ fst (ℚ₊→ℝ₊ ([ 1 / 2 ] , tt))))}
-- --   --    {R = circle-rel-overlap (ℚ₊→ℝ₊ ([ 1 / 2 ] , tt))}
-- --   --    ww
-- --   --  where

-- --   --  -- www : (x : ℝ) → distCircle
-- --   --  -- www = stichFns' distCircle isSetDistCircle
-- --   --  --   (rat [ 1 / 2 ]) 1
-- --   --  --    decℚ<ᵣ?
-- --   --  --      (λ x x<1 → Circle→distCircle (injCircle (fst pcwN (maxᵣ 0 x)
-- --   --  --        ((≤maxᵣ 0 x) , max≤-lem 0 x 1 decℚ≤ᵣ? (<ᵣWeaken≤ᵣ _ _ x<1)))))
-- --   --  --      (λ x 1/2<x → {!!})
-- --   --  --      {!!}

-- --   --  ww : Rec
-- --   --    {A = Σ-syntax ℝ
-- --   --          (λ x → x ∈ ointervalℙ 0 (1 +ᵣ fst (ℚ₊→ℝ₊ ([ 1 / 2 ] , tt))))}
-- --   --    {R = circle-rel-overlap (ℚ₊→ℝ₊ ([ 1 / 2 ] , tt))}
-- --   --    distCircle
-- --   --  ww .Rec.isSetB = isSetDistCircle
-- --   --  ww .Rec.f (x , x∈) = {!!}
-- --   --  ww .Rec.f∼ = {!!}

-- --   𝒉 : (t : ℝ) → t ∈ intervalℙ 0 1 → ℝ-S¹→S¹
-- --   𝒉 t t∈ = Circle→distCircle ∘ injCircle ∘ fst zz ,
-- --     {!!}
-- --     where
-- --     zz : {!!}
-- --     zz = fromFWI ({!!} , {!!}) {!!}
-- --  -- fromFWI
-- --   ∼f : fst (ℤ→ℝ-S¹→S¹* (fst pcwΔ)) ∼ f
-- --   ∼f = ∣ (𝒉 , {!!}) ∣₁

-- -- -- ℤ-ℝ-S¹→S¹-Hom : GroupHom ℤGroup (AbGroup→Group ℝ-π₁S¹)
-- -- -- ℤ-ℝ-S¹→S¹-Hom .fst = ℤ→ℝ-S¹→S¹/
-- -- -- ℤ-ℝ-S¹→S¹-Hom .snd = makeIsGroupHom 
-- -- --   (distrℤ· (AbGroup→Group ℝ-π₁S¹) [ id-ℝ-S¹→S¹ ]/)
  

-- -- -- ℤ-ℝ-S¹→S¹-inj : ∀ k → ℤ→ℝ-S¹→S¹/ k ≡ [ const-ℝ-S¹→S¹ ]/ → k ≡ 0
-- -- -- ℤ-ℝ-S¹→S¹-inj k p = 
-- -- --   let w = eff-ℝ-S¹→S¹/∼ _ _
-- -- --              (sym (ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* k) ∙ p)
-- -- --   in PT.rec
-- -- --        (ℤ.isSetℤ _ _)
-- -- --        (λ (h , (h0 , h1) , _) →
-- -- --          {!!}) w

-- -- -- ℤ-ℝ-S¹→S¹-BijectionIso : BijectionIso ℤGroup (AbGroup→Group ℝ-π₁S¹)
-- -- -- ℤ-ℝ-S¹→S¹-BijectionIso .BijectionIso.fun = ℤ-ℝ-S¹→S¹-Hom
-- -- -- ℤ-ℝ-S¹→S¹-BijectionIso .BijectionIso.inj = ℤ-ℝ-S¹→S¹-inj
-- -- -- ℤ-ℝ-S¹→S¹-BijectionIso .BijectionIso.surj = SQ.ElimProp.go w
-- -- --  where

-- -- --  w : ElimProp (isInIm ℤ-ℝ-S¹→S¹-Hom)
-- -- --  w .ElimProp.isPropB _ = squash₁
-- -- --  w .ElimProp.f (f , fc) =
-- -- --   PT.map
-- -- --     (map-snd (λ {z} w →
-- -- --        ℤ→ℝ-S¹→S¹/≡ℤ→ℝ-S¹→S¹* z ∙
-- -- --            (eq/ (ℤ→ℝ-S¹→S¹* z) (f , fc) (snd (snd (snd w)))))
-- -- --       ∘ ℝ-S¹→S¹-winding f) fc

-- -- -- -- ℝ-π₁S¹ : Group ℓ-zero
-- -- -- -- ℝ-π₁S¹ .fst = ℝ-S¹→S¹/∼
-- -- -- -- ℝ-π₁S¹ .snd .GroupStr.1g = [ const-ℝ-S¹→S¹ ]/
-- -- -- -- ℝ-π₁S¹ .snd .GroupStr._·_ = SQ.Rec2.go w
-- -- -- --  where
-- -- -- --  w : Rec2 (ℝ-π₁S¹ .fst)
-- -- -- --  w .Rec2.isSetB = squash/
-- -- -- --  w .Rec2.f x y = [ S¹→S¹· x y ]/
-- -- -- --  w .Rec2.f∼ = {!!}
-- -- -- --  w .Rec2.∼f = {!!}
 
-- -- -- -- ℝ-π₁S¹ .snd .GroupStr.inv = SQ.Rec.go w
-- -- -- --  where
-- -- -- --  w : Rec (ℝ-π₁S¹ .fst)
-- -- -- --  w .Rec.isSetB = squash/
-- -- -- --  w .Rec.f = [_]/ ∘ invS¹→S¹·
-- -- -- --  w .Rec.f∼ a a' (h , (px , py) , (t0 , t1)) = eq/ _ _
-- -- -- --    ((λ t t∈ → (flipCircle ∘ (fst (h t t∈))) ,
-- -- -- --      snd (snd (h t t∈)) , fst (snd (h t t∈)))
-- -- -- --      , ((funExt λ x →
-- -- -- --        Σ≡Prop (λ _ → isSetℝ _ _)
-- -- -- --        (cong₂ _,_
-- -- -- --        (cong (snd ∘ fst) (px ≡$ x))
-- -- -- --        (cong (fst ∘ fst) (px ≡$ x))))
-- -- -- --      , (funExt λ x →
-- -- -- --        Σ≡Prop (λ _ → isSetℝ _ _)
-- -- -- --        (cong₂ _,_
-- -- -- --        (cong (snd ∘ fst) (py ≡$ x))
-- -- -- --        (cong (fst ∘ fst) (py ≡$ x)))))
-- -- -- --      , {!!})
-- -- -- -- ℝ-π₁S¹ .snd .GroupStr.isGroup =
-- -- -- --   makeIsGroup squash/
-- -- -- --    {!!} {!!} {!!} {!!} {!!}


-- -- -- -- -- -- -- concatProp : fromWeldedInterval ℝ →
-- -- -- -- -- -- --    fromWeldedInterval ℝ → fromWeldedInterval ℝ  
-- -- -- -- -- -- -- concatProp = {!!}


-- module _ (ε : ℝ₊) where
--  circle-rel-overlap : 
--    (x y : (Σ[ x ∈ ℝ ] x ∈ ointervalℙ 0 (1 +ᵣ fst ε))) → Type
--  circle-rel-overlap (x , _) (y , _) = circle-rel x y

--  CircleOverlap[_] : Type
--  CircleOverlap[_] =
--   (Σ[ x ∈ ℝ ] x ∈ ointervalℙ 0 (1 +ᵣ fst ε))
--    / circle-rel-overlap


--  CircleOverlap[_]→Circle : CircleOverlap[_] → Circle
--  CircleOverlap[_]→Circle = SQ.Rec.go w
--   where
--   w : Rec _
--   w .Rec.isSetB = isSetCircle
--   w .Rec.f (a , _) = [ a ]/
--   w .Rec.f∼ _ _ = eq/ _ _



