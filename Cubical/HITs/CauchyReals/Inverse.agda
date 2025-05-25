{-# OPTIONS --lossy-unification --safe #-}

module Cubical.HITs.CauchyReals.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne


import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.Ring as RP


open import Cubical.Relation.Binary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication


Rℝ = (CR.CommRing→Ring
               (_ , CR.commringstr 0 1 _+ᵣ_ _·ᵣ_ -ᵣ_ IsCommRingℝ))
-- module CRℝ = ?

module 𝐑 = CR.CommRingTheory (_ , CR.commringstr 0 1 _+ᵣ_ _·ᵣ_ -ᵣ_ IsCommRingℝ)
module 𝐑' = RP.RingTheory Rℝ

module 𝐐' = RP.RingTheory (CR.CommRing→Ring ℚCommRing)

module L𝐑 = Lems ((_ , CR.commringstr 0 1 _+ᵣ_ _·ᵣ_ -ᵣ_ IsCommRingℝ))


Invᵣ-restrℚ : (η : ℚ₊) →
  Σ (ℚ → ℚ) (Lipschitz-ℚ→ℚ (invℚ₊ (η ℚ₊· η)))

Invᵣ-restrℚ η = f ,
  Lipschitz-ℚ→ℚ'→Lipschitz-ℚ→ℚ _ _ w
 where

 f = fst ∘ invℚ₊ ∘ ℚ.maxWithPos η

 w : ∀ q r → ℚ.abs (f q ℚ.- f r) ℚ.≤
      fst (invℚ₊ (η ℚ₊· η)) ℚ.· ℚ.abs (q ℚ.- r)
 w q r =
  let z = cong ℚ.abs (ℚ.1/p+1/q (ℚ.maxWithPos η q) (ℚ.maxWithPos η r))
           ∙ ℚ.pos·abs _ _ (ℚ.0≤ℚ₊ (invℚ₊ (ℚ.maxWithPos η q ℚ₊· ℚ.maxWithPos η r)))
           ∙ cong (fst (invℚ₊ (ℚ.maxWithPos η q ℚ₊· ℚ.maxWithPos η r)) ℚ.·_)
       ((ℚ.absComm- _ _))
  in subst (ℚ._≤ fst (invℚ₊ (η ℚ₊· η)) ℚ.· ℚ.abs (q ℚ.- r))
       (sym z)
         (ℚ.≤Monotone·-onNonNeg
           (fst (invℚ₊ (ℚ.maxWithPos η q ℚ₊· ℚ.maxWithPos η r))) _ _ _
            (ℚ.invℚ₊≤invℚ₊ _ _
              (ℚ.≤Monotone·-onNonNeg _ _ _ _
                (ℚ.≤max _ _)
                (ℚ.≤max _ _)
                (ℚ.0≤ℚ₊ η)
                (ℚ.0≤ℚ₊ η)))
            (ℚ.maxDist (fst η) r q)
            (ℚ.0≤ℚ₊ (invℚ₊ (ℚ.maxWithPos η q ℚ₊· ℚ.maxWithPos η r)))
            (ℚ.0≤abs (fst (ℚ.maxWithPos η q) ℚ.- fst (ℚ.maxWithPos η r))))

Invᵣ-restr : (η : ℚ₊) → Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (invℚ₊ (η ℚ₊· η)))
Invᵣ-restr η = (fromLipschitz (invℚ₊ (η ℚ₊· η)))
                   (_ , Lipschitz-rat∘ _ _ (snd (Invᵣ-restrℚ η)))


lowerℚBound : ∀ u → 0 <ᵣ u → ∃[ ε ∈ ℚ₊ ] (rat (fst ε) <ᵣ u)
lowerℚBound u x =
  PT.map (λ (ε , (x' , x'')) → (ε , ℚ.<→0< _ (<ᵣ→<ℚ _ _ x')) , x'')
    (denseℚinℝ 0 u x)

≤absᵣ : ∀ x → x ≤ᵣ absᵣ x
≤absᵣ = ≡Continuous
  (λ x → maxᵣ x (absᵣ x))
  (λ x → absᵣ x)
  (cont₂maxᵣ _ _ IsContinuousId IsContinuousAbsᵣ)
  IsContinuousAbsᵣ
  λ x →  cong (maxᵣ (rat x) ∘ rat) (sym (ℚ.abs'≡abs x))
     ∙∙ cong rat (ℚ.≤→max _ _ (ℚ.≤abs x)) ∙∙
     cong rat (ℚ.abs'≡abs x )

from-abs< : ∀ x y z → absᵣ (x +ᵣ (-ᵣ y)) <ᵣ z
       → (x +ᵣ (-ᵣ y) <ᵣ z)
          × ((y +ᵣ (-ᵣ x) <ᵣ z))
            × ((-ᵣ y) +ᵣ x <ᵣ z)
from-abs< x y z p = isTrans≤<ᵣ _ _ _ (≤absᵣ _) p ,
 isTrans≤<ᵣ _ _ _ (≤absᵣ _) (subst (_<ᵣ z) (minusComm-absᵣ x y) p)
   , isTrans≤<ᵣ _ _ _ (≤absᵣ _) (subst (((_<ᵣ z) ∘ absᵣ)) (+ᵣComm x (-ᵣ y)) p)

open ℚ.HLP

∃rationalApprox≤ : ∀ u → (ε : ℚ₊) →
   ∃[ q ∈ ℚ ] (((rat q) +ᵣ (-ᵣ u)) ≤ᵣ rat (fst ε)) × (u ≤ᵣ rat q)
∃rationalApprox≤ = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop _
 w .Elimℝ-Prop.ratA r ε =
  ∣  r ℚ.+ fst (/2₊ ε) ,
   ≤ℚ→≤ᵣ _ _ (
     let zzz : r ℚ.+ (fst (/2₊ ε) ℚ.+ (ℚ.- r)) ≡ fst (/2₊ ε)
         zzz = (lem--05 {r} {fst (/2₊ ε)})
         zz = (subst (ℚ._≤ fst ε) (sym (sym (ℚ.+Assoc _ _ _) ∙ zzz))
            (ℚ.<Weaken≤ _ _ (ℚ.x/2<x (ε))) )
     in zz)
       , ≤ℚ→≤ᵣ _ _ (ℚ.≤+ℚ₊ r r (/2₊ ε) (ℚ.isRefl≤ r)) ∣₁
 w .Elimℝ-Prop.limA x y R ε =
   let z = 𝕣-lim-dist x y (/4₊ ε)
   in PT.map (λ (q , z , z') →
        let (_ , Xzz' , Xzz) = from-abs< _ _ _
                     (𝕣-lim-dist x y (/4₊ ε))

            zz :  (-ᵣ (lim x y)) +ᵣ x (/2₊ (/4₊ ε))   ≤ᵣ rat (fst (/4₊ ε))
            zz = <ᵣWeaken≤ᵣ _ _ Xzz
            zz' :  (lim x y) +ᵣ (-ᵣ (x (/2₊ (/4₊ ε))))   ≤ᵣ rat (fst (/4₊ ε))
            zz' = <ᵣWeaken≤ᵣ _ _ Xzz'
        in q ℚ.+ fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε))  ,
              let zzz = (≤ᵣ-+o _ _ (rat (fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε))))
                      (≤ᵣMonotone+ᵣ _ _ _ _ z zz))
              in subst2 _≤ᵣ_
                  (cong (_+ᵣ (rat (fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε)))))
                    (L𝐑.lem--059 {rat q}
                        {x (/2₊ (/4₊ ε))}
                        { -ᵣ lim x y} ∙ +ᵣComm (rat q) (-ᵣ lim x y))
                      ∙ sym (+ᵣAssoc (-ᵣ lim x y) (rat q)
                     (rat (fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε))))) ∙
                       +ᵣComm (-ᵣ lim x y)
                        (rat q +ᵣ rat (fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε))))
                         ∙ cong (_+ᵣ (-ᵣ lim x y))
                           (+ᵣAssoc (rat q) (rat (fst (/2₊ ε)))
                            (rat (fst (/2₊ (/4₊ ε))))))
                  (cong rat
                   (distℚ! (fst ε) ·[
                        ((ge[ ℚ.[ 1 / 4 ] ]
                               ·ge ge[ ℚ.[ 1 / 2 ] ])
                            +ge  ge[ ℚ.[ 1 / 4 ] ]
                            )
                                +ge
                          (ge[ ℚ.[ 1 / 2 ] ]
                            +ge (ge[ ℚ.[ 1 / 4 ] ]
                               ·ge ge[ ℚ.[ 1 / 2 ] ]))
                      ≡ ge1 ]))
                  zzz
                ,
                 isTrans≤ᵣ _ _ _ (subst (_≤ᵣ (rat q +ᵣ rat (fst (/4₊ ε))))
                   L𝐑.lem--05 (≤ᵣMonotone+ᵣ _ _ _ _ z' zz'))
                    (≤ℚ→≤ᵣ _ _
                      (subst (q ℚ.+ fst (/4₊ ε) ℚ.≤_)
                        (ℚ.+Assoc _ _ _)
                         (ℚ.≤-o+ _ _ q distℚ≤!
                          ε [ ge[ ℚ.[ 1 / 4 ] ] ≤
                          ge[ ℚ.[ 1 / 2 ] ]
                            +ge (ge[ ℚ.[ 1 / 4 ] ]
                               ·ge ge[ ℚ.[ 1 / 2 ] ]) ]) )))
        (R (/2₊ (/4₊ ε)) (/2₊ (/4₊ ε)))
 w .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → squash₁


ℚmax-min-minus : ∀ x y → ℚ.max (ℚ.- x) (ℚ.- y) ≡ ℚ.- (ℚ.min x y)
ℚmax-min-minus = ℚ.elimBy≤
 (λ x y p → ℚ.maxComm _ _ ∙∙ p ∙∙ cong ℚ.-_ (ℚ.minComm _ _))
  λ x y x≤y →
    ℚ.maxComm _ _ ∙∙ ℚ.≤→max (ℚ.- y) (ℚ.- x) (ℚ.minus-≤ x y x≤y)
      ∙∙ cong ℚ.-_ (sym (ℚ.≤→min _ _ x≤y))


-ᵣ≤ᵣ : ∀ x y → x ≤ᵣ y → -ᵣ y ≤ᵣ -ᵣ x
-ᵣ≤ᵣ x y p = subst2 _≤ᵣ_
    (cong (x +ᵣ_) (+ᵣComm _ _) ∙
      L𝐑.lem--05 {x} { -ᵣ y}) (L𝐑.lem--05 {y} { -ᵣ x}) (≤ᵣ-+o _ _ ((-ᵣ x) +ᵣ (-ᵣ y)) p)


-ᵣ<ᵣ : ∀ x y → x <ᵣ y → -ᵣ y <ᵣ -ᵣ x
-ᵣ<ᵣ x y = PT.map
  λ ((q , q') , z , z' , z'') →
       (ℚ.- q' , ℚ.- q) , -ᵣ≤ᵣ _ _ z'' , ((ℚ.minus-< _ _ z') , -ᵣ≤ᵣ _ _ z)

∃rationalApprox< : ∀ u → (ε : ℚ₊) →
   ∃[ q ∈ ℚ ] (((rat q) +ᵣ (-ᵣ u)) <ᵣ rat (fst ε)) × (u <ᵣ rat q)
∃rationalApprox< u ε =
  PT.map (uncurry (λ q (x , x') →
     q ℚ.+ (fst (/4₊ ε))  ,
          subst (_<ᵣ (rat (fst ε)))
            (L𝐑.lem--014 {rat q} {u} {rat (fst (/4₊ ε))})  (
             isTrans≤<ᵣ _ _ (rat (fst ε)) (≤ᵣ-+o _ _ (rat (fst (/4₊ ε))) x)
             (<ℚ→<ᵣ _ _ $
               distℚ<! ε [ ge[ ℚ.[ 1 / 2 ] ]
                 +ge ge[ ℚ.[ 1 / 4 ] ] < ge1 ])) ,
              isTrans≤<ᵣ _ _ _ x'
                (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ (/4₊ ε) (ℚ.isRefl≤ _) )) ))
            $ ∃rationalApprox≤ u (/2₊ ε)


-- TODO: this is overcomplciated! it follows simply form density...

∃rationalApprox : ∀ u → (ε : ℚ₊) →
   ∃[ (q , q') ∈ (ℚ × ℚ) ] (q' ℚ.- q ℚ.< fst ε) ×
                           ((rat q <ᵣ u) × (u <ᵣ rat q'))
∃rationalApprox u ε =
  PT.map2 (uncurry (λ q (x , x') → uncurry (λ q' (y , y') →
      ((ℚ.- (q ℚ.+ (fst (/4₊ ε)))) , q' ℚ.+ (fst (/4₊ ε))) ,
            let zz = ℚ.≤-+o _ _ (fst (/4₊ ε) ℚ.+ fst (/4₊ ε))
                      (≤ᵣ→≤ℚ _ _ (subst (_≤ᵣ
                       (rat (fst (/2₊ (/4₊ ε)))
                      +ᵣ rat (fst (/2₊ (/4₊ ε)))))
                       (L𝐑.lem--059 {rat q} { -ᵣ u} {rat q'} )
                      (≤ᵣMonotone+ᵣ _ _ _ _ x y)))
                zzz : (fst (/2₊ (/4₊ ε)) ℚ.+ fst (/2₊ (/4₊ ε)))
                    ℚ.+ (fst (/4₊ ε) ℚ.+ fst (/4₊ ε)) ℚ.< fst ε
                zzz = distℚ<! ε [
                             (ge[ ℚ.[ 1 / 4 ] ]
                                ·ge ge[ ℚ.[ 1 / 2 ] ]
                              +ge ge[ ℚ.[ 1 / 4 ] ]
                                ·ge ge[ ℚ.[ 1 / 2 ] ] )
                            +ge (ge[ ℚ.[ 1 / 4 ] ]
                              +ge ge[ ℚ.[ 1 / 4 ] ]) < ge1 ]
            in ℚ.isTrans≤< _ _ _
                   (subst (ℚ._≤ _)
                    (cong (ℚ._+ ((fst (/4₊ ε) ℚ.+ fst (/4₊ ε))))
                      (ℚ.+Comm q q')
                     ∙∙ 𝐐'.+ShufflePairs _ _ _ _
                     ∙∙ cong (_ ℚ.+_) (sym (ℚ.-Invol _)))
                    zz)
                    zzz
                 ,
            (subst (rat (ℚ.- (q ℚ.+ fst (/4₊ ε))) <ᵣ_) (-ᵣInvol u)
               (-ᵣ<ᵣ _ _ $ isTrans≤<ᵣ _ _ _ x'
                (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ (/4₊ ε) (ℚ.isRefl≤ _) )))
                 , isTrans≤<ᵣ _ _ _ y'
                (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ (/4₊ ε) (ℚ.isRefl≤ _) )))
     )
     )) (∃rationalApprox≤ (-ᵣ u) (/2₊ (/4₊ ε)))
        (∃rationalApprox≤ u (/2₊ (/4₊ ε)))



<ᵣ-+o-pre : ∀ m n o  → m ℚ.< n  → (rat m +ᵣ o) <ᵣ (rat n +ᵣ o)
<ᵣ-+o-pre m n o m<n =
  PT.rec2 squash₁ (λ (q , x , x') ((q' , q'') , y , y' , y'') →
     let x* : (rat q) ≤ᵣ rat (fst (/4₊ Δ)) +ᵣ ((rat m +ᵣ o))
         x* =  subst (_≤ᵣ rat (fst (/4₊ Δ)) +ᵣ ((rat m +ᵣ o)))
                (L𝐑.lem--00)
                 (≤ᵣ-+o _ _
                  ((rat m +ᵣ o)) (<ᵣWeaken≤ᵣ _ _ x))

         y* : (rat (fst (/4₊ Δ)) +ᵣ (rat m +ᵣ o)) ≤ᵣ
               (-ᵣ (rat (fst (/4₊ Δ)) +ᵣ (-ᵣ (rat n +ᵣ o))))
         y* = subst2 {x = rat (fst (/2₊ Δ))
                 +ᵣ (rat m +ᵣ (o +ᵣ (-ᵣ (rat (fst (/4₊ Δ))))))}
                _≤ᵣ_ -- (rat m +ᵣ (o +ᵣ (-ᵣ rat (fst (/4₊ Δ)))))
              ((λ i → +ᵣComm (rat (fst (/2₊ Δ)))
                   (+ᵣAssoc (rat m) o (-ᵣ rat (fst (/4₊ Δ))) i) i)
                    ∙ sym (+ᵣAssoc _ _ _) ∙
                      cong ((rat m +ᵣ o) +ᵣ_)
                        (cong rat (distℚ! (fst Δ)
                          ·[ ((neg-ge ge[ ℚ.[ 1 / 4 ] ])
                           +ge ge[ ℚ.[ 1 / 2 ] ])
                          ≡ ge[ ℚ.[ 1 / 4 ] ] ]))
                        ∙ +ᵣComm _ _ )
              (+ᵣAssoc _ _ _ ∙
                cong (_+ᵣ (o +ᵣ (-ᵣ rat (fst (/4₊ Δ)))))
                   (L𝐑.lem--00 {rat n} {rat m}) ∙
                    +ᵣAssoc _ _ _ ∙
                     (λ i → +ᵣComm (-ᵣInvol (rat n +ᵣ o) (~ i))
                       (-ᵣ rat (fst (/4₊ Δ))) i) ∙
                      sym (-ᵣDistr (rat (fst (/4₊ Δ))) ((-ᵣ (rat n +ᵣ o)))) )
              (≤ᵣ-+o _ _ (rat m +ᵣ (o +ᵣ (-ᵣ (rat (fst (/4₊ Δ))))))
                (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (x/2<x Δ))))

         z* : -ᵣ (rat (fst (/4₊ Δ)) +ᵣ (-ᵣ (rat n +ᵣ o)))
               ≤ᵣ ((rat q'))
         z* = subst ((-ᵣ (rat (fst (/4₊ Δ)) +ᵣ (-ᵣ (rat n +ᵣ o)))) ≤ᵣ_)
               (cong (-ᵣ_) (sym (+ᵣAssoc (rat q'') (-ᵣ rat q') _)
                   ∙ L𝐑.lem--05 {rat q''} {(-ᵣ rat q')}) ∙
                     -ᵣInvol (rat q'))

                    (-ᵣ≤ᵣ _ _ (≤ᵣMonotone+ᵣ _ _ _ _
                (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ y))
                 (<ᵣWeaken≤ᵣ _ _ (-ᵣ<ᵣ _ _ y''))))
         z : rat q ≤ᵣ rat q'
         z = isTrans≤ᵣ _ _ _
              (isTrans≤ᵣ _ _ _
                  x* y* ) z*
     in isTrans<ᵣ _ _ _ x'
        (isTrans≤<ᵣ _ _ _ z y'))
    (∃rationalApprox< (rat m +ᵣ o) (/4₊ Δ))
     ((∃rationalApprox (rat n +ᵣ o) (/4₊ Δ)))

 where
 Δ = ℚ.<→ℚ₊ m n m<n

<ᵣ-+o : ∀ m n o →  m <ᵣ n → (m +ᵣ o) <ᵣ (n +ᵣ o)
<ᵣ-+o m n o = PT.rec squash₁
  λ ((q , q') , x , x' , x'') →
   let y : (m +ᵣ o) ≤ᵣ (rat q +ᵣ o)
       y = ≤ᵣ-+o m (rat q) o x
       y'' : (rat q' +ᵣ o) ≤ᵣ (n +ᵣ o)
       y'' = ≤ᵣ-+o (rat q') n o x''

       y' : (rat q +ᵣ o) <ᵣ (rat q' +ᵣ o)
       y' = <ᵣ-+o-pre q q' o x'


   in isTrans<≤ᵣ _ _ _ (isTrans≤<ᵣ _ _ _ y y') y''

<ᵣ-o+ : ∀ m n o →  m <ᵣ n → (o +ᵣ m) <ᵣ (o +ᵣ n)
<ᵣ-o+ m n o = subst2 _<ᵣ_ (+ᵣComm m o) (+ᵣComm n o) ∘ <ᵣ-+o m n o

<ᵣMonotone+ᵣ : ∀ m n o s → m <ᵣ n → o <ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
<ᵣMonotone+ᵣ m n o s m<n o<s =
  isTrans<ᵣ _ _ _ (<ᵣ-+o m n o m<n) (<ᵣ-o+ o s n o<s)

≤<ᵣMonotone+ᵣ : ∀ m n o s → m ≤ᵣ n → o <ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
≤<ᵣMonotone+ᵣ m n o s m≤n o<s =
  isTrans≤<ᵣ _ _ _ (≤ᵣ-+o m n o m≤n) (<ᵣ-o+ o s n o<s)

<≤ᵣMonotone+ᵣ : ∀ m n o s → m <ᵣ n → o ≤ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
<≤ᵣMonotone+ᵣ m n o s m<n o≤s =
  isTrans<≤ᵣ _ _ _ (<ᵣ-+o m n o m<n) (≤ᵣ-o+ o s n o≤s)



ℝ₊+ : (m : ℝ₊) (n : ℝ₊) → 0 <ᵣ (fst m) +ᵣ (fst n)
ℝ₊+ (m , <m) (n , <n) = <ᵣMonotone+ᵣ 0 m 0 n <m <n



isAsym<ᵣ : BinaryRelation.isAsym _<ᵣ_
isAsym<ᵣ x y =
  PT.rec2 (isProp⊥)
   λ ((q , q') , x , x' , x'')
      ((r , r') , y , y' , y'') →
       let q<r = ℚ.isTrans<≤ _ _ _ x' (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _ x'' y))
           r<q = ℚ.isTrans<≤ _ _ _ y' (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _ y'' x))
       in ℚ.isAsym< _ _ q<r r<q


_＃_ : ℝ → ℝ → Type
x ＃ y = (x <ᵣ y) ⊎ (y <ᵣ x)

isProp＃ : ∀ x y → isProp (x ＃ y)
isProp＃ x y (inl x₁) (inl x₂) = cong inl (squash₁ x₁ x₂)
isProp＃ x y (inl x₁) (inr x₂) = ⊥.rec (isAsym<ᵣ _ _ x₁ x₂)
isProp＃ x y (inr x₁) (inl x₂) = ⊥.rec (isAsym<ᵣ _ _ x₁ x₂)
isProp＃ x y (inr x₁) (inr x₂) = cong inr (squash₁ x₁ x₂)


rat＃ : ∀ q q' → (rat q ＃ rat q') ≃ (q ℚ.# q' )
rat＃ q q' = propBiimpl→Equiv (isProp＃ _ _) (ℚ.isProp# _ _)
  (⊎.map (<ᵣ→<ℚ _ _) (<ᵣ→<ℚ _ _))
  (⊎.map (<ℚ→<ᵣ _ _) (<ℚ→<ᵣ _ _))


decCut : ∀ x → 0 <ᵣ (absᵣ x) → (0 ＃ x)
decCut x 0<absX =
  PT.rec (isProp＃ 0 x)
    (λ (Δ , Δ<absX) →
      PT.rec (isProp＃ 0 x)
         (λ (q , q-x<Δ/2 , x<q) →
          let z→ : 0 ℚ.< q → 0 <ᵣ x
              z→ 0<q =
                let zzz : rat q <ᵣ rat (fst (/2₊ Δ)) →
                            0 <ᵣ x
                    zzz q<Δ/2 =
                      let zzz' =
                           subst2 _≤ᵣ_
                             (cong absᵣ (L𝐑.lem--05 {rat q} {x}))
                               (cong₂ _+ᵣ_
                                 (absᵣNonNeg _
                                      (≤ℚ→≤ᵣ _ _
                                         (ℚ.<Weaken≤ 0 q 0<q )))
                                  (minusComm-absᵣ _ _ ∙
                                       absᵣNonNeg _
                                         (subst (_≤ᵣ (rat q +ᵣ (-ᵣ x)))
                                           (+-ᵣ x) (≤ᵣ-+o _ _ (-ᵣ x)
                                          (<ᵣWeaken≤ᵣ _ _ x<q)))))
                              (absᵣ-triangle (rat q) (x +ᵣ (-ᵣ (rat q))))
                          zzzz' = subst (absᵣ x <ᵣ_) (cong rat
                               (ℚ.ε/2+ε/2≡ε (fst Δ)))
                             (isTrans≤<ᵣ _ _ _ zzz'
                                     (<ᵣMonotone+ᵣ
                                       _ _ _ _ q<Δ/2 q-x<Δ/2))
                      in ⊥.rec (isAsym<ᵣ _ _ Δ<absX zzzz')
                in ⊎.rec
                    (λ Δ≤q →
                       subst2 _<ᵣ_
                          (+-ᵣ (rat (fst (/2₊ Δ))))
                          ((cong (rat q +ᵣ_) (-ᵣDistr (rat q) (-ᵣ x))
                             ∙ (λ i → +ᵣAssoc (rat q) (-ᵣ (rat q))
                                (-ᵣInvol x i) i) ∙
                              cong (_+ᵣ x) (+-ᵣ (rat q)) ∙ +IdL x)) --
                          (≤<ᵣMonotone+ᵣ (rat (fst (/2₊ Δ))) (rat q) _ _
                            (≤ℚ→≤ᵣ _ _ Δ≤q) (-ᵣ<ᵣ _ _ q-x<Δ/2)))
                   (zzz ∘S <ℚ→<ᵣ _ _ )
                    (ℚ.Dichotomyℚ (fst (/2₊ Δ)) q)
              z← : q ℚ.≤ 0 → x <ᵣ 0
              z← q≤0 = isTrans<≤ᵣ _ _ _ x<q (≤ℚ→≤ᵣ q 0 q≤0)
          in ⊎.rec (inr ∘ z←) (inl ∘ z→) (ℚ.Dichotomyℚ q 0))
         (∃rationalApprox< x (/2₊ Δ)))
     (lowerℚBound _ 0<absX)



＃≃0<dist : ∀ x y → x ＃ y ≃ (0 <ᵣ (absᵣ (x +ᵣ (-ᵣ y))))
＃≃0<dist x y = propBiimpl→Equiv (isProp＃ _ _) squash₁
  (⊎.rec ((λ x<y → subst (0 <ᵣ_) (minusComm-absᵣ y x)
                (isTrans<≤ᵣ _ _ _ (subst (_<ᵣ (y +ᵣ (-ᵣ x)))
             (+-ᵣ x) (<ᵣ-+o _ _ (-ᵣ x) x<y)) (≤absᵣ _ ))))
         (λ y<x → isTrans<≤ᵣ _ _ _ (subst (_<ᵣ (x +ᵣ (-ᵣ y)))
             (+-ᵣ y) (<ᵣ-+o _ _ (-ᵣ y) y<x)) (≤absᵣ _ )))
  (⊎.rec (inr ∘S subst2 _<ᵣ_ (+IdL _) L𝐑.lem--00 ∘S <ᵣ-+o _ _ y)
         (inl ∘S subst2 _<ᵣ_ L𝐑.lem--05 (+IdR _) ∘S <ᵣ-o+ _ _ y)
          ∘S decCut (x +ᵣ (-ᵣ y)))

-- ＃≃abs< : ∀ x y → absᵣ x <ᵣ y ≃
-- ＃≃abs< : ?

isSym＃ : BinaryRelation.isSym _＃_
isSym＃ _ _ = fst ⊎-swap-≃

0＃→0<abs : ∀ r → 0 ＃ r → 0 <ᵣ absᵣ r
0＃→0<abs r 0＃r =
  subst (rat 0 <ᵣ_) (cong absᵣ (+IdR r))
    (fst (＃≃0<dist r 0) (isSym＃ 0 r 0＃r))

≤ᵣ-·o : ∀ m n o → 0 ℚ.≤ o  →  m ≤ᵣ n → (m ·ᵣ rat o ) ≤ᵣ (n ·ᵣ rat o)
≤ᵣ-·o m n o 0≤o p = sym (·ᵣMaxDistrPos m n o 0≤o) ∙
  cong (_·ᵣ rat o) p


≤ᵣ-o· : ∀ m n o → 0 ℚ.≤ o →  m ≤ᵣ n → (rat o ·ᵣ m ) ≤ᵣ (rat o ·ᵣ n)
≤ᵣ-o· m n o q p =
    cong₂ maxᵣ (·ᵣComm _ _ ) (·ᵣComm _ _ ) ∙ ≤ᵣ-·o m n o q p ∙ ·ᵣComm _ _

-- max≤-lem : ∀ x x' → x <ᵣ y → x' <ᵣ y → maxᵣ x x' ≤ᵣ x
-- max≤-lem x x' y = {!!}

<ᵣ→Δ : ∀ x y → x <ᵣ y → ∃[ δ ∈ ℚ₊ ] rat (fst δ) <ᵣ y +ᵣ (-ᵣ x)
<ᵣ→Δ x y = PT.map λ ((q , q') , (a , a' , a'')) →
              /2₊ (ℚ.<→ℚ₊ q q' a') ,
                let zz = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ a') a''
                    zz' = -ᵣ≤ᵣ _ _ a
                    zz'' = ≤ᵣMonotone+ᵣ _ _ _ _ a'' zz'
                in isTrans<≤ᵣ _ _ _
                       (<ℚ→<ᵣ _ _ (x/2<x (ℚ.<→ℚ₊ q q' a')))
                       zz''

a<b-c⇒c<b-a : ∀ a b c → a <ᵣ b +ᵣ (-ᵣ c) → c <ᵣ b +ᵣ (-ᵣ a)
a<b-c⇒c<b-a a b c p =
   subst2 _<ᵣ_ (L𝐑.lem--05 {a} {c})
                (L𝐑.lem--060 {b} {c} {a})
     (<ᵣ-+o _ _ (c +ᵣ (-ᵣ a)) p)

a<b-c⇒a+c<b : ∀ a b c → a <ᵣ b +ᵣ (-ᵣ c) → a +ᵣ c <ᵣ b
a<b-c⇒a+c<b a b c p =
   subst ((a +ᵣ c) <ᵣ_)
        (L𝐑.lem--00 {b} {c})
     (<ᵣ-+o _ _ c p)


a-b≤c⇒a-c≤b : ∀ a b c → a +ᵣ (-ᵣ b) ≤ᵣ c  → a +ᵣ (-ᵣ c) ≤ᵣ b
a-b≤c⇒a-c≤b a b c p =
  subst2 _≤ᵣ_
    (L𝐑.lem--060 {a} {b} {c})
    (L𝐑.lem--05 {c} {b})
     (≤ᵣ-+o _ _ (b +ᵣ (-ᵣ c)) p)

a-b<c⇒a-c<b : ∀ a b c → a +ᵣ (-ᵣ b) <ᵣ c  → a +ᵣ (-ᵣ c) <ᵣ b
a-b<c⇒a-c<b a b c p =
  subst2 _<ᵣ_
    (L𝐑.lem--060 {a} {b} {c})
    (L𝐑.lem--05 {c} {b})
     (<ᵣ-+o _ _ (b +ᵣ (-ᵣ c)) p)


a-b<c⇒a<c+b : ∀ a b c → a +ᵣ (-ᵣ b) <ᵣ c  → a <ᵣ c +ᵣ b
a-b<c⇒a<c+b a b c p =
  subst (_<ᵣ (c +ᵣ b))
    (L𝐑.lem--00 {a} {b})
     (<ᵣ-+o _ _ b p)

≤-o+-cancel : ∀ m n o →  o +ᵣ m ≤ᵣ o +ᵣ n → m ≤ᵣ n
≤-o+-cancel m n o p =
     subst2 (_≤ᵣ_) L𝐑.lem--04 L𝐑.lem--04
     (≤ᵣ-o+ _ _ (-ᵣ o) p)

x≤y→0≤y-x : ∀ x y →  x ≤ᵣ y  → 0 ≤ᵣ y +ᵣ (-ᵣ x)
x≤y→0≤y-x x y p =
  subst (_≤ᵣ y +ᵣ (-ᵣ x)) (+-ᵣ x) (≤ᵣ-+o x y (-ᵣ x) p)

x<y→0<y-x : ∀ x y →  x <ᵣ y  → 0 <ᵣ y +ᵣ (-ᵣ x)
x<y→0<y-x x y p =
  subst (_<ᵣ y +ᵣ (-ᵣ x)) (+-ᵣ x) (<ᵣ-+o x y (-ᵣ x) p)

0<y-x→x<y : ∀ x y → 0 <ᵣ y +ᵣ (-ᵣ x) → x <ᵣ y
0<y-x→x<y x y p =
  subst2 (_<ᵣ_)
   (+IdL x) (sym (L𝐑.lem--035 {y} {x}))
    (<ᵣ-+o 0 (y +ᵣ (-ᵣ x)) x p)



max-lem : ∀ x x' y → maxᵣ (maxᵣ x y) (maxᵣ x' y) ≡ (maxᵣ (maxᵣ x x') y)
max-lem x x' y = maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ y) (maxᵣComm _ _)
  ∙ sym (maxᵣAssoc _ _ _) ∙
    cong (maxᵣ x') (sym (maxᵣAssoc _ _ _) ∙ cong (maxᵣ x) (maxᵣIdem y))
     ∙ maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ y) (maxᵣComm _ _)



minᵣIdem : ∀ x → minᵣ x x ≡ x
minᵣIdem = ≡Continuous _ _
  (cont₂minᵣ _ _ IsContinuousId IsContinuousId)
  IsContinuousId
  (cong rat ∘ ℚ.minIdem)


min-lem : ∀ x x' y → minᵣ (minᵣ x y) (minᵣ x' y) ≡ (minᵣ (minᵣ x x') y)
min-lem x x' y = minᵣAssoc _ _ _ ∙ cong (flip minᵣ y) (minᵣComm _ _)
  ∙ sym (minᵣAssoc _ _ _) ∙
    cong (minᵣ x') (sym (minᵣAssoc _ _ _) ∙ cong (minᵣ x) (minᵣIdem y))
     ∙ minᵣAssoc _ _ _ ∙ cong (flip minᵣ y) (minᵣComm _ _)


max≤-lem : ∀ x x' y → x ≤ᵣ y → x' ≤ᵣ y → maxᵣ x x' ≤ᵣ y
max≤-lem x x' y p p' =
  sym (max-lem _ _ _)
   ∙∙ cong₂ maxᵣ p p' ∙∙ maxᵣIdem y

max<-lem : ∀ x x' y → x <ᵣ y → x' <ᵣ y → maxᵣ x x' <ᵣ y
max<-lem x x' y = PT.map2
  λ ((q , q') , (a , a' , a''))
    ((r , r') , (b , b' , b'')) →
     (ℚ.max q r , ℚ.max q' r') ,
       (max≤-lem _ _ (rat (ℚ.max q r))
         (isTrans≤ᵣ _ _ _ a (≤ℚ→≤ᵣ _ _ (ℚ.≤max q r)))
         ((isTrans≤ᵣ _ _ _ b (≤ℚ→≤ᵣ _ _ (ℚ.≤max' q r)))) ,
          (ℚ.<MonotoneMaxℚ _ _ _ _ a' b' , max≤-lem _ _ _ a'' b''))

minDistMaxᵣ : ∀ x y y' →
  maxᵣ x (minᵣ y y') ≡ minᵣ (maxᵣ x y) (maxᵣ x y')
minDistMaxᵣ x y y' = ≡Continuous _ _
   (IsContinuousMaxR _)
   (cont₂minᵣ _ _ (IsContinuousMaxR _) (IsContinuousMaxR _))
   (λ xR →
     ≡Continuous _ _
       (IsContinuous∘ _ _ (IsContinuousMaxL (rat xR)) ((IsContinuousMinR y')))
       (IsContinuous∘ _ _ (IsContinuousMinR _) (IsContinuousMaxL (rat xR)))
       (λ yR →
         ≡Continuous _ _
           (IsContinuous∘ _ _ (IsContinuousMaxL (rat xR))
             ((IsContinuousMinL (rat yR))))
           (IsContinuous∘ _ _ (IsContinuousMinL (maxᵣ (rat xR) (rat yR)))
             (IsContinuousMaxL (rat xR)))
           (cong rat ∘ ℚ.minDistMax xR yR ) y')
       y)
   x


≤maxᵣ : ∀ m n →  m ≤ᵣ maxᵣ m n
≤maxᵣ m n = maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ n) (maxᵣIdem m)

≤min-lem : ∀ x y y' → x ≤ᵣ y → x ≤ᵣ y' →  x ≤ᵣ minᵣ y y'
≤min-lem x y y' p p' =
   minDistMaxᵣ x y y' ∙ cong₂ minᵣ p p'


<min-lem : ∀ x x' y → y <ᵣ x → y <ᵣ x' →  y <ᵣ minᵣ x x'
<min-lem x x' y = PT.map2
  λ ((q , q') , (a , a' , a''))
    ((r , r') , (b , b' , b'')) →
     (ℚ.min q r , ℚ.min q' r') , ≤min-lem _ _ _ a b
        , ℚ.<MonotoneMinℚ _ _ _ _ a' b' ,
            ≤min-lem (rat (ℚ.min q' r')) x x'
             (isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤ q' r')) a'')
             (isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤' q' r')) b'')




ℝ₊min : (m : ℝ₊) (n : ℝ₊) → 0 <ᵣ minᵣ (fst m) (fst n)
ℝ₊min (m , <m) (n , <n) = <min-lem m n 0 <m <n

maxAbsorbLMinᵣ : ∀ x y → maxᵣ x (minᵣ x y) ≡ x
maxAbsorbLMinᵣ x =
  ≡Continuous _ _
    (IsContinuous∘ _ _
      (IsContinuousMaxL _) (IsContinuousMinL x))
      (IsContinuousConst _)
     λ y' →
       ≡Continuous _ _
          (cont₂maxᵣ _ _ IsContinuousId (IsContinuousMinR _))
        IsContinuousId
         (λ x' → cong rat (ℚ.maxAbsorbLMin x' y')) x

min≤ᵣ : ∀ m n → minᵣ m n ≤ᵣ m
min≤ᵣ m n = maxᵣComm _ _ ∙ maxAbsorbLMinᵣ _ _

min≤ᵣ' : ∀ m n → minᵣ m n ≤ᵣ n
min≤ᵣ' m n = subst (_≤ᵣ n) (minᵣComm n m) (min≤ᵣ n m)

invℝ'' : Σ (∀ r → ∃[ σ ∈ ℚ₊ ] (rat (fst σ) <ᵣ r) → ℝ)
      λ _ → Σ (∀ r → 0 <ᵣ r → ℝ) (IsContinuousWithPred (λ r → _ , squash₁))
invℝ'' = f , (λ r 0<r → f r (lowerℚBound r 0<r)) ,
   ctnF

 where

 2co : ∀ σ σ' r
    → (rat (fst σ ) <ᵣ r)
    → (rat (fst σ') <ᵣ r)
    → fst (Invᵣ-restr σ) r ≡ fst (Invᵣ-restr σ') r

 2co σ σ' = Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop _
  w .Elimℝ-Prop.ratA x σ<x σ'<x =
    cong (rat ∘ fst ∘ invℚ₊)
      (ℚ₊≡ (ℚ.≤→max _ _ (≤ᵣ→≤ℚ _  _ (<ᵣWeaken≤ᵣ _ _ σ<x))
           ∙ sym (ℚ.≤→max _ _ (≤ᵣ→≤ℚ _  _ (<ᵣWeaken≤ᵣ _ _ σ'<x))) ))
  w .Elimℝ-Prop.limA x y R σ<limX σ'<limX = eqℝ _ _ λ ε →
    PT.rec (isProp∼ _ _ _)
      (λ (q , σ⊔<q , q<limX) →
       let
           φ*ε = (((invℚ₊ ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))))
                                   ℚ₊· ε))


           φ*σ = (/2₊ (ℚ.<→ℚ₊ (fst σ⊔) q (<ᵣ→<ℚ _ _ σ⊔<q)))

           φ* : ℚ₊
           φ* = ℚ.min₊ (/2₊ φ*ε) φ*σ



           limRestr'' : rat (fst φ*)
               ≤ᵣ (rat q +ᵣ (-ᵣ rat (fst σ⊔))) ·ᵣ rat [ 1 / 2 ]
           limRestr'' =
             let zz = ((ℚ.min≤'
                    ((fst (/2₊ ((invℚ₊ ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))))
                                   ℚ₊· ε))))
                                    (fst (/2₊
                             (ℚ.<→ℚ₊ (fst σ⊔) q (<ᵣ→<ℚ _ _ σ⊔<q))
                          ))))
             in subst (rat (fst φ*) ≤ᵣ_)
                (rat·ᵣrat _ _)
                  (≤ℚ→≤ᵣ (fst φ*)
                    (fst (/2₊
                             (ℚ.<→ℚ₊ (fst σ⊔) q (<ᵣ→<ℚ _ _ σ⊔<q))
                          )) zz)


           limRestr' : rat (fst φ* ℚ.+ fst φ*)
               ≤ᵣ (lim x y +ᵣ (-ᵣ rat (fst σ⊔)))
           limRestr' =
             let zz : ((rat q +ᵣ (-ᵣ rat (fst σ⊔)))) ≤ᵣ
                        ((lim x y +ᵣ (-ᵣ rat (fst σ⊔))) )
                 zz = ≤ᵣ-+o (rat q) (lim x y) (-ᵣ rat (fst σ⊔))
                          (<ᵣWeaken≤ᵣ _ _ q<limX)
             in  subst2 _≤ᵣ_
                  (sym (rat·ᵣrat _ _) ∙
                   cong rat (distℚ! (fst φ*) ·[ ge[ 2 ]  ≡ ge1 +ge ge1 ]))
                    (sym (·ᵣAssoc _ _ _) ∙∙
                      cong ((lim x y +ᵣ (-ᵣ rat (fst σ⊔))) ·ᵣ_)
                       (sym (rat·ᵣrat _ _)
                         ∙ (cong rat (𝟚.toWitness {Q = ℚ.discreteℚ
                           ([ 1 / 2 ] ℚ.· 2) 1} tt))) ∙∙
                      ·IdR _ )
                   (≤ᵣ-·o _ _ 2 (ℚ.decℚ≤? {0} {2}) (isTrans≤ᵣ _ _ _
                   limRestr'' (≤ᵣ-·o _ _ [ 1 / 2 ] (ℚ.decℚ≤? {0} {[ 1 / 2 ]})
                         zz)))


           limRestr : rat (fst σ⊔)
               ≤ᵣ ((lim x y +ᵣ (-ᵣ rat (fst φ* ℚ.+ fst φ*))))
           limRestr = subst2 _≤ᵣ_
             (L𝐑.lem--00 {rat (fst σ⊔)} {(rat (fst φ*) +ᵣ rat (fst φ*))})
               (L𝐑.lem--061
                 {rat (fst σ⊔)} {rat (fst φ* ℚ.+ fst φ*)} {lim x y} )
             (≤ᵣ-o+ _ _
               (rat (fst σ⊔) +ᵣ (-ᵣ (rat (fst φ* ℚ.+ fst φ*))))
                 limRestr')

           ∣x-limX∣ : (lim x y +ᵣ (-ᵣ rat (fst φ* ℚ.+ fst φ*))) <ᵣ x φ*

           ∣x-limX∣ =
             let zz = isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                  (subst (_<ᵣ rat (fst φ* ℚ.+ fst φ*))
                   (minusComm-absᵣ _ _)
                   (fst (∼≃abs<ε _ _ (φ* ℚ₊+ φ*))
                   $ 𝕣-lim-self x y φ* φ*))
             in subst2 _<ᵣ_ (L𝐑.lem--060 {lim x y} {x φ*}
                           {rat (fst φ* ℚ.+ fst φ*)})
                  (L𝐑.lem--05 {rat (fst φ* ℚ.+ fst φ*)} {x φ*})
                   (<ᵣ-+o _ _ (x φ* +ᵣ (-ᵣ rat (fst φ* ℚ.+ fst φ*))) zz)



           φ : ℚ₊
           φ = (invℚ₊ (σ ℚ₊· σ)) ℚ₊·  φ*
           φ' : ℚ₊
           φ' = (invℚ₊ (σ' ℚ₊· σ')) ℚ₊·  φ*
           σ⊔<Xφ* : rat (fst σ⊔) <ᵣ x φ*
           σ⊔<Xφ* = isTrans≤<ᵣ _ _ _ limRestr ∣x-limX∣
           σ<Xφ* : rat (fst σ) <ᵣ x φ*
           σ<Xφ* = isTrans≤<ᵣ _ _ _
              (≤ℚ→≤ᵣ _ _ (ℚ.≤max (fst σ) (fst σ'))) σ⊔<Xφ*
           σ'<Xφ* : rat (fst σ') <ᵣ x φ*
           σ'<Xφ* = isTrans≤<ᵣ _ _ _
              (≤ℚ→≤ᵣ _ _ (ℚ.≤max' (fst σ) (fst σ'))) σ⊔<Xφ*

           preε'< :  (fst ((invℚ₊ (σ ℚ₊· σ)) ℚ₊·  φ*)
                                   ℚ.+ fst ((invℚ₊ (σ' ℚ₊· σ')) ℚ₊·  φ*))
                                    ℚ.≤ fst (/2₊ ε)
           preε'< = subst2 ℚ._≤_
             (ℚ.·DistR+ _ _ (fst φ*)) (
                cong (fst (invℚ₊ (σ ℚ₊· σ) ℚ₊+ invℚ₊ (σ' ℚ₊· σ')) ℚ.·_)
                   (sym (ℚ.·Assoc _ _ _))
                 ∙ ℚ.y·[x/y] ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))) (fst (/2₊ ε)) )
               (ℚ.≤-o· _ _ (fst ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))))
                              (ℚ.0≤ℚ₊ ((invℚ₊ (σ ℚ₊· σ))
                                   ℚ₊+ (invℚ₊ (σ' ℚ₊· σ'))))
                             (
                               (ℚ.min≤ (fst (/2₊ φ*ε)) (fst φ*σ))))

           ε'< : 0< (fst ε ℚ.- (fst ((invℚ₊ (σ ℚ₊· σ)) ℚ₊·  φ*)
                                   ℚ.+ fst ((invℚ₊ (σ' ℚ₊· σ')) ℚ₊·  φ*)))
           ε'< = snd (ℚ.<→ℚ₊ (fst ((invℚ₊ (σ ℚ₊· σ)) ℚ₊·  φ*)
                                   ℚ.+ fst ((invℚ₊ (σ' ℚ₊· σ')) ℚ₊·  φ*))
                                    (fst ε)
              (ℚ.isTrans≤< _ _ _ preε'< (x/2<x ε)))


           φ= = ℚ₊≡ {φ*} $ sym (ℚ.[y·x]/y (invℚ₊ (σ ℚ₊· σ)) (fst φ*))

           φ'= = ℚ₊≡ {φ*} $ sym (ℚ.[y·x]/y (invℚ₊ (σ' ℚ₊· σ')) (fst φ*))


           R' : _
           R' = invEq (∼≃≡ _ _) (R φ* σ<Xφ* σ'<Xφ* )
             ((fst ε ℚ.- (fst φ ℚ.+ fst φ')) , ε'<)


       in (lim-lim _ _ ε φ φ' _ _ ε'<
                (((cong ((fst (Invᵣ-restr σ)) ∘ x) (φ=))
                   subst∼[ refl ] (cong ((fst (Invᵣ-restr σ')) ∘ x)
                     (φ'=))) R')))
      (denseℚinℝ (rat (fst σ⊔)) (lim x y) σ⊔<limX)
   where
   σ⊔ = ℚ.max₊ σ σ'

   σ⊔<limX : rat (fst σ⊔) <ᵣ lim x y
   σ⊔<limX = max<-lem (rat (fst σ)) (rat (fst σ'))
      (lim x y) σ<limX σ'<limX


  w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isSetℝ _ _

 f' : ∀ r → Σ ℚ₊ (λ σ → rat (fst σ) <ᵣ r) → ℝ
 f' r (σ , σ<) = fst (Invᵣ-restr σ) r

 f : ∀ r → ∃[ σ ∈ ℚ₊ ] (rat (fst σ) <ᵣ r) → ℝ
 f r = PT.rec→Set {B = ℝ} isSetℝ (f' r)
          λ (σ , σ<r) (σ' , σ'<r) → 2co σ σ' r σ<r σ'<r


 ctnF : ∀ u ε u∈ → ∃[ δ ∈ ℚ₊ ]
                 (∀ v v∈P → u ∼[ δ ] v →
                  f u (lowerℚBound u u∈) ∼[ ε ] f v (lowerℚBound v v∈P))
 ctnF u ε u∈ = ctnF' (lowerℚBound u u∈)

  where
  ctnF' : ∀ uu → ∃[ δ ∈ ℚ₊ ]
                 (∀ v v∈P → u ∼[ δ ] v →
                  f u uu ∼[ ε ] f v (lowerℚBound v v∈P))
  ctnF' = PT.elim (λ _ → squash₁)
    λ (σ , σ<u) →
     let zz : ∃[ δ ∈ ℚ₊ ] ((v₁ : ℝ) →  u ∼[ δ ] v₁
                      → f u ∣ σ , σ<u ∣₁ ∼[ ε ] Invᵣ-restr σ .fst v₁)
         zz = Lipschitz→IsContinuous (invℚ₊ (σ ℚ₊· σ))
                 (λ z → Invᵣ-restr σ .fst z)
                 (snd (Invᵣ-restr σ) ) u ε

         zz' : ∃[ δ ∈ ℚ₊ ] (∀ v v∈ →
                    u ∼[ δ ] v →
                  f u ∣ σ , σ<u ∣₁ ∼[ ε ] f v (lowerℚBound v v∈))
         zz' = PT.rec2 squash₁
             (uncurry (λ δ R (η , η<u-σ)  →
               let δ' = ℚ.min₊ δ η
               in ∣ δ' ,
                   (λ v v∈ →
                      PT.elim {P = λ vv → u ∼[ δ' ] v →
                               f u ∣ σ , σ<u ∣₁ ∼[ ε ] f v vv}
                          (λ _ → isPropΠ λ _ → isProp∼ _ _ _)
                          (λ (σ' , σ'<v) u∼v →
                             let zuz :  (u +ᵣ (-ᵣ v)) <ᵣ rat (fst η)
                                 zuz = isTrans≤<ᵣ _ _ _ (≤absᵣ (u +ᵣ (-ᵣ v)))
                                    (isTrans<≤ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) u∼v)
                                       (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst η))))

                                 u-η≤v : u +ᵣ (-ᵣ rat (fst η)) ≤ᵣ v
                                 u-η≤v = a-b≤c⇒a-c≤b _ _ _
                                          (<ᵣWeaken≤ᵣ _ _ zuz)
                                 σ<u-η : rat (fst σ) <ᵣ u +ᵣ (-ᵣ rat (fst η))
                                 σ<u-η = a<b-c⇒c<b-a _ _ _ η<u-σ
                                 σ<v : rat (fst σ) <ᵣ v
                                 σ<v = isTrans<≤ᵣ _ _ _ σ<u-η u-η≤v
                             in subst (f u ∣ σ , σ<u ∣₁ ∼[ ε ]_)
                                        (2co σ σ' v σ<v σ'<v)
                                        (R v
                                         (∼-monotone≤ (ℚ.min≤ _ _) u∼v)))
                          ((lowerℚBound v v∈))) ∣₁
                          ))
           zz (<ᵣ→Δ _ _ σ<u)
     in zz'

invℝ' : Σ (∀ r → 0 <ᵣ r → ℝ) (IsContinuousWithPred (λ r → _ , squash₁))
invℝ' = snd invℝ''

invℝ'-rat : ∀ q p' p →
             fst invℝ' (rat q) p ≡
              rat (fst (invℚ₊ (q , p')))
invℝ'-rat q p' p = PT.elim (λ xx →
                       isSetℝ ((fst invℝ'') (rat q) xx) _)
                        (λ x → cong (rat ∘ fst ∘ invℚ₊)
                        (ww x)) (lowerℚBound (rat q) p)

 where
 ww : ∀ x → (ℚ.maxWithPos (fst x) q) ≡ (q , p')
 ww x = ℚ₊≡ (ℚ.≤→max (fst (fst x)) q (ℚ.<Weaken≤ _ _ (<ᵣ→<ℚ _ _ (snd x))))



invℝ'-pos : ∀ u p →
             0 <ᵣ fst invℝ' u p
invℝ'-pos u p = PT.rec squash₁
  (λ (n , u<n) →
    PT.rec squash₁
       (λ (σ , X) →
         PT.rec squash₁
           (λ ((q , q'*) , x* , x' , x''*) →
             let q' : ℚ
                 q' = ℚ.min q'* [ pos (ℕ₊₁→ℕ n) / 1 ]
                 x : q' ℚ.- q ℚ.< fst σ
                 x = ℚ.isTrans≤< _ _ _ (
                    ℚ.≤-+o q' q'* (ℚ.- q)
                      (ℚ.min≤ q'* [ pos (ℕ₊₁→ℕ n) / 1 ])) x*
                 x'' : u <ᵣ rat q'
                 x'' = <min-lem _ _ _ x''* (isTrans≤<ᵣ _ _ _ (≤absᵣ u) u<n)


                 0<q' : 0 <ᵣ rat q'
                 0<q' = isTrans<ᵣ _ _ _ p x''
                 z' : rat [ 1 / n ] ≤ᵣ invℝ' .fst (rat q') 0<q'
                 z' = subst (rat [ 1 / n ] ≤ᵣ_) (sym (invℝ'-rat q'
                               (ℚ.<→0< q' (<ᵣ→<ℚ _ _ 0<q')) 0<q'))
                            (≤ℚ→≤ᵣ _ _ (
                             ℚ.invℚ≤invℚ ([ ℚ.ℕ₊₁→ℤ n / 1 ] , _)
                               (q' , ℚ.<→0< q' (<ᵣ→<ℚ [ pos 0 / 1 ] q' 0<q'))
                                ((ℚ.min≤' q'* [ pos (ℕ₊₁→ℕ n) / 1 ]))))
                 z : ((invℝ' .fst (rat q') 0<q') +ᵣ (-ᵣ rat [ 1 / n ]))
                       <ᵣ
                       (invℝ' .fst u p)
                 z = a-b<c⇒a-c<b _ (invℝ' .fst u p) _
                      (isTrans≤<ᵣ _ _ _ (≤absᵣ _) (fst (∼≃abs<ε _ _ _)
                      (sym∼ _ _ _  (X (rat q') 0<q'
                       (sym∼ _ _ _ (invEq (∼≃abs<ε (rat q') u σ) (
                          isTrans≤<ᵣ _ _ _
                            (subst (_≤ᵣ ((rat q') +ᵣ (-ᵣ (rat q))))
                              (sym (absᵣNonNeg (rat q' +ᵣ (-ᵣ u))
                                (x≤y→0≤y-x _ _ (<ᵣWeaken≤ᵣ _ _ x''))))
                              (≤ᵣ-o+ _ _ _ (-ᵣ≤ᵣ _ _ (<ᵣWeaken≤ᵣ _ _ x'))))
                           (<ℚ→<ᵣ _ _ x))))))))

             in isTrans≤<ᵣ _ _ _ (x≤y→0≤y-x _ _ z') z
             )
           (∃rationalApprox u σ))
      (snd invℝ' u ([ 1 / n ]  , _) p))
  (getClamps u)

signᵣ : ∀ r → 0 ＃ r → ℝ
signᵣ _ = ⊎.rec (λ _ → rat 1) (λ _ → rat -1)

0<signᵣ : ∀ r 0＃r → 0 <ᵣ r → 0 <ᵣ signᵣ r 0＃r
0<signᵣ r (inl x) _ = <ℚ→<ᵣ _ _ ((𝟚.toWitness {Q = ℚ.<Dec 0 1} _))
0<signᵣ r (inr x) y = ⊥.rec (isAsym<ᵣ _ _ x y)

signᵣ-rat : ∀ r p  → signᵣ (rat r) p ≡ rat (ℚ.sign r)
signᵣ-rat r (inl x) = cong rat (sym (fst (ℚ.<→sign r) (<ᵣ→<ℚ _ _ x)))
signᵣ-rat r (inr x) = cong rat (sym (snd (snd (ℚ.<→sign r)) (<ᵣ→<ℚ _ _ x)))

0＃ₚ : ℝ → hProp ℓ-zero
0＃ₚ r = 0 ＃ r , isProp＃ _ _

-- HoTT Theorem (11.3.47)

IsContinuousWithPredSignᵣ : IsContinuousWithPred 0＃ₚ signᵣ
IsContinuousWithPredSignᵣ u ε =
 ⊎.elim
  (λ 0<u → PT.map (λ (q , 0<q , q<u) →
             ((q , ℚ.<→0< q (<ᵣ→<ℚ _ _ 0<q))) ,
              λ v v∈P v∼u →
                ⊎.elim {C = λ v∈P → signᵣ u (inl 0<u) ∼[ ε ] signᵣ v v∈P}
                  (λ _ → refl∼ _ _)
                  (⊥.rec ∘ (isAsym<ᵣ 0 v
                    (subst2 _<ᵣ_ (+ᵣComm _ _ ∙ +-ᵣ _)
                        (L𝐑.lem--04 {rat q} {v})
                         (<ᵣMonotone+ᵣ _ _ _ _ (-ᵣ<ᵣ _ _ q<u)
                       (a-b<c⇒a<c+b _ _ _ (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                          (fst (∼≃abs<ε _ _ _) v∼u))))))) v∈P)
         (denseℚinℝ 0 u 0<u))
  (λ u<0 → PT.map (λ (q , u<q , q<0) →
             (ℚ.- q , ℚ.<→0< (ℚ.- q) (ℚ.minus-< _ _ (<ᵣ→<ℚ _ _ q<0))) ,
              λ v v∈P v∼u →
                ⊎.elim {C = λ v∈P → signᵣ u (inr u<0) ∼[ ε ] signᵣ v v∈P}
                  ((⊥.rec ∘ (isAsym<ᵣ v 0
                    (subst2 _<ᵣ_  (L𝐑.lem--05 {u} {v})
                     (+-ᵣ (rat q)) (<ᵣMonotone+ᵣ _ _ _ _
                       u<q (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                          (fst (∼≃abs<ε _ _ _) (sym∼ _ _ _ v∼u))))))))
                  (λ _ → refl∼ _ _) v∈P)
             (denseℚinℝ u 0 u<0))



-ᵣ≡[-1·ᵣ] : ∀ x → -ᵣ x ≡ (-1) ·ᵣ x
-ᵣ≡[-1·ᵣ] = ≡Continuous _ _
   IsContinuous-ᵣ
   (IsContinuous·ᵣL -1)
   λ r → rat·ᵣrat _ _


openPred< : ∀ x → ⟨ openPred (λ y → (x <ᵣ y) , squash₁)  ⟩
openPred< x y =
     PT.map (map-snd (λ {q} a<y-x v
        →   isTrans<ᵣ _ _ _
                (a<b-c⇒c<b-a (rat (fst q)) y x a<y-x )
          ∘S a-b<c⇒a-c<b y v (rat (fst q))
          ∘S isTrans≤<ᵣ _ _ _ (≤absᵣ _)
          ∘S fst (∼≃abs<ε _ _ _)))
  ∘S lowerℚBound (y +ᵣ (-ᵣ x))
  ∘S x<y→0<y-x x y

openPred> : ∀ x → ⟨ openPred (λ y → (y <ᵣ x) , squash₁)  ⟩
openPred> x y =
       PT.map (map-snd (λ {q} q<x-y v
        →     flip (isTrans<ᵣ _ _ _)
                (a<b-c⇒a+c<b (rat (fst q)) x y q<x-y )
          ∘S a-b<c⇒a<c+b v y (rat (fst q))
          ∘S isTrans≤<ᵣ _ _ _ (≤absᵣ _)
          ∘S fst (∼≃abs<ε _ _ _)
          ∘S sym∼ _ _ _ ))
  ∘S lowerℚBound (x +ᵣ (-ᵣ y))
  ∘S x<y→0<y-x y x


isOpenPred0＃ : ⟨ openPred 0＃ₚ ⟩
isOpenPred0＃ x =
 ⊎.rec
   (PT.map (map-snd ((inl ∘_) ∘_)) ∘ openPred< 0 x)
   (PT.map (map-snd ((inr ∘_) ∘_)) ∘ openPred> 0 x)



·invℝ' : ∀ r 0<r → (r ·ᵣ fst invℝ' (r) 0<r) ≡ 1
·invℝ' r =  ∘diag $
  ≡ContinuousWithPred _ _ (openPred< 0) (openPred< 0)
   _ _ (cont₂·ᵣWP _ _ _
          (AsContinuousWithPred _ _ IsContinuousId)
          (snd invℝ'))
        (AsContinuousWithPred _ _ (IsContinuousConst 1))
        (λ r r∈ r∈' → cong (rat r ·ᵣ_) (invℝ'-rat r _ r∈)
          ∙∙ sym (rat·ᵣrat _ _) ∙∙ cong rat (ℚ.x·invℚ₊[x]
            (r , ℚ.<→0< _ (<ᵣ→<ℚ _ _ r∈)))) r


sign²=1 :  ∀ r 0＃r → (signᵣ r 0＃r) ·ᵣ (signᵣ r 0＃r) ≡ 1
sign²=1 r = ⊎.elim
    (λ _ → sym (rat·ᵣrat _ _))
    (λ _ → sym (rat·ᵣrat _ _))

sign·absᵣ : ∀ r 0＃r → absᵣ r ·ᵣ (signᵣ r 0＃r) ≡ r
sign·absᵣ r = ∘diag $
  ≡ContinuousWithPred 0＃ₚ 0＃ₚ isOpenPred0＃ isOpenPred0＃
      (λ r 0＃r → absᵣ r ·ᵣ (signᵣ r 0＃r))
       (λ r _ → r)
        (cont₂·ᵣWP _ _ _
          (AsContinuousWithPred _ _ IsContinuousAbsᵣ)
          IsContinuousWithPredSignᵣ)
        (AsContinuousWithPred _ _ IsContinuousId)
        (λ r 0＃r 0＃r' → (cong₂ _·ᵣ_ refl (signᵣ-rat r 0＃r)
          ∙ sym (rat·ᵣrat _ _))
          ∙ cong rat (cong (ℚ._· ℚ.sign r) (sym (ℚ.abs'≡abs r))
           ∙ ℚ.sign·abs r) ) r

-- HoTT Theorem (11.3.47)

abstract
 invℝ : ∀ r → 0 ＃ r → ℝ
 invℝ r 0＃r = signᵣ r 0＃r ·ᵣ fst invℝ' (absᵣ r) (0＃→0<abs r 0＃r)


 invℝimpl : ∀ r 0＃r → invℝ r 0＃r ≡
             signᵣ r 0＃r ·ᵣ fst invℝ' (absᵣ r) (0＃→0<abs r 0＃r)

 invℝimpl r 0＃r = refl

 invℝ≡ : ∀ r 0＃r 0＃r' →
            invℝ r 0＃r ≡ invℝ r 0＃r'
 invℝ≡ r 0＃r 0＃r' = cong (invℝ r) (isProp＃ _ _ _ _)

 IsContinuousWithPredInvℝ : IsContinuousWithPred (λ _ → _ , isProp＃ _ _) invℝ
 IsContinuousWithPredInvℝ =
    IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ (λ r x → x)
    (cont₂·ᵣWP 0＃ₚ _ _
        IsContinuousWithPredSignᵣ (IsContinuousWP∘ _ _
            _ _ 0＃→0<abs (snd invℝ')
          (AsContinuousWithPred _ _ IsContinuousAbsᵣ)))
      (AsContinuousWithPred _
        _ IsContinuousId)


 invℝ-rat : ∀ q p p' → invℝ (rat q) p ≡ rat (ℚ.invℚ q p')
 invℝ-rat q p p' =
   cong₂ _·ᵣ_ (signᵣ-rat q p) (invℝ'-rat _ _ _) ∙ sym (rat·ᵣrat _ _)


 invℝ-pos : ∀ x → (p : 0 <ᵣ x) → 0 <ᵣ invℝ x (inl p)
 invℝ-pos x p = subst (0 <ᵣ_) (sym (·IdL _))
     (invℝ'-pos (absᵣ x) (0＃→0<abs x (inl p)))


 invℝ-neg : ∀ x → (p : x <ᵣ 0) → invℝ x (inr p) <ᵣ 0
 invℝ-neg x p =
      subst (_<ᵣ 0)
        (-ᵣ≡[-1·ᵣ] _)
        (-ᵣ<ᵣ 0 _ (invℝ'-pos (absᵣ x) (0＃→0<abs x (inr p))))

 invℝ0＃ : ∀ r 0＃r → 0 ＃ (invℝ r 0＃r)
 invℝ0＃ r = ⊎.elim (inl ∘ invℝ-pos r)
                    (inr ∘ invℝ-neg r)



 invℝInvol : ∀ r 0＃r → invℝ (invℝ r 0＃r) (invℝ0＃ r 0＃r) ≡ r
 invℝInvol r 0＃r = ≡ContinuousWithPred
   0＃ₚ 0＃ₚ isOpenPred0＃ isOpenPred0＃
    (λ r 0＃r → invℝ (invℝ r 0＃r) (invℝ0＃ r 0＃r)) (λ x _ → x)
     (IsContinuousWP∘ _ _ _ _ invℝ0＃
       IsContinuousWithPredInvℝ IsContinuousWithPredInvℝ)
     (AsContinuousWithPred _
        _ IsContinuousId)
         (λ r 0＃r 0＃r' →
           let 0#r = (fst (rat＃ 0 r) 0＃r)
               0#InvR = ℚ.0#invℚ r 0#r
           in  cong₂ invℝ (invℝ-rat _ _ _)
                  (isProp→PathP (λ i → isProp＃ _ _) _ _)

              ∙∙ invℝ-rat ((invℚ r (fst (rat＃ [ pos 0 / 1+ 0 ] r) 0＃r)))
                    (invEq (rat＃ 0 _) 0#InvR)
                     (ℚ.0#invℚ r (fst (rat＃ [ pos 0 / 1+ 0 ] r) 0＃r))
                ∙∙ cong rat (ℚ.invℚInvol r 0#r 0#InvR)
             )
    r 0＃r 0＃r

 x·invℝ[x] : ∀ r 0＃r → r ·ᵣ (invℝ r 0＃r) ≡ 1
 x·invℝ[x] r 0＃r =
   cong (_·ᵣ (invℝ r 0＃r)) (sym (sign·absᵣ r 0＃r))
    ∙∙ sym (·ᵣAssoc _ _ _)
    ∙∙ (cong (absᵣ r ·ᵣ_) (·ᵣAssoc _ _ _
      ∙ cong (_·ᵣ (fst invℝ' (absᵣ r) (0＃→0<abs r 0＃r)))
         (sign²=1 r 0＃r) ∙ ·IdL (fst invℝ' (absᵣ r) (0＃→0<abs r 0＃r)))
    ∙ ·invℝ' (absᵣ r) (0＃→0<abs r 0＃r))

_／ᵣ[_,_] : ℝ → ∀ r → 0 ＃ r  → ℝ
q ／ᵣ[ r , 0＃r ] = q ·ᵣ (invℝ r 0＃r)

_／ᵣ₊_ : ℝ → ℝ₊  → ℝ
q ／ᵣ₊ (r , 0<r) = q ／ᵣ[ r , inl (0<r) ]

[x·y]/yᵣ : ∀ q r → (0＃r : 0 ＃ r) →
               ((q ·ᵣ r) ／ᵣ[ r , 0＃r ]) ≡ q
[x·y]/yᵣ q r 0＃r =
      sym (·ᵣAssoc _ _ _)
   ∙∙ cong (q ·ᵣ_) (x·invℝ[x] r 0＃r)
   ∙∙ ·IdR q


[x/y]·yᵣ : ∀ q r → (0＃r : 0 ＃ r) →
               (q ／ᵣ[ r , 0＃r ]) ·ᵣ r ≡ q
[x/y]·yᵣ q r 0＃r =
      sym (·ᵣAssoc _ _ _)
   ∙∙ cong (q ·ᵣ_) (·ᵣComm _ _ ∙ x·invℝ[x] r 0＃r)
   ∙∙ ·IdR q

x/y≡z→x≡z·y : ∀ x q r → (0＃r : 0 ＃ r)
               → (x ／ᵣ[ r , 0＃r ]) ≡ q
               → x ≡ q ·ᵣ r
x/y≡z→x≡z·y x q r 0＃r p =
    sym ([x/y]·yᵣ _ _ _) ∙ cong (_·ᵣ r) p

x·y≡z→x≡z/y : ∀ x q r → (0＃r : 0 ＃ r)
               → (x ·ᵣ r) ≡ q
               → x ≡ q ／ᵣ[ r , 0＃r ]
x·y≡z→x≡z/y x q r 0＃r p =
    sym ([x·y]/yᵣ _ _ _) ∙ cong (_／ᵣ[ r , 0＃r ]) p

x·rat[α]+x·rat[β]=x : ∀ x →
    ∀ {α β : ℚ} → {𝟚.True (ℚ.discreteℚ (α ℚ.+ β) 1)} →
                   (x ·ᵣ rat α) +ᵣ (x ·ᵣ rat β) ≡ x
x·rat[α]+x·rat[β]=x x {α} {β} {p} =
   sym (·DistL+ _ _ _)
    ∙∙ cong (x ·ᵣ_) (decℚ≡ᵣ? {_} {_} {p})
    ∙∙ ·IdR _
