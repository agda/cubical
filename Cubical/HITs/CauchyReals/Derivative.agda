{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)

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
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence




at_limitOf_is_ : (x : ℝ) → (∀ r → x ＃ r → ℝ)  → ℝ → Type
at x limitOf f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r x＃r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r x＃r) <ᵣ fst ε)

at_inclLimitOf_is_ : (x : ℝ) → (∀ r → ℝ)  → ℝ → Type
at x inclLimitOf f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r) <ᵣ fst ε)

inclLimit→Limit : ∀ f x L → at x inclLimitOf f is L
                          → at x limitOf (λ r _ → f r)  is L
inclLimit→Limit f x L = PT.map (map-snd (const ∘_)) ∘_

substLim : ∀ {x f f' L}
  → (∀ r x＃r → f r x＃r ≡ f' r x＃r)
  → at x limitOf f is L → at x limitOf f' is L
substLim {x} {L = L} p =  subst (at x limitOf_is L) (funExt₂ p)

IsContinuousInclLim : ∀ f x → IsContinuous f →
                    at x inclLimitOf f is (f x)
IsContinuousInclLim f x cx = uncurry
  λ ε → (PT.rec squash₁
   λ (q , 0<q , q<ε) →
     PT.map (λ (δ , X) →
       (ℚ₊→ℝ₊ δ) ,
         λ r x₁ → isTrans<ᵣ _ _ _
           (fst (∼≃abs<ε _ _ _) (X r (invEq (∼≃abs<ε _ _ _) x₁)))
            q<ε  )
       (cx x (q , ℚ.<→0< q (<ᵣ→<ℚ 0 q 0<q)))) ∘ denseℚinℝ 0 ε

IsContinuousLim : ∀ f x → IsContinuous f →
                    at x limitOf (λ r _ → f r) is (f x)
IsContinuousLim f x cx = inclLimit→Limit _ _ _ (IsContinuousInclLim f x cx)

IsContinuousInclLim→IsContinuous : ∀ f  →
                    (∀ x → at x inclLimitOf f is (f x))
                    → IsContinuous f
IsContinuousInclLim→IsContinuous f xc x (ε , 0<ε) =
  PT.rec squash₁ w z

 where
  z = xc x (rat ε , <ℚ→<ᵣ 0 ε (ℚ.0<→< _ 0<ε) )
  w : Σ ℝ₊
        (λ δ →
           (r : ℝ) →
           absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (f x -ᵣ f r) <ᵣ rat ε) →
        ∃-syntax ℚ₊ (λ δ → (v₁ : ℝ) → x ∼[ δ ] v₁ → f x ∼[ ε , 0<ε ] f v₁)
  w ((δ , 0<δ) , X) =
      PT.map (λ (q , 0<q , q<δ) →
        ((q , ℚ.<→0< q (<ᵣ→<ℚ 0 q 0<q))) ,
          λ r x∼r → invEq (∼≃abs<ε _ _ _) (X r
            (isTrans<ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) x∼r) q<δ)))
       (denseℚinℝ 0 δ 0<δ)

IsContinuousInclLim≃IsContinuous : ∀ f  →
                    (∀ x → at x inclLimitOf f is (f x))
                    ≃ (IsContinuous f)
IsContinuousInclLim≃IsContinuous f =
  propBiimpl→Equiv (isPropΠ2 λ _ _ → squash₁) (isPropIsContinuous f)
    (IsContinuousInclLim→IsContinuous f)
     λ fc x → IsContinuousInclLim f x fc

IsContinuousLimΔ : ∀ f x → IsContinuous f →
                    at 0 limitOf (λ Δx _ → f (x +ᵣ Δx)) is (f x)
IsContinuousLimΔ f x cx =
  subst (at rat [ pos 0 / 1+ 0 ] limitOf (λ Δx _ → f (x +ᵣ Δx)) is_)
   (cong f (+IdR x))
  (IsContinuousLim (λ Δx → f (x +ᵣ Δx)) 0
    (IsContinuous∘ _ _ cx (IsContinuous+ᵣL x)))



const-lim : ∀ C x → at x limitOf (λ _ _ → C) is C
const-lim C x ε = ∣ (1 , decℚ<ᵣ?) ,
  (λ r x＃r x₁ → subst (_<ᵣ fst ε) (cong absᵣ (sym (+-ᵣ C))) (snd ε)) ∣₁

id-lim : ∀ x → at x limitOf (λ r _ → r) is x
id-lim x ε = ∣ ε , (λ r x＃r p → p )  ∣₁

_$[_]$_ : (ℝ → ℝ)
        → (ℝ → ℝ → ℝ)
        → (ℝ → ℝ)
        → (ℝ → ℝ)
f $[ _op_ ]$ g = λ r → (f r) op (g r)

_#[_]$_ : {x : ℝ}
        → (∀ r → x ＃ r → ℝ)
        → (ℝ → ℝ → ℝ)
        → (∀ r → x ＃ r → ℝ)
        → (∀ r → x ＃ r → ℝ)
f #[ _op_ ]$ g = λ r x → (f r x) op (g r x)

+-lim : ∀ x f g F G
        → at x limitOf f is F
        → at x limitOf g is G
        → at x limitOf (f #[ _+ᵣ_ ]$ g) is (F +ᵣ G)
+-lim x f g F G fL gL ε =
  PT.map2 (λ (δ , p) (δ' , p') →
       (_ , ℝ₊min δ δ') ,
        λ r x＃r x₁ →
         let u = p r x＃r (isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ _ _))
             u' = p' r x＃r (isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ' _ _))
         in subst2 _<ᵣ_
                (cong absᵣ (sym L𝐑.lem--041))
                (x·rat[α]+x·rat[β]=x (fst ε))
               (isTrans≤<ᵣ _ _ _
                 (absᵣ-triangle _ _)
                 (<ᵣMonotone+ᵣ _ _ _ _ u u')))
    (fL (ε ₊·ᵣ (rat [ 1 / 2 ] , decℚ<ᵣ?)))
     (gL (ε ₊·ᵣ (rat [ 1 / 2 ] , decℚ<ᵣ?)))


·-lim : ∀ x f g F G
        → at x limitOf f is F
        → at x limitOf g is G
        → at x limitOf (f #[ _·ᵣ_ ]$ g) is (F ·ᵣ G)
·-lim x f g F G fL gL ε = PT.map3 w (fL (ε'f)) (gL (ε'g)) (gL 1)

 where

 ε'f : ℝ₊
 ε'f = (ε ₊／ᵣ₊ 2) ₊／ᵣ₊ (1 +ᵣ absᵣ G ,
          <≤ᵣMonotone+ᵣ 0 1 0 (absᵣ G) decℚ<ᵣ? (0≤absᵣ G))

 ε'g : ℝ₊
 ε'g = (ε ₊／ᵣ₊ 2) ₊／ᵣ₊ (1 +ᵣ absᵣ F ,
          <≤ᵣMonotone+ᵣ 0 1 0 (absᵣ F) decℚ<ᵣ? (0≤absᵣ F))

 w : _
 w (δ , p) (δ' , p') (δ'' , p'') = δ* , ww

  where

   δ* : ℝ₊
   δ* = minᵣ (minᵣ (fst δ) (fst δ')) (fst δ'') ,
              ℝ₊min ((minᵣ (fst δ) (fst δ')) , (ℝ₊min δ δ')) δ''

   ww : (r : ℝ) (x＃r : x ＃ r) →
          absᵣ (x -ᵣ r) <ᵣ fst δ* →
          absᵣ (F ·ᵣ G -ᵣ (f #[ _·ᵣ_ ]$ g) r x＃r) <ᵣ fst ε
   ww r x＃r x₁ = subst2 _<ᵣ_
        (cong absᵣ (sym L𝐑.lem--065))
        yy
        (isTrans≤<ᵣ _ _ _
          ((absᵣ-triangle _ _) )
          (<ᵣMonotone+ᵣ _ _ _ _
            (isTrans≡<ᵣ _ _ _
              (·absᵣ _ _)
              (<ᵣ₊Monotone·ᵣ _ _ _ _
              (0≤absᵣ _) (0≤absᵣ _) gx< u))
              (isTrans≡<ᵣ _ _ _ (·absᵣ _ _)
                (<ᵣ₊Monotone·ᵣ _ _ _ _
              ((0≤absᵣ F)) (0≤absᵣ _)
               (subst (_<ᵣ (1 +ᵣ (absᵣ F)))
                (+IdL _)
                 (<ᵣ-+o (rat 0) (rat 1) (absᵣ F) decℚ<ᵣ?)) u'))))


     where
      x₁' = isTrans<≤ᵣ _ _ _ x₁
                 (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (min≤ᵣ _ _))
      x₁'' = isTrans<≤ᵣ _ _ _ x₁
                 (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (min≤ᵣ' _ _))
      x₁''' = isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ' _ _)
      u = p r x＃r x₁'
      u' = p' r x＃r x₁''
      u'' = p'' r x＃r x₁'''
      gx< : absᵣ (g r x＃r) <ᵣ 1 +ᵣ absᵣ G
      gx< =
         subst (_<ᵣ (1 +ᵣ absᵣ G))
            (cong absᵣ (sym (L𝐑.lem--035)))

           (isTrans≤<ᵣ _ _ _
             (absᵣ-triangle ((g r x＃r) -ᵣ G) G)
              (<ᵣ-+o _ 1 (absᵣ G)
                (subst (_<ᵣ 1) (minusComm-absᵣ _ _) u'')))
      0<1+g = <≤ᵣMonotone+ᵣ 0 1 0 (absᵣ G) decℚ<ᵣ? (0≤absᵣ G)
      0<1+f = <≤ᵣMonotone+ᵣ 0 1 0 (absᵣ F) decℚ<ᵣ? (0≤absᵣ F)

      yy : _ ≡ _
      yy = (cong₂ _+ᵣ_
          (cong ((1 +ᵣ absᵣ G) ·ᵣ_)
            (cong ((fst (ε ₊／ᵣ₊ 2)) ·ᵣ_)
              (invℝ≡ _ _ _)
             ∙ ·ᵣComm  (fst (ε ₊／ᵣ₊ 2))
            (invℝ (1 +ᵣ absᵣ G)
                (inl 0<1+g))) ∙
            ·ᵣAssoc _ _ _)
          (cong ((1 +ᵣ absᵣ F) ·ᵣ_)
            (cong ((fst (ε ₊／ᵣ₊ 2)) ·ᵣ_)
             (invℝ≡ _ _ _)
             ∙ ·ᵣComm  (fst (ε ₊／ᵣ₊ 2))
            (invℝ (1 +ᵣ absᵣ F)
                (inl 0<1+f))) ∙
             ·ᵣAssoc _ _ _) ∙
          sym (·DistR+ _ _ (fst (ε ₊／ᵣ₊ 2)))
           ∙∙ cong {y = 2} (_·ᵣ (fst (ε ₊／ᵣ₊ 2)))
                           (cong₂ _+ᵣ_
                               (x·invℝ[x] (1 +ᵣ absᵣ G)
                                 (inl 0<1+g))
                               (x·invℝ[x] (1 +ᵣ absᵣ F)
                                 (inl 0<1+f))
                              )
                      ∙∙ ·ᵣComm 2 (fst (ε ₊／ᵣ₊ 2))  ∙
                        [x/y]·yᵣ (fst ε) _ (inl _))

At_limitOf_ : (x : ℝ) → (∀ r → x ＃ r → ℝ) → Type
At x limitOf f = Σ _ (at x limitOf f is_)


differenceAt : (ℝ → ℝ) → ℝ → ∀ h → 0 ＃ h → ℝ
differenceAt f x h 0＃h = (f (x +ᵣ h) -ᵣ f x) ／ᵣ[ h , 0＃h ]


derivativeAt : (ℝ → ℝ) → ℝ → Type
derivativeAt f x = At 0 limitOf (differenceAt f x)

derivativeOf_at_is_ : (ℝ → ℝ) → ℝ → ℝ → Type
derivativeOf f at x is d = at 0 limitOf (differenceAt f x) is d

constDerivative : ∀ C x → derivativeOf (λ _ → C) at x is 0
constDerivative C x =
 subst (at 0 limitOf_is 0)
   (funExt₂ λ r 0＃r → sym (𝐑'.0LeftAnnihilates (invℝ r 0＃r)) ∙
     cong (_·ᵣ (invℝ r 0＃r)) (sym (+-ᵣ _)))
   (const-lim 0 0)

idDerivative : ∀ x → derivativeOf (idfun ℝ) at x is 1
idDerivative x =  subst (at 0 limitOf_is 1)
   (funExt₂ λ r 0＃r → sym (x·invℝ[x] r 0＃r) ∙
    cong (_·ᵣ (invℝ r 0＃r)) (sym (L𝐑.lem--063)))
   (const-lim 1 0)

+Derivative : ∀ x f f'x g g'x
        → derivativeOf f at x is f'x
        → derivativeOf g at x is g'x
        → derivativeOf (f $[ _+ᵣ_ ]$ g) at x is (f'x +ᵣ g'x)
+Derivative x f f'x g g'x F G =
 subst {x = (differenceAt f x) #[ _+ᵣ_ ]$ (differenceAt g x)}
            {y = (differenceAt (f $[ _+ᵣ_ ]$ g) x)}
      (at 0 limitOf_is (f'x +ᵣ g'x))
       (funExt₂ λ h 0＃h →
         sym (·DistR+ _ _ _) ∙
          cong (_·ᵣ (invℝ h 0＃h))
           (sym L𝐑.lem--041)) (+-lim _ _ _ _ _ F G)

C·Derivative : ∀ C x f f'x
        → derivativeOf f at x is f'x
        → derivativeOf ((C ·ᵣ_) ∘S f) at x is (C ·ᵣ f'x)
C·Derivative C x f f'x F =
   subst {x = λ h 0＃h → C ·ᵣ differenceAt f x h 0＃h}
            {y = (differenceAt ((C ·ᵣ_) ∘S f) x)}
      (at 0 limitOf_is (C ·ᵣ f'x))
       (funExt₂ λ h 0＃h →
         ·ᵣAssoc _ _ _ ∙
           cong (_·ᵣ (invℝ h 0＃h)) (·DistL- _ _ _))
       (·-lim _ _ _ _ _ (const-lim C 0) F)

substDer : ∀ {x f' f g} → (∀ r → f r ≡ g r)
     → derivativeOf f at x is f'
     → derivativeOf g at x is f'
substDer = subst (derivativeOf_at _ is _) ∘ funExt

substDer₂ : ∀ {x f' g' f g} →
        (∀ r → f r ≡ g r) → f' ≡ g'
     → derivativeOf f at x is f'
     → derivativeOf g at x is g'
substDer₂ p q = subst2 (derivativeOf_at _ is_) (funExt p) q


C·Derivative' : ∀ C x f f'x
        → derivativeOf f at x is f'x
        → derivativeOf ((_·ᵣ C) ∘S f) at x is (f'x ·ᵣ C)
C·Derivative' C x f f'x F =
  substDer₂ (λ _ → ·ᵣComm _ _) (·ᵣComm _ _)
    (C·Derivative C x f f'x F)

·Derivative : ∀ x f f'x g g'x
        → IsContinuous g
        → derivativeOf f at x is f'x
        → derivativeOf g at x is g'x
        → derivativeOf (f $[ _·ᵣ_ ]$ g) at x is
           (f'x ·ᵣ (g x) +ᵣ (f x) ·ᵣ g'x)
·Derivative x f f'x g g'x gC F G =
  substLim w
    (+-lim _ _ _ _ _
      (·-lim _ _ _ _ _
        F (IsContinuousLimΔ g x gC))
      (·-lim _ _ _ _ _
         (const-lim _ _) G))

 where
 w : (r : ℝ) (x＃r : 0 ＃ r) → _
       ≡ differenceAt (f $[ _·ᵣ_ ]$ g) x r x＃r
 w h 0＃h =
    cong₂ _+ᵣ_ (sym (·ᵣAssoc _ _ _) ∙
       cong ((f (x +ᵣ h) -ᵣ f x) ·ᵣ_) (·ᵣComm _ _)
         ∙ (·ᵣAssoc _ _ _) )
      (·ᵣAssoc _ (g (x +ᵣ h) -ᵣ g x) (invℝ h 0＃h))
      ∙ sym (·DistR+ _ _ _) ∙
       cong (_·ᵣ (invℝ h 0＃h))
         (cong₂ _+ᵣ_ (·DistR+ _ _ _ ∙
            cong (f (x +ᵣ h) ·ᵣ g (x +ᵣ h) +ᵣ_) (-ᵣ· _ _))
           (·DistL+ _ _ _ ∙
             cong (f x ·ᵣ g (x +ᵣ h) +ᵣ_) (·-ᵣ _ _))
           ∙ L𝐑.lem--060)

-- LimEverywhere→LimIncl : ∀ f → (∀ x → at x limitOf (λ x _ → f x) is (f x))
--                            → (∀ x → at x inclLimitOf f is (f x))
-- LimEverywhere→LimIncl = {!!}


-- hasDer→isCont : ∀ f (f' : ℝ → ℝ) →
--   (∀ x → derivativeOf f at x is f' x )
--   → IsContinuous f
-- hasDer→isCont f f' df ε = {!df!}

derivative-^ⁿ : ∀ n x →
   derivativeOf (_^ⁿ (suc n)) at x
            is (fromNat (suc n) ·ᵣ (x ^ⁿ n))
derivative-^ⁿ zero x =
 substDer₂
   (λ _ → sym (·IdL _))
   (sym (·IdL _))
   (idDerivative x)
derivative-^ⁿ (suc n) x =
  substDer₂ (λ _ → refl)
    (+ᵣComm _ _ ∙ cong₂ _+ᵣ_
       (·ᵣComm _ _) (sym (·ᵣAssoc _ _ _)) ∙
       sym (·DistR+ _ _ _) ∙
        cong (_·ᵣ ((x ^ⁿ n) ·ᵣ idfun ℝ x))
         (cong rat (ℚ.ℕ+→ℚ+ _ _)))
    (·Derivative _ _ _ _ _ IsContinuousId
       (derivative-^ⁿ n x) (idDerivative x))

-- -- -- chainRule : ∀ x f f'gx g g'x
-- -- --         → derivativeOf g at x is g'x
-- -- --          → derivativeOf f at (g x) is f'gx
-- -- --         → derivativeOf (f ∘ g) at x is (f'gx ·ᵣ g'x)
-- -- -- chainRule = {!!}
