{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)


open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.NatPlusOne
open import Cubical.Foundations.Path
open import Cubical.Foundations.CartesianKanOps


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz



sumR : NonExpanding₂ ℚ._+_
sumR .NonExpanding₂.cL q r s =
 ℚ.≡Weaken≤  (ℚ.abs ((q ℚ.+ s) ℚ.- (r ℚ.+ s))) (ℚ.abs (q ℚ.- r))
  (sym $ cong ℚ.abs (lem--036 {q} {r} {s}))
sumR .NonExpanding₂.cR q r s =
   ℚ.≡Weaken≤ (ℚ.abs ((q ℚ.+ r) ℚ.- (q ℚ.+ s))) (ℚ.abs (r ℚ.- s))
   (sym $ cong ℚ.abs (lem--037 {r} {s} {q}))

infix  8 -ᵣ_
infixl 6 _+ᵣ_ _-ᵣ_


_+ᵣ_ : ℝ → ℝ → ℝ
_+ᵣ_ = NonExpanding₂.go sumR

+ᵣ-∼ : ∀ u v r ε → u ∼[ ε ] v → (u +ᵣ r) ∼[ ε ] (v +ᵣ r)
+ᵣ-∼ u v r =
  NonExpanding₂.go∼L sumR r u v

minR : NonExpanding₂ ℚ.min
minR = w

 where

 w' : (q r s : ℚ) → ℚ.abs (ℚ.min q s ℚ.- ℚ.min r s) ℚ.≤ ℚ.abs (q ℚ.- r)
 w' q r s =
  let s' = ℚ.min r q
  in subst (ℚ._≤ (ℚ.abs (q ℚ.- r)))
     (cong {x = ℚ.min (ℚ.max s' q) s ℚ.-
                   ℚ.min (ℚ.max s' r) s}
           {y = ℚ.min q s ℚ.- ℚ.min r s}
            ℚ.abs
       (cong₂ (λ q' r' → ℚ.min q' s ℚ.-
                   ℚ.min r' s)
                 (ℚ.maxComm s' q ∙∙
                   cong (ℚ.max q) (ℚ.minComm r q)
                  ∙∙ ℚ.maxAbsorbLMin q r )
             ((ℚ.maxComm s' r ∙ ℚ.maxAbsorbLMin r q )
               ))) (ℚ.clampDist s' s r q)


 w : NonExpanding₂ ℚ.min
 w .NonExpanding₂.cL = w'
 w .NonExpanding₂.cR q r s =
   subst2 (λ u v → ℚ.abs (u ℚ.- v) ℚ.≤ ℚ.abs (r ℚ.- s))
        (ℚ.minComm r q) (ℚ.minComm s q) (w' r s q)



maxR : NonExpanding₂ ℚ.max
maxR = w
 where

 h : ∀ q r s →  ℚ.min (ℚ.max s q) (ℚ.max s (ℚ.max r q)) ≡ ℚ.max q s
 h q r s = cong (ℚ.min (ℚ.max s q)) (cong (ℚ.max s) (ℚ.maxComm r q)
             ∙ ℚ.maxAssoc s q r) ∙
      ℚ.minAbsorbLMax (ℚ.max s q) r ∙ ℚ.maxComm s q

 w' : (q r s : ℚ) → ℚ.abs (ℚ.max q s ℚ.- ℚ.max r s) ℚ.≤ ℚ.abs (q ℚ.- r)
 w' q r s =
  let s' = ℚ.max s (ℚ.max r q)
  in subst (ℚ._≤ (ℚ.abs (q ℚ.- r)))
       ( cong {x = ℚ.min (ℚ.max s q) s' ℚ.-
                   ℚ.min (ℚ.max s r) s'}
           {y = ℚ.max q s ℚ.- ℚ.max r s}
            ℚ.abs
            (cong₂ ℚ._-_
              (h q r s)
              (cong (ℚ.min (ℚ.max s r))
                 (cong (ℚ.max s) (ℚ.maxComm r q))
                ∙ h r q s)) )
       (ℚ.clampDist s s' r q )

 w : NonExpanding₂ ℚ.max
 w .NonExpanding₂.cL = w'
 w .NonExpanding₂.cR q r s =
   subst2 (λ u v → ℚ.abs (u ℚ.- v) ℚ.≤ ℚ.abs (r ℚ.- s))
        (ℚ.maxComm r q) (ℚ.maxComm s q)
         (w' r s q)

minᵣ = NonExpanding₂.go minR
maxᵣ = NonExpanding₂.go maxR

_≤ᵣ_ : ℝ → ℝ → Type
u ≤ᵣ v = maxᵣ u v ≡ v

Lipschitz-ℝ→ℝ-1→NonExpanding : ∀ f
  → Lipschitz-ℝ→ℝ 1 f → ⟨ NonExpandingₚ f ⟩
Lipschitz-ℝ→ℝ-1→NonExpanding f x _ _ _ =
  subst∼ (ℚ.·IdL _) ∘S x _ _ _


maxᵣComm : ∀ x y → NonExpanding₂.go maxR x y ≡ NonExpanding₂.go maxR y x
maxᵣComm x y =
  nonExpanding₂Ext ℚ.max (flip ℚ.max)
    maxR (NonExpanding₂-flip ℚ.max maxR) ℚ.maxComm x y ∙
   (NonExpanding₂-flip-go ℚ.max maxR
     (NonExpanding₂-flip ℚ.max maxR) x y )

minᵣComm : ∀ x y → NonExpanding₂.go minR x y ≡ NonExpanding₂.go minR y x
minᵣComm x y =
  nonExpanding₂Ext ℚ.min (flip ℚ.min)
    minR (NonExpanding₂-flip ℚ.min minR) ℚ.minComm x y ∙
   (NonExpanding₂-flip-go ℚ.min minR
     (NonExpanding₂-flip ℚ.min minR) x y )


+ᵣComm : ∀ x y → NonExpanding₂.go sumR x y ≡ NonExpanding₂.go sumR y x
+ᵣComm x y =
  nonExpanding₂Ext ℚ._+_ (flip ℚ._+_)
    sumR (NonExpanding₂-flip ℚ._+_ sumR) ℚ.+Comm x y ∙
   (NonExpanding₂-flip-go ℚ._+_ sumR
     (NonExpanding₂-flip ℚ._+_ sumR) x y )



inj-rat : ∀ q r → rat q ≡ rat r → q ≡ r
inj-rat q r x with (ℚ.discreteℚ q r)
... | yes p = p
... | no ¬p =
  let (zz , zz') = ∼→∼' (rat q) (rat r) _
           $ invEq (∼≃≡ (rat q) (rat r)) x (ℚ.abs (q ℚ.- r) ,
               ℚ.≠→0<abs q r ¬p)
  in ⊥.rec (ℚ.isIrrefl< (ℚ.abs (q ℚ.- r))
        (ℚ.absFrom<×< (ℚ.abs (q ℚ.- r)) (q ℚ.- r)
          zz zz'))

≤ℚ→≤ᵣ : ∀ q r → q ℚ.≤ r → rat q ≤ᵣ rat r
≤ℚ→≤ᵣ q r x = cong rat (ℚ.≤→max q r x)

≤ᵣ→≤ℚ : ∀ q r → rat q ≤ᵣ rat r → q ℚ.≤ r
≤ᵣ→≤ℚ q r x = subst (q ℚ.≤_) (inj-rat _ _ x) (ℚ.≤max q r)


≤ᵣ≃≤ℚ : ∀ q r → (rat q ≤ᵣ rat r) ≃ (q ℚ.≤ r)
≤ᵣ≃≤ℚ q r = propBiimpl→Equiv
 (isSetℝ _ _) (ℚ.isProp≤ _ _)
  (≤ᵣ→≤ℚ q r) (≤ℚ→≤ᵣ q r)



maxᵣIdem : ∀ x → maxᵣ x x ≡ x
maxᵣIdem = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop (λ z → maxᵣ z z ≡ z)
 w .Elimℝ-Prop.ratA = cong rat ∘ ℚ.maxIdem
 w .Elimℝ-Prop.limA x p x₁ =
   snd (NonExpanding₂.β-lim-lim/2 maxR x p x p)
    ∙ eqℝ _ _
       λ ε → lim-lim _ _ _ (/2₊ ε)
                 (/2₊ (/2₊ ε)) _ _
                   (subst ℚ.0<_ (cong₂ ℚ._-_
                            (ℚ.·IdR (fst ε))
                            (cong (fst ε ℚ.·_) ℚ.decℚ? ∙∙
                               ℚ.·DistL+ (fst ε) _ _  ∙∙
                                cong ((fst (/2₊ ε) ℚ.+_))
                                  (ℚ.·Assoc (fst ε) ℚ.[ 1 / 2 ]
                                     ℚ.[ 1 / 2 ])))
                     (snd (ℚ.<→ℚ₊ ((fst ε) ℚ.· (ℚ.[ 3 / 4 ]))
                         (fst ε ℚ.· 1)
                       (ℚ.<-o· _ _ (fst ε)
                         (ℚ.0<ℚ₊ ε) ℚ.decℚ<?))))
                  (invEq (∼≃≡  _ _ ) (x₁ (/2₊ (/2₊ ε))) _)

 w .Elimℝ-Prop.isPropA _ = isSetℝ _ _



≤ᵣ-refl : ∀ x → x ≤ᵣ x
≤ᵣ-refl x = maxᵣIdem x


_Σ<ᵣ_ : ℝ → ℝ → Type
u Σ<ᵣ v = Σ[ (q , r) ∈ (ℚ × ℚ) ] (u ≤ᵣ rat q) × (q ℚ.< r) × (rat r ≤ᵣ v)

infix 4 _≤ᵣ_ _<ᵣ_

_<ᵣ_ : ℝ → ℝ → Type
u <ᵣ v = ∃[ (q , r) ∈ (ℚ × ℚ) ] (u ≤ᵣ rat q) × (q ℚ.< r) × (rat r ≤ᵣ v)


isProp≤ᵣ : ∀ x y → isProp (x ≤ᵣ y)
isProp≤ᵣ _ _ = isSetℝ _ _


<ℚ→<ᵣ : ∀ q r → q ℚ.< r → rat q <ᵣ rat r
<ℚ→<ᵣ x y x<y =
  let y-x : ℚ₊
      y-x = ℚ.<→ℚ₊ x y x<y

      x' = x ℚ.+ fst (/3₊ (y-x))
      y' = x' ℚ.+ fst (/3₊ (y-x))
  in ∣ (x' , y') ,
          ≤ℚ→≤ᵣ x x' (
             subst (ℚ._≤ x') (ℚ.+IdR x)
                   (ℚ.≤-o+ 0 (fst (/3₊ (y-x))) x
                    (ℚ.0≤ℚ₊ (/3₊ (y-x)))) )
        , subst (ℚ._< y') (ℚ.+IdR x')
                   (ℚ.<-o+ 0 (fst (/3₊ (y-x))) x'
                    (ℚ.0<ℚ₊ (/3₊ (y-x))))
        , ≤ℚ→≤ᵣ y' y
            (subst2 (ℚ._≤_) (ℚ.+IdR y')
               (lem--048 {x} {y} {ℚ.[ 1 / 3 ]}
                 ∙∙
                  cong {x = ℚ.[ 1 / 3 ] ℚ.+ ℚ.[ 1 / 3 ] ℚ.+ ℚ.[ 1 / 3 ]}
                    {1} (λ a → x ℚ.+ a ℚ.· (y ℚ.- x))
                   ℚ.decℚ?
                  ∙∙ (cong (x ℚ.+_) (ℚ.·IdL (y ℚ.- x))
                      ∙ lem--05))
              ((ℚ.≤-o+ 0 (fst (/3₊ (y-x))) y'
                    (ℚ.0≤ℚ₊ (/3₊ (y-x))))))  ∣₁

<ᵣ→<ℚ : ∀ q r → rat q <ᵣ rat r → q ℚ.< r
<ᵣ→<ℚ = ElimProp2.go w
 where
 w : ElimProp2 (λ z z₁ → rat z <ᵣ rat z₁ → z ℚ.< z₁)
 w .ElimProp2.isPropB _ _ = isProp→ (ℚ.isProp< _ _)
 w .ElimProp2.f x y =
  PT.rec (ℚ.isProp< _ _)
   λ ((x' , y') , a , b , c) →
     ℚ.isTrans<≤ _//_.[ x ] y' _//_.[ y ]
      (ℚ.isTrans≤< _//_.[ x ] x' y' (≤ᵣ→≤ℚ _ _ a) b)
        (≤ᵣ→≤ℚ _ _ c)

<ᵣ≃<ℚ : ∀ q r → (rat q <ᵣ rat r) ≃ (q ℚ.< r)
<ᵣ≃<ℚ q r = propBiimpl→Equiv
 squash₁ (ℚ.isProp< _ _)
  (<ᵣ→<ℚ q r) (<ℚ→<ᵣ q r)

maxᵣAssoc : ∀ x y z → maxᵣ x (maxᵣ y z) ≡ maxᵣ (maxᵣ x y) z
maxᵣAssoc x y z =
  (fst (∼≃≡ _ _)) (NonExpanding₂-Lemmas.gAssoc∼ _
    maxR maxᵣComm ℚ.maxAssoc x y z)

minᵣAssoc : ∀ x y z → minᵣ x (minᵣ y z) ≡ minᵣ (minᵣ x y) z
minᵣAssoc x y z =
  (fst (∼≃≡ _ _)) (NonExpanding₂-Lemmas.gAssoc∼ _
    minR minᵣComm ℚ.minAssoc x y z)


+ᵣAssoc : ∀ x y z →  x +ᵣ (y +ᵣ z) ≡ (x +ᵣ y) +ᵣ z
+ᵣAssoc x y z =
  (fst (∼≃≡ _ _)) (NonExpanding₂-Lemmas.gAssoc∼ _
    sumR +ᵣComm ℚ.+Assoc x y z)

isTrans≤ᵣ : ∀ x y z → x ≤ᵣ y → y ≤ᵣ z → x ≤ᵣ z
isTrans≤ᵣ x y z u v = ((cong (maxᵣ x) (sym v)
  ∙ maxᵣAssoc x y z) ∙ cong (flip maxᵣ z) u) ∙ v

isTrans<ᵣ : ∀ x y z → x <ᵣ y → y <ᵣ z → x <ᵣ z
isTrans<ᵣ x y z =
 PT.map2 λ ((q , r) , (u , v , w))
           ((q' , r') , (u' , v' , w')) →
            ((q , r')) ,
             (u , ℚ.isTrans< q q' r' (ℚ.isTrans<≤ q r q' v
                      (≤ᵣ→≤ℚ r q' (isTrans≤ᵣ _ _ _ w u')))
                        v' , w')

isTrans≤<ᵣ : ∀ x y z → x ≤ᵣ y → y <ᵣ z → x <ᵣ z
isTrans≤<ᵣ x y z u =
 PT.map $ map-snd λ (v , v' , v'')
   → isTrans≤ᵣ x y _ u v  , v' , v''

isTrans<≤ᵣ : ∀ x y z → x <ᵣ y → y ≤ᵣ z → x <ᵣ z
isTrans<≤ᵣ x y z = flip λ u →
 PT.map $ map-snd λ (v , v' , v'')
   → v  , v' , isTrans≤ᵣ _ y z v'' u

isTrans≤≡ᵣ : ∀ x y z → x ≤ᵣ y → y ≡ z → x ≤ᵣ z
isTrans≤≡ᵣ x y z p q = subst (x ≤ᵣ_) q p

isTrans≡≤ᵣ : ∀ x y z → x ≡ y → y ≤ᵣ z → x ≤ᵣ z
isTrans≡≤ᵣ x y z p q = subst (_≤ᵣ z) (sym p) q

isTrans<≡ᵣ : ∀ x y z → x <ᵣ y → y ≡ z → x <ᵣ z
isTrans<≡ᵣ x y z p q = subst (x <ᵣ_) q p

isTrans≡<ᵣ : ∀ x y z → x ≡ y → y <ᵣ z → x <ᵣ z
isTrans≡<ᵣ x y z p q = subst (_<ᵣ z) (sym p) q


-ᵣR : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (1 , tt))
-ᵣR = fromLipschitz (1 , _)
  ((rat ∘ ℚ.-_ ) , λ q r ε x x₁ →
    subst∼ {ε = ε} (sym $ ℚ.·IdL (fst ε))
     (rat-rat _ _ _ (subst ((ℚ.- fst ε) ℚ.<_)
       (ℚ.-Distr q (ℚ.- r))
       (ℚ.minus-< (q ℚ.- r) (fst ε) x₁)) (
       ℚ.minus-<' (fst ε) ((ℚ.- q) ℚ.- (ℚ.- r))
        (subst ((ℚ.- fst ε) ℚ.<_)
         (sym (ℚ.-[x-y]≡y-x r q) ∙
           cong (ℚ.-_) (ℚ.+Comm r (ℚ.- q) ∙
             cong ((ℚ.- q) ℚ.+_) (sym $ ℚ.-Invol r))) x))))

-ᵣ_ : ℝ → ℝ
-ᵣ_ = fst -ᵣR


_-ᵣ_ : ℝ → ℝ → ℝ
x -ᵣ y = x +ᵣ (-ᵣ y)


open ℚ.HLP

+-ᵣ : ∀ x → x -ᵣ x ≡ 0
+-ᵣ = fst (∼≃≡ _ _) ∘ Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop _ --(λ z → (z +ᵣ (-ᵣ z)) ≡ 0)
 w .Elimℝ-Prop.ratA x = invEq (∼≃≡ _ _) (cong rat (ℚ.+InvR x)) --
 w .Elimℝ-Prop.limA x p x₁ ε =

    lim-rat _ _ _ (/4₊ ε) _ (distℚ0<! ε (ge1 +ge (neg-ge ge[ ℚ.[ 1 / 4 ] ])))
      (subst∼ (distℚ! (fst ε) ·[ ge[ ℚ.[ 1 / 2 ] ] +ge ge[ ℚ.[ 1 / 4 ] ]
             ≡ (ge1 +ge (neg-ge ge[ ℚ.[ 1 / 4 ] ]))  ]) (triangle∼
        (NonExpanding₂.go∼R sumR (x (/4₊ ε)) (-ᵣ lim x p)
         (-ᵣ x (/4₊ ε)) (/2₊ ε) (subst∼ (ℚ.·IdL (fst (/2₊ ε)) ) $
          snd -ᵣR (lim x p) (x (/4₊ ε)) (/2₊ ε)
          (subst∼ (cong fst (ℚ./4₊+/4₊≡/2₊ ε))
           $ sym∼ _ _ _ $ 𝕣-lim-self x p (/4₊ ε) (/4₊ ε))))
        (x₁ ((/4₊ ε)) (/4₊ ε) )))

 w .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → isProp∼ _ _ _



abs-dist : ∀ q r → ℚ.abs (ℚ.abs' q ℚ.- ℚ.abs' r) ℚ.≤ ℚ.abs (q ℚ.- r)
abs-dist =
  ℚ.elimBy≡⊎<'
    (λ x y → subst2 ℚ._≤_ (ℚ.absComm- _ _) (ℚ.absComm- _ _))
    (λ x → ℚ.≡Weaken≤ _ _ (cong ℚ.abs (ℚ.+InvR (ℚ.abs' x) ∙ sym (ℚ.+InvR x))))
    λ x ε → subst (ℚ.abs (ℚ.abs' x ℚ.- ℚ.abs' (x ℚ.+ fst ε)) ℚ.≤_)
      (sym (ℚ.-[x-y]≡y-x x (x ℚ.+ fst ε)) ∙ sym (ℚ.absNeg (x ℚ.- (x ℚ.+ fst ε))
         ((subst {x = ℚ.- (fst ε) } {(x ℚ.- (x ℚ.+ fst ε))}
           (ℚ._< 0) lem--050 (ℚ.-ℚ₊<0 ε)))))

      ((ℚ.absFrom≤×≤ ((x ℚ.+ fst ε) ℚ.- x)
        (ℚ.abs' x ℚ.- ℚ.abs' (x ℚ.+ fst ε))
         (subst2
             {x = (ℚ.abs (fst ε ℚ.+ x)) ℚ.+
                     ((ℚ.- ℚ.abs' (x ℚ.+ fst ε)) ℚ.- fst ε)}
             {y = ℚ.- ((x ℚ.+ fst ε) ℚ.- x)}
            ℚ._≤_ (cong (ℚ._+ ((ℚ.- ℚ.abs' (x ℚ.+ fst ε)) ℚ.- fst ε))
                      (λ i → ℚ.abs'≡abs (ℚ.+Comm (fst ε) x i) i) ∙
                          lem--051 )
                       (λ i → lem--052 {fst ε} {ℚ.abs'≡abs x i}
                               {ℚ.abs' (x ℚ.+ fst ε)} i) $
           ℚ.≤-+o (ℚ.abs (fst ε ℚ.+ x)) (fst ε ℚ.+ ℚ.abs x)
           ((ℚ.- ℚ.abs' (x ℚ.+ fst ε)) ℚ.- fst ε)
             (ℚ.abs+pos (fst ε) x (ℚ.0<ℚ₊ ε)))
         (subst2 {x = ℚ.abs (x ℚ.+ fst ε ℚ.+ (ℚ.- fst ε)) ℚ.+
                     (ℚ.- ℚ.abs' (x ℚ.+ fst ε))}
                  {ℚ.abs' x ℚ.- ℚ.abs' (x ℚ.+ fst ε)}
            ℚ._≤_ (cong ((ℚ._+
                 (ℚ.- ℚ.abs' (x ℚ.+ fst ε))))
                   (congS ℚ.abs (sym (lem--034 {x} {fst ε}))
                     ∙ ℚ.abs'≡abs _))
                  ((λ i → ℚ.abs'≡abs (x ℚ.+ fst ε) i
                   ℚ.+ (ℚ.absNeg (ℚ.- fst ε) (ℚ.-ℚ₊<0 ε) i) ℚ.+
                      (ℚ.- ℚ.abs' (x ℚ.+ fst ε))) ∙
                       lem--053)
           $ ℚ.≤-+o (ℚ.abs (x ℚ.+ fst ε ℚ.+ (ℚ.- fst ε)))
                 (ℚ.abs (x ℚ.+ fst ε) ℚ.+ ℚ.abs (ℚ.- fst ε))
            (ℚ.- ℚ.abs' (x ℚ.+ fst ε))
            (ℚ.abs+≤abs+abs (x ℚ.+ fst ε) (ℚ.- (fst ε))))))



absᵣL : Σ _ _
absᵣL = fromLipschitz 1 (rat ∘ ℚ.abs' , h )
 where
 h : Lipschitz-ℚ→ℝ 1 (λ x → rat (ℚ.abs' x))
 h q r ε x x₁ = subst∼ {ε = ε} (sym (ℚ.·IdL (fst ε)))
    (rat-rat-fromAbs _ _ _ (
      ℚ.isTrans≤< _ _ (fst ε) ((abs-dist q r))
        (ℚ.absFrom<×< (fst ε) (q ℚ.- r) x x₁)))

absᵣ = fst absᵣL

absᵣ-nonExpanding : ⟨ NonExpandingₚ absᵣ ⟩
absᵣ-nonExpanding u v ε x =
  subst∼ (ℚ.·IdL _) $ snd absᵣL u v ε x

lim≤rat→∼ : ∀ x y r → (lim x y ≤ᵣ rat r)
                    ≃ (∀ ε → ∃[ δ ∈ _ ]
                         Σ _ λ v →
                           (maxᵣ (x δ) (rat r))
                              ∼'[ (fst ε ℚ.- fst δ , v) ] (rat r) )
lim≤rat→∼ x y r =
  invEquiv (∼≃≡ _ _ ) ∙ₑ
    equivΠCod λ ε →
      propBiimpl→Equiv (isProp∼ _ _ _) squash₁ (∼→∼' _ _ _) (∼'→∼ _ _ _)


maxᵣ-lem : ∀ u v r ε → u ∼[ ε ] v →
                   (((ε₁ : ℚ₊) →
                      maxᵣ v (rat r) ∼[ ε₁ ] rat r)) →
                      maxᵣ u (rat r) ∼[ ε ] rat r
maxᵣ-lem u v r ε xx x =
   subst (NonExpanding₂.go maxR u (rat r) ∼[ ε ]_)
      (fst (∼≃≡ (NonExpanding₂.go maxR v (rat r)) (rat r)) x )
        (NonExpanding₂.go∼L maxR (rat r) u v ε xx)



ℝ₊ = Σ _ λ r → 0 <ᵣ r


ℚ₊→ℝ₊ : ℚ₊ → ℝ₊
ℚ₊→ℝ₊ (x , y) = rat x , <ℚ→<ᵣ 0 x (ℚ.0<→< x y)

decℚ≡ᵣ? : ∀ {x y} → {𝟚.True (ℚ.discreteℚ x y)} →  (rat x ≡ rat y)
decℚ≡ᵣ? {x} {y} {p} = cong rat (ℚ.decℚ? {x} {y} {p})

decℚ<ᵣ? : ∀ {x y} → {𝟚.True (ℚ.<Dec x y)} →  (rat x <ᵣ rat y)
decℚ<ᵣ? {x} {y} {p} = <ℚ→<ᵣ x y (ℚ.decℚ<? {x} {y} {p})

decℚ≤ᵣ? : ∀ {x y} → {𝟚.True (ℚ.≤Dec x y)} →  (rat x ≤ᵣ rat y)
decℚ≤ᵣ? {x} {y} {p} = ≤ℚ→≤ᵣ x y (ℚ.decℚ≤? {x} {y} {p})

instance
  fromNatℝ₊ : HasFromNat ℝ₊
  fromNatℝ₊ = record {
     Constraint = λ { zero → ⊥ ; _ → Unit }
   ; fromNat = λ { zero {{()}}  ; (suc n) →
     (rat [ pos (suc n) / 1 ]) , <ℚ→<ᵣ _ _
       (ℚ.<ℤ→<ℚ _ _ (ℤ.suc-≤-suc ℤ.zero-≤pos)) }}
