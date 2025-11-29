module Cubical.HITs.CauchyReals.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)


open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.NatPlusOne
open import Cubical.Foundations.Path
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Relation.Binary

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz

open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Proset

open import Cubical.Tactics.CommRingSolver.FastRationalsReflection
open import Cubical.Tactics.CommRingSolver.IntReflection


infix  8 -ᵣ_
infixl 6 _+ᵣ_ _-ᵣ_


opaque

 sumR : NonExpanding₂ ℚ._+_
 sumR .NonExpanding₂.cL q r s =
  ℚ.≡Weaken≤  (ℚ.abs ((q ℚ.+ s) ℚ.- (r ℚ.+ s))) (ℚ.abs (q ℚ.- r))
   (sym $ cong {x = q ℚ.- r} {y = (q ℚ.+ s) ℚ.- (r ℚ.+ s)} ℚ.abs ℚ!)
 sumR .NonExpanding₂.cR q r s =
    ℚ.≡Weaken≤ (ℚ.abs ((q ℚ.+ r) ℚ.- (q ℚ.+ s))) (ℚ.abs (r ℚ.- s))
    (sym $ cong {x = r ℚ.- s} {y = (q ℚ.+ r) ℚ.- (q ℚ.+ s)} ℚ.abs ℚ!)


 _+ᵣ_ : ℝ → ℝ → ℝ
 _+ᵣ_ = NonExpanding₂.go sumR

 +ᵣ-∼ : ∀ u v r ε → u ∼[ ε ] v → (u +ᵣ r) ∼[ ε ] (v +ᵣ r)
 +ᵣ-∼ u v r =
   NonExpanding₂.go∼L sumR r u v

 +ᵣ-∼' : ∀ u v r ε → u ∼[ ε ] v → (r +ᵣ u) ∼[ ε ] (r +ᵣ v)
 +ᵣ-∼' u v r =
   NonExpanding₂.go∼R sumR r u v

 +ᵣ-rat : ∀ p q → rat p +ᵣ rat q ≡ rat (p ℚ.+ q)
 +ᵣ-rat p q = refl


 +ᵣComm : ∀ x y → x +ᵣ y ≡ y +ᵣ x
 +ᵣComm x y =
   nonExpanding₂Ext ℚ._+_ (flip ℚ._+_)
     sumR (NonExpanding₂-flip ℚ._+_ sumR) ℚ.+Comm x y ∙
    (NonExpanding₂-flip-go ℚ._+_ sumR
      (NonExpanding₂-flip ℚ._+_ sumR) x y )



 +ᵣAssoc : ∀ x y z →  x +ᵣ (y +ᵣ z) ≡ (x +ᵣ y) +ᵣ z
 +ᵣAssoc x y z =
   (fst (∼≃≡ _ _)) (NonExpanding₂-Lemmas.gAssoc∼ _
     sumR +ᵣComm ℚ.+Assoc x y z)



 +ᵣ-impl : ∀ x y → x +ᵣ y ≡ NonExpanding₂.go sumR x y
 +ᵣ-impl _ _ = refl

 rat-+ᵣ-lim : ∀ r x y → rat r +ᵣ lim x y ≡ lim (λ ε → rat r +ᵣ x ε)
               λ δ ε → +ᵣ-∼' (x δ) (x ε) (rat r) (δ ℚ₊+ ε) (y δ ε)
 rat-+ᵣ-lim r x y = NonExpanding₂.β-rat-lim sumR r x y λ δ ε → +ᵣ-∼' (x δ) (x ε) (rat r) (δ ℚ₊+ ε) (y δ ε)

 lim-+ᵣ-rat : ∀ x y r → lim x y +ᵣ rat r ≡ lim (λ ε → x ε +ᵣ rat r )
               λ δ ε → +ᵣ-∼  (x δ) (x ε) (rat r) (δ ℚ₊+ ε) (y δ ε)
 lim-+ᵣ-rat x y r = +ᵣComm (lim x y) (rat r) ∙ rat-+ᵣ-lim r x y  ∙
   congLim _ _ _  _ λ q → +ᵣComm (rat r) (x q)

 +∼ : ∀ (x : ℚ₊ → ℝ) (y : (δ ε : ℚ₊) → x δ ∼[ δ ℚ₊+ ε ] x ε)
    (x' : ℚ₊ → ℝ) (y' : (δ ε : ℚ₊) → x' δ ∼[ δ ℚ₊+ ε ] x' ε)
     δ ε → (x (/2₊ δ) +ᵣ x' (/2₊ δ)) ∼[ δ ℚ₊+ ε ] (x (/2₊ ε) +ᵣ x' (/2₊ ε))
 +∼ x y x' y' = fst  (NonExpanding₂.β-lim-lim/2 sumR x y x' y')

 lim-+ᵣ-lim : ∀ x (y : (δ ε : ℚ₊) → x δ ∼[ δ ℚ₊+ ε ] x ε) x' y' → lim x y +ᵣ lim x' y' ≡ lim (λ ε → x (/2₊ ε) +ᵣ x' (/2₊ ε))
                (+∼ x y x' y')
 lim-+ᵣ-lim x y x' y' = snd (NonExpanding₂.β-lim-lim/2 sumR x y x' y')



opaque


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

 minᵣ : ℝ → ℝ → ℝ
 minᵣ = NonExpanding₂.go minR

 maxᵣ : ℝ → ℝ → ℝ
 maxᵣ = NonExpanding₂.go maxR

 maxᵣ-impl : ∀ x y → maxᵣ x y ≡ NonExpanding₂.go maxR x y
 maxᵣ-impl _ _ = refl

 minᵣ-rat : ∀ a b → minᵣ (rat a) (rat b) ≡ rat (ℚ.min a b)
 minᵣ-rat _ _ = refl

 maxᵣ-rat : ∀ a b → maxᵣ (rat a) (rat b) ≡ rat (ℚ.max a b)
 maxᵣ-rat _ _ = refl



 maxᵣComm : ∀ x y → maxᵣ x y ≡ maxᵣ y x
 maxᵣComm x y =
   nonExpanding₂Ext ℚ.max (flip ℚ.max)
     maxR (NonExpanding₂-flip ℚ.max maxR) ℚ.maxComm x y ∙
    (NonExpanding₂-flip-go ℚ.max maxR
      (NonExpanding₂-flip ℚ.max maxR) x y )

 minᵣComm : ∀ x y → minᵣ x y ≡ minᵣ y x
 minᵣComm x y =
   nonExpanding₂Ext ℚ.min (flip ℚ.min)
     minR (NonExpanding₂-flip ℚ.min minR) ℚ.minComm x y ∙
    (NonExpanding₂-flip-go ℚ.min minR
      (NonExpanding₂-flip ℚ.min minR) x y )


clampᵣ : ℝ → ℝ → ℝ → ℝ
clampᵣ d u x = minᵣ (maxᵣ d x) u

opaque
 unfolding maxᵣ minᵣ
 clampᵣ-rat : ∀ a b x → clampᵣ (rat a) (rat b) (rat x) ≡ rat (ℚ.clamp a b x)
 clampᵣ-rat a b x = refl

Lipschitz-ℝ→ℝ-1→NonExpanding : ∀ f
  → Lipschitz-ℝ→ℝ 1 f → ⟨ NonExpandingₚ f ⟩
Lipschitz-ℝ→ℝ-1→NonExpanding f x _ _ _ =
  subst∼ (ℚ.·IdL _) ∘S x _ _ _


opaque
 unfolding maxᵣ minᵣ
 clamp-limΣ : ∀ d u x y →
          Σ _ (λ y' →
           clampᵣ d u (lim x y) ≡ lim (λ ε → clampᵣ d u (x ε)) y')
 clamp-limΣ d u x y = _ , cong (flip minᵣ u) (maxᵣComm d (lim x y))
   ∙ congLim' _ (λ δ ε →
                   Elimℝ.go∼ (NonExpanding₂-Lemmas.NE.w ℚ.min minR)
                   (Elimℝ.go∼ (NonExpanding₂-Lemmas.NE.w ℚ.max maxR) (y δ ε) d) u) _ λ _ → cong (flip minᵣ u) (maxᵣComm (x _) d)


clamp-lim : ∀ d u x y →

           clampᵣ d u (lim x y) ≡ lim (λ ε → clampᵣ d u (x ε)) _
clamp-lim d u x y = snd (clamp-limΣ d u x y)

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


opaque
 unfolding maxᵣ minᵣ
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

infix 4 _≤ᵣ_ _<ᵣ_

open ℚ.HLP

opaque
 unfolding maxᵣ minᵣ
 _≤ᵣ_ : ℝ → ℝ → Type
 u ≤ᵣ v = maxᵣ u v ≡ v

 ≤ᵣ→≡ : ∀ {u v} → u ≤ᵣ v → maxᵣ u v ≡ v
 ≤ᵣ→≡ p = p

 ≡→≤ᵣ : ∀ {u v} → maxᵣ u v ≡ v → u ≤ᵣ v
 ≡→≤ᵣ p = p

 ≤ℚ→≤ᵣ : ∀ q r → q ℚ.≤ r → rat q ≤ᵣ rat r
 ≤ℚ→≤ᵣ q r x = cong rat (ℚ.≤→max q r x)

 ≤ᵣ→≤ℚ : ∀ q r → rat q ≤ᵣ rat r → q ℚ.≤ r
 ≤ᵣ→≤ℚ q r x = subst (q ℚ.≤_) (inj-rat _ _ x) (ℚ.≤max q r)


 ≤ᵣ≃≤ℚ : ∀ q r → (rat q ≤ᵣ rat r) ≃ (q ℚ.≤ r)
 ≤ᵣ≃≤ℚ q r = propBiimpl→Equiv
  (isSetℝ _ _) (ℚ.isProp≤ _ _)
   (≤ᵣ→≤ℚ q r) (≤ℚ→≤ᵣ q r)


 ≤ᵣ-refl : ∀ x → x ≤ᵣ x
 ≤ᵣ-refl x = maxᵣIdem x


 _Σ<ᵣ_ : ℝ → ℝ → Type
 u Σ<ᵣ v = Σ[ (q , r) ∈ (ℚ × ℚ) ] (u ≤ᵣ rat q) × (q ℚ.< r) × (rat r ≤ᵣ v)


 _<ᵣ_ : ℝ → ℝ → Type
 u <ᵣ v = ∃[ (q , r) ∈ (ℚ × ℚ) ] (u ≤ᵣ rat q) × (q ℚ.< r) × (rat r ≤ᵣ v)

 <ᵣ-impl : ∀ u v → (u <ᵣ v) ≃ (∃[ (q , r) ∈ (ℚ × ℚ) ] (u ≤ᵣ rat q) × (q ℚ.< r) × (rat r ≤ᵣ v))
 <ᵣ-impl _ _ = idEquiv _

 isProp≤ᵣ : ∀ x y → isProp (x ≤ᵣ y)
 isProp≤ᵣ _ _ = isSetℝ _ _

 isProp<ᵣ : ∀ x y → isProp (x <ᵣ y)
 isProp<ᵣ _ _ = squash₁


 <ℚ→<ᵣ : ∀ q r → q ℚ.< r → rat q <ᵣ rat r
 <ℚ→<ᵣ x y x<y =
   let y-x : ℚ₊
       y-x = ℚ.<→ℚ₊ x y x<y

       x' = x ℚ.+ fst (/3₊ (y-x))
       y' = x' ℚ.+ fst (/3₊ (y-x))
   in ∣ (x' , y') ,
       (let p : ∀ x y → ((x ℚ.+ ((y ℚ.- x) ℚ.· [ 1 / 3 ]))
                   ℚ.+ ((y ℚ.- x) ℚ.· [ 1 / 3 ])) ℚ.+ ((y ℚ.- x) ℚ.· [ 1 / 3 ]) ≡ y
            p = ℚ.eqElim₂ _ (ℚ.eqℚ ℤ!)
        in (≤ℚ→≤ᵣ x x' (
                 subst (ℚ._≤ x') (ℚ.+IdR x)
                       (ℚ.≤-o+ 0 (fst (/3₊ (y-x))) x
                        (ℚ.0≤ℚ₊ (/3₊ (y-x)))) )
            , subst (ℚ._< y') (ℚ.+IdR x')
                       (ℚ.<-o+ 0 (fst (/3₊ (y-x))) x'
                        (ℚ.0<ℚ₊ (/3₊ (y-x))))
            , ≤ℚ→≤ᵣ y' y
                (subst2 {x = y' ℚ.+ 0} {y = y'} (ℚ._≤_) (ℚ.+IdR y')
                    (p x y)
                  ((ℚ.≤-o+ 0 (fst (/3₊ (y-x))) y'
                        (ℚ.0≤ℚ₊ (/3₊ (y-x))))))))  ∣₁

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

 isTrans≤ᵣ : ∀ x y z → x ≤ᵣ y → y ≤ᵣ z → x ≤ᵣ z
 isTrans≤ᵣ x y z u v = ((cong (maxᵣ x) (sym v)
   ∙ maxᵣAssoc x y z) ∙ cong (flip maxᵣ z) u) ∙ v


 isTrans<ᵣ : ∀ x y z → x <ᵣ y → y <ᵣ z → x <ᵣ z
 isTrans<ᵣ x y z =
  PT.map2 λ ((q , r) , (u , v , w))
            ((q' , r') , (u' , v' , w')) →
             ((q , r')) ,
              (u , ℚ.isTrans< q q' r' (ℚ.isTrans<≤ q r q' v
                       (≤ᵣ→≤ℚ r q' (isTrans≤ᵣ (rat r) _ _ w u')))
                         v' , w')


 isTrans≤<ᵣ : ∀ x y z → x ≤ᵣ y → y <ᵣ z → x <ᵣ z
 isTrans≤<ᵣ x y z u =
  PT.map $ map-snd λ (v , v' , v'')
    → isTrans≤ᵣ x y _ u v  , v' , v''

 isTrans<≤ᵣ : ∀ x y z → x <ᵣ y → y ≤ᵣ z → x <ᵣ z
 isTrans<≤ᵣ x y z = flip λ u →
  PT.map $ map-snd λ {a} (v , v' , v'')
    → v  , v' , isTrans≤ᵣ (rat (a .snd)) y z v'' u

 isTrans≤≡ᵣ : ∀ x y z → x ≤ᵣ y → y ≡ z → x ≤ᵣ z
 isTrans≤≡ᵣ x y z p q = subst (x ≤ᵣ_) q p

 isTrans≡≤ᵣ : ∀ x y z → x ≡ y → y ≤ᵣ z → x ≤ᵣ z
 isTrans≡≤ᵣ x y z p q = subst (_≤ᵣ z) (sym p) q

 isTrans<≡ᵣ : ∀ x y z → x <ᵣ y → y ≡ z → x <ᵣ z
 isTrans<≡ᵣ x y z p q = subst (x <ᵣ_) q p

 isTrans≡<ᵣ : ∀ x y z → x ≡ y → y <ᵣ z → x <ᵣ z
 isTrans≡<ᵣ x y z p q = subst (_<ᵣ z) (sym p) q

 <ᵣWeaken≤ᵣ : ∀ m n → m <ᵣ n → m ≤ᵣ n
 <ᵣWeaken≤ᵣ m n = PT.rec (isSetℝ _ _)
  λ ((q , q') , x , x' , x'')
    → isTrans≤ᵣ m _ _ x (isTrans≤ᵣ (rat q) _ _ (≤ℚ→≤ᵣ q q' (ℚ.<Weaken≤ q q' x')) x'')

 ≡ᵣWeaken≤ᵣ : ∀ m n → m ≡ n → m ≤ᵣ n
 ≡ᵣWeaken≤ᵣ m n p = cong (flip maxᵣ n) p ∙ ≤ᵣ-refl n


 isAsym<ᵣ : BinaryRelation.isAsym _<ᵣ_
 isAsym<ᵣ x y =
   PT.rec2 (isProp⊥)
    λ ((q , q') , x , x' , x'')
       ((r , r') , y , y' , y'') →
        let q<r = ℚ.isTrans<≤ _ _ _ x' (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ (rat q') _ _ x'' y))
            r<q = ℚ.isTrans<≤ _ _ _ y' (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ (rat r') _ _ y'' x))
        in ℚ.isAsym< _ _ q<r r<q

 isAntisym≤ᵣ : BinaryRelation.isAntisym _≤ᵣ_
 isAntisym≤ᵣ a b a≤b b≤a = sym b≤a ∙∙ maxᵣComm b a ∙∙ a≤b

 ℚ-isLip : Lipschitz-ℚ→ℝ ([ pos 1 / 1+ 0 ] , tt) (λ x → rat (ℚ.- x))
 ℚ-isLip q r ε x x₁ =
     subst∼ {ε = ε} (sym $ ℚ.·IdL (fst ε))
      (rat-rat _ _ _ (subst ((ℚ.- fst ε) ℚ.<_)
        (ℚ.-Distr q (ℚ.- r))
        (ℚ.minus-< (q ℚ.- r) (fst ε) x₁)) (
        ℚ.minus-<' (fst ε) ((ℚ.- q) ℚ.- (ℚ.- r))
         (subst ((ℚ.- fst ε) ℚ.<_)
          (sym (ℚ.-[x-y]≡y-x r q) ∙
            cong (ℚ.-_) (ℚ.+Comm r (ℚ.- q) ∙
              cong ((ℚ.- q) ℚ.+_) (sym $ ℚ.-Invol r))) x)))

 -ᵣR : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (1 , tt))
 -ᵣR = fromLipschitz (1 , _)
   ((rat ∘ ℚ.-_ ) , ℚ-isLip)

 -ᵣ_ : ℝ → ℝ
 -ᵣ_ = fst -ᵣR

 -ᵣ-rat : ∀ q → -ᵣ (rat q) ≡ rat (ℚ.- q)
 -ᵣ-rat q = refl

 -ᵣ-impl : ∀ x → -ᵣ x ≡ fst (fromLipschitz (1 , _) ((rat ∘ ℚ.-_ ) , ℚ-isLip)) x
 -ᵣ-impl x = refl

 -ᵣ-lip : Lipschitz-ℝ→ℝ 1 -ᵣ_
 -ᵣ-lip = snd -ᵣR


 -ᵣ-lim : ∀ x p p' → -ᵣ (lim x p) ≡ lim (λ ε → -ᵣ (x ε)) p'
 -ᵣ-lim x p p' = cong (uncurry lim)
   (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isProp∼ _ _ _)
    (congS ((-ᵣ_ ∘S x) ∘S_) (funExt λ y → ℚ₊≡ (ℚ.·IdL _))))

 -ᵣ-nonExpanding : ⟨ NonExpandingₚ -ᵣ_ ⟩
 -ᵣ-nonExpanding u v ε x =
   subst∼ (ℚ.·IdL _) $ -ᵣ-lip u v ε x


 -ᵣ-lim' : ∀ x p → -ᵣ (lim x p) ≡ lim (λ ε → -ᵣ (x ε))
   λ δ ε → -ᵣ-nonExpanding  _ _ _ (p δ ε)
 -ᵣ-lim' x p  = cong (uncurry lim)
   (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isProp∼ _ _ _)
    (congS ((-ᵣ_ ∘S x) ∘S_) (funExt λ y → ℚ₊≡ (ℚ.·IdL _))))


_-ᵣ_ : ℝ → ℝ → ℝ
x -ᵣ y = x +ᵣ (-ᵣ y)

x-ᵣy≡x+ᵣ[-ᵣy] : ∀ x y → x -ᵣ y ≡ x +ᵣ -ᵣ y
x-ᵣy≡x+ᵣ[-ᵣy] x y = refl


-ᵣ-rat₂ : ∀ u q → (rat u) -ᵣ (rat q) ≡ rat (u ℚ.- q)
-ᵣ-rat₂ u q = cong (rat u +ᵣ_) (-ᵣ-rat q) ∙ +ᵣ-rat _ _


opaque
 unfolding -ᵣ_ _+ᵣ_
 +-ᵣ : ∀ x → x -ᵣ x ≡ 0
 +-ᵣ = fst (∼≃≡ _ _) ∘ Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop λ z → (ε : ℚ₊) → (z -ᵣ z) ∼[ ε ] 0 --(λ z → (z +ᵣ (-ᵣ z)) ≡ 0)
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
     (λ x y → subst2 ℚ._≤_ (ℚ.absComm- (ℚ.abs' x) (ℚ.abs' y)) (ℚ.absComm- x y))
     (λ x → ℚ.≡Weaken≤ _ _ (cong ℚ.abs (ℚ.+InvR (ℚ.abs' x) ∙ sym (ℚ.+InvR x))))
     λ x ε → subst (ℚ.abs (ℚ.abs' x ℚ.- ℚ.abs' (x ℚ.+ fst ε)) ℚ.≤_)
       (sym (ℚ.-[x-y]≡y-x x (x ℚ.+ fst ε)) ∙ sym (ℚ.absNeg (x ℚ.- (x ℚ.+ fst ε))
          ((subst {x = ℚ.- (fst ε) } {(x ℚ.- (x ℚ.+ fst ε))}
            (ℚ._< 0) ℚ! (ℚ.-ℚ₊<0 ε)))))

       ((ℚ.absFrom≤×≤ ((x ℚ.+ fst ε) ℚ.- x)
         (ℚ.abs' x ℚ.- ℚ.abs' (x ℚ.+ fst ε))
          (subst2
              {x = (ℚ.abs (fst ε ℚ.+ x)) ℚ.+
                      ((ℚ.- ℚ.abs' (x ℚ.+ fst ε)) ℚ.- fst ε)}
              {y = ℚ.- ((x ℚ.+ fst ε) ℚ.- x)}
             ℚ._≤_ (cong {x = ℚ.abs'≡abs (ℚ.+Comm (fst ε) x i0) i0} {y = ℚ.abs'≡abs (ℚ.+Comm (fst ε) x i1) i1}
                  (ℚ._+ ((ℚ.- ℚ.abs' (x ℚ.+ fst ε)) ℚ.- fst ε))
                       (λ i → ℚ.abs'≡abs (ℚ.+Comm (fst ε) x i) i) ∙
                           ℚ!)
                            (ℚ! ∙
                             cong₂ {x = ℚ.abs x} {y = ℚ.abs' x} ℚ._-_ (ℚ.abs'≡abs x)
                              {u = ℚ.abs' (x ℚ.+ fst ε)} refl)
                                $
            ℚ.≤-+o (ℚ.abs (fst ε ℚ.+ x)) (fst ε ℚ.+ ℚ.abs x)
            ((ℚ.- ℚ.abs' (x ℚ.+ fst ε)) ℚ.- fst ε)
              (ℚ.abs+pos (fst ε) x (ℚ.0<ℚ₊ ε)))
          (subst2 {x = ℚ.abs (x ℚ.+ fst ε ℚ.+ (ℚ.- fst ε)) ℚ.+
                      (ℚ.- ℚ.abs' (x ℚ.+ fst ε))}
                   {ℚ.abs' x ℚ.- ℚ.abs' (x ℚ.+ fst ε)}
             ℚ._≤_ (cong ((ℚ._+
                  (ℚ.- ℚ.abs' (x ℚ.+ fst ε))))
                    (congS {x = x ℚ.+ fst ε ℚ.+ ℚ.- fst ε} {y = x}
                     ℚ.abs (ℚ!)
                      ∙ ℚ.abs'≡abs x))
                   ((λ i → ℚ.abs'≡abs (x ℚ.+ fst ε) i
                    ℚ.+ (ℚ.absNeg (ℚ.- fst ε) (ℚ.-ℚ₊<0 ε) i) ℚ.+
                       (ℚ.- ℚ.abs' (x ℚ.+ fst ε))) ∙
                        ℚ!)
            $ ℚ.≤-+o (ℚ.abs (x ℚ.+ fst ε ℚ.+ (ℚ.- fst ε)))
                  (ℚ.abs (x ℚ.+ fst ε) ℚ.+ ℚ.abs (ℚ.- fst ε))
             (ℚ.- ℚ.abs' (x ℚ.+ fst ε))
             (ℚ.abs+≤abs+abs (x ℚ.+ fst ε) (ℚ.- (fst ε))))))



 absᵣL : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ 1)
 absᵣL = fromLipschitz 1 (rat ∘ ℚ.abs' , h )
  where
  h : Lipschitz-ℚ→ℝ 1 (λ x → rat (ℚ.abs' x))
  h q r ε x x₁ = subst∼ {ε = ε} (sym (ℚ.·IdL (fst ε)))
     (rat-rat-fromAbs _ _ _ (
       ℚ.isTrans≤< _ _ (fst ε) ((abs-dist q r))
         (ℚ.absFrom<×< (fst ε) (q ℚ.- r) x x₁)))

 absᵣ : ℝ → ℝ
 absᵣ = fst absᵣL

 absᵣ0 : absᵣ 0 ≡ 0
 absᵣ0 = refl


 absᵣ-lip : Lipschitz-ℝ→ℝ 1 absᵣ
 absᵣ-lip = snd absᵣL

 absᵣ-rat' : ∀ q → absᵣ (rat q) ≡ rat (ℚ.abs' q)
 absᵣ-rat' q = refl

 absᵣ-rat : ∀ q → absᵣ (rat q) ≡ rat (ℚ.abs q)
 absᵣ-rat q = cong rat (sym (ℚ.abs'≡abs q))

 absᵣ-lim : ∀ x p p' → absᵣ (lim x p) ≡ lim (λ ε → absᵣ (x ε)) p'
 absᵣ-lim x p p' = cong (uncurry lim)
   (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isProp∼ _ _ _)
    (congS ((absᵣ ∘S x) ∘S_) (funExt λ y → ℚ₊≡ (ℚ.·IdL _))))

 absᵣ-nonExpanding : ⟨ NonExpandingₚ absᵣ ⟩
 absᵣ-nonExpanding u v ε x =
   subst∼ (ℚ.·IdL _) $ snd absᵣL u v ε x


 absᵣ-lim' : ∀ x p → absᵣ (lim x p) ≡ lim (λ ε → absᵣ (x ε))
   λ δ ε → absᵣ-nonExpanding  _ _ _ (p δ ε)
 absᵣ-lim' x p  = cong (uncurry lim)
   (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isProp∼ _ _ _)
    (congS ((absᵣ ∘S x) ∘S_) (funExt λ y → ℚ₊≡ (ℚ.·IdL _))))



 lim≤rat→∼ : ∀ x y r → (lim x y ≤ᵣ rat r)
                     ≃ (∀ (ε : ℚ₊) → ∃[ δ ∈ _ ]
                          Σ _ λ v →
                            (maxᵣ (x δ) (rat r))
                               ∼'[ (fst ε ℚ.- fst δ , v) ] (rat r) )
 lim≤rat→∼ x y r =
   invEquiv (∼≃≡ (maxᵣ (lim x y) (rat r)) (rat r) ) ∙ₑ
     equivΠCod λ ε →
       propBiimpl→Equiv (isProp∼ _ _ _) squash₁
        (∼→∼' (maxᵣ (lim x y) (rat r)) (rat r) ε)
        (∼'→∼ (maxᵣ (lim x y) (rat r)) (rat r) ε)




 maxᵣ-lem : ∀ u v r ε → u ∼[ ε ] v →
                    (((ε₁ : ℚ₊) →
                       maxᵣ v (rat r) ∼[ ε₁ ] rat r)) →
                       maxᵣ u (rat r) ∼[ ε ] rat r
 maxᵣ-lem u v r ε xx x =
    subst (NonExpanding₂.go maxR u (rat r) ∼[ ε ]_)
       (fst (∼≃≡ (NonExpanding₂.go maxR v (rat r)) (rat r)) x )
         (NonExpanding₂.go∼L maxR (rat r) u v ε xx)


 -ᵣInvol : ∀ x → -ᵣ (-ᵣ x) ≡ x
 -ᵣInvol = Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop λ x → -ᵣ (-ᵣ x) ≡ x
  w .Elimℝ-Prop.ratA x = cong rat (ℚ.-Invol x)
  w .Elimℝ-Prop.limA x p x₁ =
    congLim _ _ _ _
      λ q → x₁ _ ∙ cong x (ℚ₊≡ (λ i → ℚ.·IdL (ℚ.·IdL (fst q) i) i))
  w .Elimℝ-Prop.isPropA x = isSetℝ (-ᵣ (-ᵣ x)) x



 -absᵣ : ∀ x → absᵣ x ≡ absᵣ (-ᵣ x)
 -absᵣ = Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop λ x → absᵣ x ≡ absᵣ (-ᵣ x)
  w .Elimℝ-Prop.ratA x = cong rat (ℚ.-abs' x)
  w .Elimℝ-Prop.limA x p x₁ =
   let yy = _
   in congLim  (λ v₁ →
                   Elimℝ.go
                   yy
                   (x (ℚ.invℚ₊ 1 ℚ₊· v₁))) _
                   (λ x₂ → Elimℝ.go yy
                             (Elimℝ.go
                              _
                              (x (1 ℚ₊· (1 ℚ₊· x₂))))) _
       λ q → _∙_ {y = Elimℝ.go yy (x (1 ℚ₊· (1 ℚ₊· q)))}
        (cong (Elimℝ.go yy ∘ x) ((ℚ₊≡ (sym (ℚ.·IdL _)))) ) (x₁ _)

  w .Elimℝ-Prop.isPropA x = isSetℝ (absᵣ x) (absᵣ (-ᵣ x))


-ᵣDistr : ∀ x y → -ᵣ (x +ᵣ y) ≡ (-ᵣ x) +ᵣ (-ᵣ y)
-ᵣDistr = Elimℝ-Prop2Sym.go w
 where
 w : Elimℝ-Prop2Sym (λ z z₁ → (-ᵣ (z +ᵣ z₁)) ≡ ((-ᵣ z) +ᵣ (-ᵣ z₁)))
 w .Elimℝ-Prop2Sym.rat-ratA r q = (cong -ᵣ_ (+ᵣ-rat _ _) ∙ -ᵣ-rat _) ∙ cong rat (ℚ.-Distr r q) ∙
   sym (+ᵣ-rat _ _) ∙
    cong₂ _+ᵣ_ (sym (-ᵣ-rat _)) (sym (-ᵣ-rat _))
 w .Elimℝ-Prop2Sym.rat-limA r x y x₁ =
   cong (-ᵣ_) (rat-+ᵣ-lim _ _ _)
    ∙  -ᵣ-lim' _ _
    ∙  (congLim _ _ _ _  λ q → x₁ q ∙ cong (_-ᵣ x q) (-ᵣ-rat r))
     ∙ sym (rat-+ᵣ-lim _ _ _) ∙ cong₂ _+ᵣ_ (sym (-ᵣ-rat r)) (sym (-ᵣ-lim' _ _) )

 w .Elimℝ-Prop2Sym.lim-limA x y x' y' x₁ =
   cong -ᵣ_ (lim-+ᵣ-lim x y x' y')
     ∙ (-ᵣ-lim' _ _ ∙
      congLim _ _ _ _ (λ q → x₁ (/2₊ q) (/2₊ q))
       ∙ sym (lim-+ᵣ-lim  _ _ _ _))
     ∙ cong₂ _+ᵣ_ (sym (-ᵣ-lim' _ _)) (sym (-ᵣ-lim' _ _))
 w .Elimℝ-Prop2Sym.isSymA x y p =
  cong (-ᵣ_) (+ᵣComm y x)
   ∙∙ p  ∙∙
    +ᵣComm (-ᵣ x) (-ᵣ y)
 w .Elimℝ-Prop2Sym.isPropA x y = isSetℝ (-ᵣ (x +ᵣ y)) ((-ᵣ x) +ᵣ (-ᵣ y))



 -[x-y]≡y-x : ∀ x y → -ᵣ ( x +ᵣ (-ᵣ y) ) ≡ y +ᵣ (-ᵣ x)
 -[x-y]≡y-x x y =
      -ᵣDistr x (-ᵣ y)
      ∙ λ i → +ᵣComm (-ᵣ x) (-ᵣInvol y i) i


 minusComm-absᵣ : ∀ x y → absᵣ (x +ᵣ (-ᵣ y)) ≡ absᵣ (y +ᵣ (-ᵣ x))
 minusComm-absᵣ x y = -absᵣ _ ∙ cong absᵣ (-[x-y]≡y-x x y)

opaque
 unfolding _<ᵣ_
 denseℚinℝ : ∀ u v → u <ᵣ v → ∃[ q ∈ ℚ ] ((u <ᵣ rat q) × (rat q <ᵣ v))
 denseℚinℝ u v =
  PT.map λ ((p , q) , u≤p , p<q , q≤v) →
  let
    m = (p ℚ.+ q) ℚ.· [ 1 / 2 ]
    p<m = subst2 ℚ._<_ (
      p ℚ.· [ 1 / 2 ] ℚ.+ p ℚ.· [ 1 / 2 ] ≡⟨ sym $ ℚ.·DistL+ p [ 1 / 2 ] [ 1 / 2 ] ⟩
      p ℚ.· [ 4 / 4 ]                      ≡⟨ cong (p ℚ.·_) (ℚ.[n/n]≡[m/m] 3 0) ⟩
      p ℚ.· [ 1 / 1 ]                      ≡⟨ ℚ.·IdR p ⟩
      p                                    ∎)
      (sym (ℚ.·DistR+ p q [ 1 / 2 ]))
      (ℚ.<-o+ (p ℚ.· [ 1 / 2 ]) (q ℚ.· [ 1 / 2 ]) (p ℚ.· [ 1 / 2 ])
        (ℚ.<-·o p q [ 1 / 2 ] (ℚ.0<pos 0 2) p<q))
    m<q = subst2 ℚ._<_
      (sym (ℚ.·DistR+ p q [ 1 / 2 ]))
      (
      q ℚ.· [ 1 / 2 ] ℚ.+ q ℚ.· [ 1 / 2 ] ≡⟨ sym $ ℚ.·DistL+ q [ 1 / 2 ] [ 1 / 2 ] ⟩
      q ℚ.· [ 4 / 4 ]                      ≡⟨ cong (q ℚ.·_) (ℚ.[n/n]≡[m/m] 3 0) ⟩
      q ℚ.· [ 1 / 1 ]                      ≡⟨ ℚ.·IdR q ⟩
      q                                    ∎)
      (ℚ.<-+o (p ℚ.· [ 1 / 2 ]) (q ℚ.· [ 1 / 2 ]) (q ℚ.· [ 1 / 2 ])
        ((ℚ.<-·o p q [ 1 / 2 ] (ℚ.0<pos 0 2) p<q)))
  in
    m , ∣ (p , m) , u≤p , p<m , ≤ᵣ-refl _ ∣₁ , ∣ (m , q) , ≤ᵣ-refl _ , m<q , q≤v ∣₁



0≤absᵣ : ∀ x → 0 ≤ᵣ absᵣ x
0≤absᵣ = Elimℝ-Prop.go w
 where

 w : Elimℝ-Prop (λ z → 0 ≤ᵣ absᵣ z)
 w .Elimℝ-Prop.ratA q = isTrans≤≡ᵣ _ _ _ (≤ℚ→≤ᵣ 0 (ℚ.abs' q)
   (subst (0 ℚ.≤_) (ℚ.abs'≡abs q) (ℚ.0≤abs q))) (sym (absᵣ-rat' _))
 w .Elimℝ-Prop.limA x p x₁ =
  let

      zz : _ ≡ _
      zz = sym (congLim
              _ _ _ _
               λ q → sym (≤ᵣ→≡ (x₁ q)) ∙ maxᵣ-impl _ _
              )


  in ≡→≤ᵣ ((cong₂ maxᵣ refl (absᵣ-lim' _ _) ∙ maxᵣ-impl _ _)
       ∙ (snd (NonExpanding₂.β-rat-lim' {ℚ.max} maxR 0 (λ q → (absᵣ (x q)))
          λ _ _ → absᵣ-nonExpanding  _ _ _ (p _ _))
         ∙ zz) ∙ sym (absᵣ-lim' _ _))


 w .Elimℝ-Prop.isPropA _ = isProp≤ᵣ _ _


ℝ₊ : Type
ℝ₊ = Σ _ λ r → 0 <ᵣ r

ℝ₀₊ : Type
ℝ₀₊ = Σ _ λ r → 0 ≤ᵣ r


isSetℝ₊ : isSet ℝ₊
isSetℝ₊ = isSetΣ isSetℝ (λ _ → isProp→isSet (isProp<ᵣ _ _))

isSetℝ₀₊ : isSet ℝ₀₊
isSetℝ₀₊ = isSetΣ isSetℝ (λ _ → isProp→isSet (isProp≤ᵣ _ _))


ℝ₊≡ : {x y : ℝ₊} → fst x ≡ fst y → x ≡ y
ℝ₊≡ = Σ≡Prop λ _ → isProp<ᵣ _ _


ℝ₀₊≡ : {x y : ℝ₀₊} → fst x ≡ fst y → x ≡ y
ℝ₀₊≡ = Σ≡Prop λ _ → isProp≤ᵣ _ _


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
       (ℚ.<ℤ→<ℚ _ _ (_ , refl)) }}


fromNat+ᵣ : ∀ n m → fromNat n +ᵣ fromNat m ≡ fromNat (n ℕ.+ m)
fromNat+ᵣ n m = +ᵣ-rat _ _ ∙ cong rat (ℚ.ℕ+→ℚ+ n m)

isIncrasing : (ℝ → ℝ) → Type₀
isIncrasing f = ∀ x y → x <ᵣ y → f x <ᵣ f y

isPropIsIncrasing : ∀ f → isProp (isIncrasing f)
isPropIsIncrasing f = isPropΠ3 λ _ _ _ → isProp<ᵣ _ _


ℚintervalℙ : ℚ → ℚ → ℙ ℚ
ℚintervalℙ a b x = ((a ℚ.≤ x) × (x ℚ.≤ b)) ,
  isProp× (ℚ.isProp≤ _ _)  (ℚ.isProp≤ _ _)


intervalℙ : ℝ → ℝ → ℙ ℝ
intervalℙ a b x = ((a ≤ᵣ x) × (x ≤ᵣ b)) ,
  isProp× (isProp≤ᵣ _ _ )  (isProp≤ᵣ _ _ )


pointIntervalℙ : ∀ x y → x ≡ y → isContr (Σ _ (_∈ intervalℙ x y))
pointIntervalℙ x y x≡y = (x , ≤ᵣ-refl x , ≡ᵣWeaken≤ᵣ _ _ x≡y) ,
  λ (z , x≤z , z≤y) →
   Σ≡Prop (∈-isProp (intervalℙ x y))
    (isAntisym≤ᵣ x z x≤z (isTrans≤≡ᵣ _ _ _ z≤y (sym x≡y)))

ointervalℙ : ℝ → ℝ → ℙ ℝ
ointervalℙ a b x = ((a <ᵣ x) × (x <ᵣ b)) ,
  isProp× (isProp<ᵣ _ _ )  (isProp<ᵣ _ _ )

ointervalℙ⊆intervalℙ : ∀ a b → ointervalℙ a b ⊆ intervalℙ a b
ointervalℙ⊆intervalℙ a b x (<x  , x<) = <ᵣWeaken≤ᵣ _ _ <x , <ᵣWeaken≤ᵣ _ _ x<


pred< : ℝ → ℙ ℝ
pred< x y = (y <ᵣ x) , isProp<ᵣ _ _

pred≤ : ℝ → ℙ ℝ
pred≤ x y = (y ≤ᵣ x) , isProp≤ᵣ _ _

pred≥ : ℝ → ℙ ℝ
pred≥ x y = (x ≤ᵣ y) , isProp≤ᵣ _ _

pred> : ℝ → ℙ ℝ
pred> x y = (x <ᵣ y) , isProp<ᵣ _ _

pred≤< : ℝ → ℝ → ℙ ℝ
pred≤< a b x = ((a ≤ᵣ x) × (x <ᵣ b)) , isProp× (isProp≤ᵣ _ _) (isProp<ᵣ _ _)

pred<≤ : ℝ → ℝ → ℙ ℝ
pred<≤ a b x = ((a <ᵣ x) × (x ≤ᵣ b)) , isProp× (isProp<ᵣ _ _) (isProp≤ᵣ _ _)



isPosetℝ : IsPoset _≤ᵣ_
isPosetℝ .IsPoset.is-set = isSetℝ
isPosetℝ .IsPoset.is-prop-valued = isProp≤ᵣ
isPosetℝ .IsPoset.is-refl = ≤ᵣ-refl
isPosetℝ .IsPoset.is-trans = isTrans≤ᵣ
isPosetℝ .IsPoset.is-antisym = isAntisym≤ᵣ



supremumℙ : ∀ (P : ℙ ℝ) → (f : ∀ x → x ∈ P → ℝ) → Type
supremumℙ P f =
  Σ _ (isSupremum (isPoset→isProset isPosetℝ) (uncurry f))

infimumℙ : ∀ (P : ℙ ℝ) → (f : ∀ x → x ∈ P → ℝ) → Type
infimumℙ P f =
  Σ _ (isInfimum (isPoset→isProset isPosetℝ) (uncurry f))

