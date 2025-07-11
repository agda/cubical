{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.NatPlusOne

import Cubical.Algebra.CommRing as CR

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous

open import Cubical.HITs.SequentialColimit as SCL
open import Cubical.Data.Sequence

private
  variable
    ℓ ℓ' : Level

record Seq⊆ : Type₁ where
 field
  𝕡 : ℕ → ℙ ℝ
  𝕡⊆ : ∀ n → 𝕡 n ⊆ 𝕡 (suc n)


 𝕡⊆+ : ∀ n m → 𝕡 n ⊆ 𝕡 (m ℕ.+ n)
 𝕡⊆+ n zero = ⊆-refl _
 𝕡⊆+ n (suc m) x = 𝕡⊆ _ x ∘ 𝕡⊆+ n m x

 𝕡⊆' : ∀ n m → n ℕ.≤ m → 𝕡 n ⊆ 𝕡 m
 𝕡⊆' n m (k , p) x = subst (λ l → x ∈ 𝕡 l) p ∘ 𝕡⊆+ _ _ x

 _s⊇_ : ℙ ℝ → Type₀
 _s⊇_ P = ∀ x → x ∈ P → ∃[ n ∈ ℕ ] x ∈ 𝕡 n


 _s⊆_ : ℙ ℝ → Type₀
 _s⊆_ P = ∀ n → 𝕡 n ⊆ P


 elimProp-∩ : ∀ P → ∀ x → x ∈ P  → (P⊇ : _s⊇_ P) → (A : ℝ → Type)
    → (∀ x → isProp (A x))
    → (∀ n → x ∈ 𝕡 n → A x)
    → A x
 elimProp-∩ P x x∈P P⊇ A propA a  =
   PT.rec (propA _)
     (λ (n , x∈ₙ) → a n x∈ₙ)
     (P⊇ x x∈P)

 elimProp-∩' : ∀ P → ∀ x x∈P  → (_s⊇_ P) → (s⊆P : _s⊆_ P)
   → (A : ∀ x → x ∈ P  → Type)
    → (∀ x∈ → isProp (A x x∈))
    → (∀ n x∈ₙ → A x (s⊆P n x x∈ₙ ))
    → A x x∈P
 elimProp-∩' P x x∈P P⊇ Ps⊆ A propA a  =
   PT.rec (propA _)
     (λ (n , x∈ₙ) → subst (A x) (∈-isProp P x _ _) (a n x∈ₙ))
     (P⊇ x x∈P)


 elem𝕡-Seq : Sequence ℓ-zero
 elem𝕡-Seq .Sequence.obj n = Σ _ (_∈ 𝕡 n)
 elem𝕡-Seq .Sequence.map = map-snd (𝕡⊆ _ _)

 elem𝕡-Seq* : ℝ → Sequence ℓ-zero
 elem𝕡-Seq* x .Sequence.obj n = x ∈ 𝕡 n
 elem𝕡-Seq* x .Sequence.map = 𝕡⊆ _ _

 -- module _ P (s⊇P : _s⊇_ P) (s⊆P : _s⊆_ P) where

 --  toSC : ∀ x → ∃[ n ∈ ℕ ] x ∈ 𝕡 n → ElemLim-𝕡
 --  toSC x = {!s⊇P x!}

 --  fromSC : ElimData elem𝕡-Seq (λ _ → Σ ℝ (_∈ P))
 --  fromSC .ElimData.inclP {k} = map-snd (s⊆P k _)
 --  fromSC .ElimData.pushP _ = Σ≡Prop (snd ∘ P) refl


 --  isoElemP : Iso (Σ _ (_∈ P)) ElemLim-𝕡
 --  isoElemP .Iso.fun (x , x∈) = toSC x (s⊇P x x∈)
 --  isoElemP .Iso.inv = SCL.elim _ _ fromSC
 --  isoElemP .Iso.rightInv = {!!}
 --  isoElemP .Iso.leftInv = {!!}

open Seq⊆

ℝU : ℙ ℝ
ℝU x .fst = Unit
ℝU x .snd = isPropUnit

Seq⊆-<N : Seq⊆
Seq⊆-<N .Seq⊆.𝕡 n x = (x <ᵣ fromNat (suc n)) , isProp<ᵣ _ _
Seq⊆-<N .Seq⊆.𝕡⊆ n x x∈ =
  isTrans<ᵣ _ _ _ x∈
   (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤))

Seq⊆-abs<N : Seq⊆
Seq⊆-abs<N .Seq⊆.𝕡 n x =
   (fromNeg (suc n) <ᵣ x) × (x <ᵣ fromNat (suc n)) ,
     isProp× (isProp<ᵣ _ _) (isProp<ᵣ _ _)
Seq⊆-abs<N .Seq⊆.𝕡⊆ n x (<x , x<) =
  isTrans<ᵣ _ _ _
   (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤)) <x
   , isTrans<ᵣ _ _ _ x<
   (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤))



record Seq⊆→ (A : Type ℓ) (s : Seq⊆) : Type ℓ where
 field
  fun : ∀ x n → x ∈ 𝕡 s n → A
  fun⊆ : ∀ x n m x∈ x∈' → n ℕ.< m → fun x n x∈ ≡ fun x m x∈'

 module FromIntersection (isSetA : isSet A) P (s⊆P : s s⊇ P) where

  2c : ∀ x n n' n∈ n∈' → fun x n n∈ ≡ fun x n' n∈'
  2c x = ℕ.elimBy≤ (λ n n' X n∈ n'∈  → sym (X n'∈ n∈))
         λ n n' → ⊎.rec (λ n<n' _ _ → fun⊆ _ _ _ _ _ n<n')
           (λ p _ _ → cong (uncurry (fun x))
           (Σ≡Prop (λ n → ∈-isProp (𝕡 s n) x) p)) ∘ ≤-split

  ∩$ : ∀ x → x ∈ P  → A
  ∩$ x x∈ =
    PT.rec→Set isSetA (λ (n , n∈) → fun x n n∈)
       (λ (n , n∈) (n' , n'∈) → 2c x n n' n∈ n'∈) (s⊆P x x∈)


  -- it shouulb by possisble also for hSet
  ∩$-elimProp : ∀ x x∈ → {B : A → Type ℓ}
     → (∀ a → isProp (B a))
     → (∀ n x∈ → B (fun x n x∈))
     → B (∩$ x x∈)
  ∩$-elimProp x x∈ {B} isPropB g =
    PT.elim (isPropB ∘ PT.rec→Set isSetA (λ (n , n∈) → fun x n n∈)
       (λ (n , n∈) (n' , n'∈) → 2c x n n' n∈ n'∈))
      (uncurry g)
      (s⊆P x x∈)


  ∩$-lem : ∀ x x∈ → ∃[ n ∈ ℕ ] Σ _ λ x∈𝕡 → ∩$ x x∈ ≡ fun x n x∈𝕡
  ∩$-lem x x∈ = ∩$-elimProp x x∈
    {B = λ a → ∃[ n ∈ ℕ ] Σ _ λ x∈𝕡 → a ≡ fun x n x∈𝕡} (λ _ → squash₁)
   λ n x∈' → ∣ n , x∈' , refl ∣₁

  ∩$-∈ₙ : ∀ x x∈ n (x∈ₙ : x ∈ 𝕡 s n)
             → ∩$ x x∈ ≡ fun x n x∈ₙ
  ∩$-∈ₙ x x∈ = ∩$-elimProp x x∈
              {λ y → ∀ n → (x∈ₙ : x ∈ 𝕡 s n)
             → y ≡ fun x n x∈ₙ} (λ _ → isPropΠ2 λ _ _ → isSetA _ _)
               λ _ _ _ _ → 2c x _ _ _ _


  -- it shouulb by possisble also for hSet
  ∩$-elimProp2 : ∀ x x∈ y y∈ → {B : A → A → Type ℓ}
     → (∀ a a' → isProp (B a a'))
     → (∀ n x∈ y∈ → B (fun x n x∈) (fun y n y∈))
     → B (∩$ x x∈) (∩$ y y∈)
  ∩$-elimProp2 x x∈ y y∈ {B} isPropB g =
    PT.elim2 (λ z z' →
      isPropB
       (PT.rec→Set isSetA (λ (n , n∈) → fun x n n∈)
       (λ (n , n∈) (n' , n'∈) → 2c x n n' n∈ n'∈) z)
       (PT.rec→Set isSetA (λ (n , n∈) → fun y n n∈)
       (λ (n , n∈) (n' , n'∈) → 2c y n n' n∈ n'∈) z'))

      (λ (n , x∈) (m , y∈) →
        subst2 B (2c _ _ _ _ _) (2c _ _ _ _ _)
         (g (ℕ.max n m) (𝕡⊆' s _ _ ℕ.left-≤-max x x∈) (𝕡⊆' s _ _ ℕ.right-≤-max y y∈)))
      (s⊆P x x∈) (s⊆P y y∈)


∩$-cont : ∀ P s → (∀ n → ⟨ openPred (Seq⊆.𝕡 s n) ⟩) → ∀ r s⊇P
    → (∀ n → IsContinuousWithPred (𝕡 s n) (flip (Seq⊆→.fun r) n))
    → IsContinuousWithPred P
   (Seq⊆→.FromIntersection.∩$ {A = ℝ} {s = s} r isSetℝ P s⊇P)

∩$-cont P s op r s⊇P cₙ x ε x∈ =
 PT.rec squash₁ (λ (n , p , q) →
   PT.map2 (λ (δ , X) (η , Y) →
        ℚ.min₊ δ η , λ v v∈ x∼v →
          let z = Y v (X v (∼-monotone≤ (ℚ.min≤ _ _) x∼v))
                           (∼-monotone≤ (ℚ.min≤' _ _) x∼v)
          in subst2 _∼[ ε ]_
               (sym (Seq⊆→.FromIntersection.∩$-∈ₙ {A = ℝ} {s = s} r isSetℝ P s⊇P
                _ _ _ _))
               (sym (Seq⊆→.FromIntersection.∩$-∈ₙ {A = ℝ} {s = s} r isSetℝ P s⊇P
                _ _ _ _)) z)
     (op n x p) (cₙ n x ε p))

  (Seq⊆→.FromIntersection.∩$-lem {A = ℝ} {s = s} r isSetℝ P s⊇P
     x x∈)

∩$-cont' : ∀ P s → (∀ n x →
               x ∈ (𝕡 s n) →
               ∃[ δ ∈ ℚ₊ ] (∀ y → x ∼[ δ ] y → y ∈ (𝕡 s (suc n))  )) → ∀ r s⊇P
    → (∀ n → IsContinuousWithPred (𝕡 s n) (flip (Seq⊆→.fun r) n))
    → IsContinuousWithPred P
   (Seq⊆→.FromIntersection.∩$ {A = ℝ} {s = s} r isSetℝ P s⊇P)

∩$-cont' P s op r s⊇P cₙ x ε x∈ =
 PT.rec squash₁ (λ (n , p , q) →
   PT.map2 (λ (δ , X) (η , Y) →
        ℚ.min₊ δ η , λ v v∈ x∼v →
          let z = Y v (X v (∼-monotone≤ (ℚ.min≤ _ _) x∼v))
                           (∼-monotone≤ (ℚ.min≤' _ _) x∼v)
          in subst2 _∼[ ε ]_
               (sym (Seq⊆→.FromIntersection.∩$-∈ₙ {A = ℝ} {s = s} r isSetℝ P s⊇P
                _ _ _ _))
               (sym (Seq⊆→.FromIntersection.∩$-∈ₙ {A = ℝ} {s = s} r isSetℝ P s⊇P
                _ _ _ _)) z)
     (op n x p) (cₙ (suc n) x ε (𝕡⊆ s n x p)))

  (Seq⊆→.FromIntersection.∩$-lem {A = ℝ} {s = s} r isSetℝ P s⊇P
     x x∈)


∩$-cont'' : ∀ P s → (∀ n x →
               x ∈ (𝕡 s n) →
               ∃[ δ ∈ ℚ₊ ] (∀ y → y ∈ P → x ∼[ δ ] y → y ∈ (𝕡 s (suc n))  )) → ∀ r s⊇P
    → (∀ n → IsContinuousWithPred (𝕡 s n) (flip (Seq⊆→.fun r) n))
    → IsContinuousWithPred P
   (Seq⊆→.FromIntersection.∩$ {A = ℝ} {s = s} r isSetℝ P s⊇P)

∩$-cont'' P s op r s⊇P cₙ x ε x∈ =
 PT.rec squash₁ (λ (n , p , q) →
   PT.map2 (λ (δ , X) (η , Y) →
        ℚ.min₊ δ η , λ v v∈ x∼v →
          let z = Y v (X v v∈ (∼-monotone≤ (ℚ.min≤ _ _) x∼v))
                           (∼-monotone≤ (ℚ.min≤' _ _) x∼v)
          in subst2 _∼[ ε ]_
               (sym (Seq⊆→.FromIntersection.∩$-∈ₙ {A = ℝ} {s = s} r isSetℝ P s⊇P
                _ _ _ _))
               (sym (Seq⊆→.FromIntersection.∩$-∈ₙ {A = ℝ} {s = s} r isSetℝ P s⊇P
                _ _ _ _)) z)
     (op n x p) (cₙ (suc n) x ε (𝕡⊆ s n x p)))

  (Seq⊆→.FromIntersection.∩$-lem {A = ℝ} {s = s} r isSetℝ P s⊇P
     x x∈)


infixl 7 _·ᵣ_



open ℚ.HLP


-- HoTT (11.3.46)
opaque
 unfolding _<ᵣ_ absᵣ -ᵣ_
 sqᵣ' : Σ (ℝ → ℝ) IsContinuous
 sqᵣ'  = (λ r → f r (getClamps r))
   , λ u ε →
      PT.elim2 {P = λ gcr _ →
         ∃[ δ ∈ ℚ₊ ] (∀ v → u ∼[ δ ] v
             → f u gcr ∼[ ε ] (f v (getClamps v)))}
        (λ _ _ → squash₁)
        (λ (1+ n , nL) (1+ n' , n'L) →
         let L = (2 ℚ₊· fromNat (suc (suc n')))
             1<L : pos 1 ℤ.<
                ℚ.ℕ₊₁→ℤ
                 (fst
                  (ℤ.0<→ℕ₊₁ (2 ℤ.· (pos (suc (suc n'))))
                   (ℚ.·0< 2 (fromNat (suc (suc n')))
                    tt tt)))
             1<L = subst (1 ℤ.<_)
                    (ℤ.pos·pos 2 (suc (suc n')) ∙ (snd
                  (ℤ.0<→ℕ₊₁ (2 ℤ.· (pos (suc (suc n'))))
                   (ℚ.·0< 2 (fromNat (suc (suc n')))
                    tt tt))) )
                     (ℤ.suc-≤-suc
                       (ℤ.suc-≤-suc (ℤ.zero-≤pos
                         {l = (n' ℕ.+ suc (suc (n' ℕ.+ zero)))} )))

             δ = (invℚ₊ L) ℚ₊· ε
         in ∣ δ , (λ v →
               PT.elim {P = λ gcv → u ∼[ δ ] v → f' u (1+ n , nL) ∼[ ε ] f v gcv}
                (λ _ → isPropΠ λ _ → isProp∼ _ _ _ )
                  (uncurry (λ (1+ n*) n*L u∼v →
                      let z = snd (clampedSq (suc n')) u v
                                    δ u∼v
                          zz : absᵣ (v +ᵣ (-ᵣ u)) <ᵣ rat (fst ε)

                          zz =
                            subst2 (_<ᵣ_)
                              (minusComm-absᵣ u v)
                               (cong rat (ℚ.·IdL (fst ε)))
                                  (isTrans<ᵣ _ _ _
                                   (fst (∼≃abs<ε _ _ _) u∼v)
                                   (<ℚ→<ᵣ _ _ (ℚ.<-·o _ 1 (fst ε)
                                    (ℚ.0<ℚ₊ ε)
                                      (subst (1 ℤ.<_)
                                        (sym (ℤ.·IdL _))
                                         1<L ))))
                          zz* = (sym (absᵣNonNeg (absᵣ u +ᵣ rat (fst ε))
                                 (subst (_≤ᵣ (absᵣ u +ᵣ rat (fst ε)))
                                  (+IdR 0)
                                   (≤ᵣMonotone+ᵣ 0 (absᵣ u)
                                     0 (rat (fst ε))
                                      (0≤absᵣ u)
                                       (≤ℚ→≤ᵣ _ _ $ ℚ.0≤ℚ₊ ε)))))
                          zz' : absᵣ v ≤ᵣ absᵣ (absᵣ u +ᵣ rat (fst ε))
                          zz' =
                             subst2 (_≤ᵣ_)
                               (cong absᵣ (lem--05ᵣ _ _))
                               zz*
                               (isTrans≤ᵣ
                                (absᵣ (u +ᵣ (v +ᵣ (-ᵣ u))))
                                 (absᵣ u +ᵣ absᵣ (v +ᵣ (-ᵣ u)))
                                 _
                                (absᵣ-triangle u (v +ᵣ (-ᵣ u)))
                                (≤ᵣ-o+ _ _ (absᵣ u)
                                  (<ᵣWeaken≤ᵣ _ _ zz)))
                      in ( 2co (1+ n') (1+ n) u
                         (isTrans≤<ᵣ (absᵣ u) _ _
                           (subst2 (_≤ᵣ_)
                             (+IdR (absᵣ u))
                             zz*
                             (≤ᵣMonotone+ᵣ
                               (absᵣ u) (absᵣ u)
                                0 (rat (fst ε))
                                (≤ᵣ-refl (absᵣ u))
                                ((≤ℚ→≤ᵣ _ _ $ ℚ.0≤ℚ₊ ε)))) n'L) nL
                          subst∼[ ℚ₊≡ (ℚ.y·[x/y] L (fst ε)) ]
                          2co (1+ n') (1+ n*) v

                           ((isTrans≤<ᵣ (absᵣ v) _ _
                             zz' n'L))
                             n*L)
                       z))
                        (getClamps v))   ∣₁)
        (getClamps u) (getClamps (absᵣ u +ᵣ rat (fst ε)))
  where

  2co : ∀ n n' r
     → (absᵣ r <ᵣ fromNat (ℕ₊₁→ℕ n))
     → (absᵣ r <ᵣ fromNat (ℕ₊₁→ℕ n'))
     → fst (clampedSq (ℕ₊₁→ℕ n)) r ≡ fst (clampedSq (ℕ₊₁→ℕ n')) r

  2co (1+ n) (1+ n') = Elimℝ-Prop.go w
   where
   w : Elimℝ-Prop
         (λ z →
            absᵣ z <ᵣ fromNat (suc n) →
            absᵣ z <ᵣ fromNat (suc n') →
            fst (clampedSq (suc n)) z ≡ fst (clampedSq (suc n')) z)
   w .Elimℝ-Prop.ratA q n< n<' =
     let Δ : ℕ → ℚ₊
         Δ n = ℚ.<→ℚ₊
              ([ 1 / 4 ])
              ([ pos (suc (suc (n))) / 1 ])

              ((<Δ (suc (n))))
         q* : ℕ → ℚ
         q* n = ℚ.clamp (ℚ.- (fst (Δ n))) (fst (Δ n)) q
         q₁ = q* n
         q₂ = q* n'

         -Δ₁≤q : ∀ n → absᵣ (rat q) <ᵣ rat [ pos (suc n) / 1+ 0 ]
              → ℚ.- (fst (Δ n)) ℚ.≤ q
         -Δ₁≤q n n< = subst (ℚ.- fst (Δ n) ℚ.≤_) (ℚ.-Invol q)
          (ℚ.minus-≤ (ℚ.- q) (fst (Δ n))
            (ℚ.isTrans≤ _ _ _ (
             subst (ℚ.- q ℚ.≤_) (sym (ℚ.-abs q) ∙
                ℚ.abs'≡abs q) (ℚ.≤abs (ℚ.- q))) (abs'q≤Δ₁ q n n<)))

         q₁= : ∀ n n< → q* n ≡ q
         q₁= n n< = ℚ.inClamps (ℚ.- (fst (Δ n))) (fst (Δ n)) q
            (-Δ₁≤q n n<) (ℚ.isTrans≤ q (ℚ.abs' q) (fst (Δ n))
                  (subst (q ℚ.≤_) (ℚ.abs'≡abs q)
                     (ℚ.≤abs q)) (abs'q≤Δ₁ q n n<))
         z : q₁ ℚ.· q₁
              ≡ q₂ ℚ.· q₂
         z = cong₂ ℚ._·_ (q₁= n n<) (q₁= n n<)
               ∙ sym (cong₂ ℚ._·_ (q₁= n' n<') (q₁= n' n<'))
     in cong rat z
   w .Elimℝ-Prop.limA x p R n< n<' =
     eqℝ _ _
           (λ ε → PT.rec (isProp∼ _ _ _) (ww ε) <n⊓)


    where

    n⊓ n⊔ : ℕ
    n⊓ = ℕ.min n n'
    n⊔ = ℕ.max n n'

    <n⊓ : absᵣ (lim x p) <ᵣ rat [ pos (suc n⊓) / 1+ 0 ]
    <n⊓ =
     let z = <min-rr _ _ _ n< n<'
     in subst (absᵣ (lim x p) <ᵣ_)
       (cong (rat ∘ [_/ 1+ 0 ]) (
        cong₂ ℤ.min (cong (1 ℤ.+_) (ℤ.·IdR (pos n))
          ∙ sym (ℤ.pos+ 1 n)) ((cong (1 ℤ.+_) (ℤ.·IdR (pos n'))
          ∙ sym (ℤ.pos+ 1 n')))
         ∙ ℤ.min-pos-pos (suc n) (suc n'))) z

    ww : ∀ ε → absᵣ (lim x p) Σ<ᵣ
                rat [ pos (suc n⊓) / 1+ 0 ]
             → fst (clampedSq (suc n)) (lim x p) ∼[ ε ]
                 fst (clampedSq (suc n')) (lim x p)
    ww ε ((q , q') , lx≤q , q<q' , q'≤n) =
     lim-lim _ _ ε δ η _ _ 0<ε-[δ+η] ll
     where
      Δ θ : ℚ₊
      Δ = ℚ.<→ℚ₊ q q' q<q'
      θ = ℚ.min₊ (ℚ./3₊ ε) Δ

      3θ≤ε : (fst θ) ℚ.+ ((fst θ) ℚ.+ (fst θ)) ℚ.≤ fst ε
      3θ≤ε = subst2 ℚ._≤_
         (3·x≡x+[x+x] (fst θ))
          (cong (3 ℚ.·_) (ℚ.·Comm _ _) ∙ ℚ.y·[x/y] 3 (fst ε))
        (ℚ.≤-o· ((ℚ.min (fst (ℚ./3₊ ε)) (fst Δ)))
                 (fst (ℚ./3₊ ε)) 3 ((ℚ.0≤ℚ₊ 3)) (ℚ.min≤ (fst (ℚ./3₊ ε)) (fst Δ)))

      δ η υ : ℚ₊
      δ = (([ pos (suc (suc n)) / 1+ (suc n⊔) ] , _)
                                     ℚ₊· θ)
      η = (([ pos (suc (suc n')) / 1+ (suc n⊔) ] , _)
                                     ℚ₊· θ)
      υ = invℚ₊ (2 ℚ₊· fromNat (suc (suc n⊔))) ℚ₊· θ

      ν-δη : ∀ n* → fst (invℚ₊ (2 ℚ₊· fromNat (suc (suc n⊔))) ℚ₊· θ)
             ≡ fst (invℚ₊ (2 ℚ₊· fromNat (suc (suc n*))) ℚ₊·
             ((([ pos (suc (suc n*)) / 1+ (suc n⊔) ] , _)
                                     ℚ₊· θ)))
      ν-δη n* = cong (ℚ._· fst θ)
          (cong (fst ∘ invℚ₊)
               (cong {x = fromNat (suc (suc n⊔)) , _}
                     {y = fromNat (suc (suc n*)) ℚ₊·
                          ([ pos (suc (suc n⊔)) / 2+ n* ] , _)}
                (2 ℚ₊·_) (ℚ₊≡ (sym (m·n/m _ _))) ∙
             ℚ₊≡ (ℚ.·Assoc 2 _ _))
           ∙ cong fst (sym (ℚ.invℚ₊Dist· _
              ([ pos (suc (suc n⊔)) / 1+ (suc n*) ] , _))))
            ∙ sym (ℚ.·Assoc (fst (invℚ₊ (2 ℚ₊· fromNat (suc (suc n*)))))
              [ pos (suc (suc n*)) / 1+ (suc n⊔) ] (fst θ))

      0<ε-[δ+η] : 0< (fst ε ℚ.- (fst δ ℚ.+ fst η))
      0<ε-[δ+η] = snd (ℚ.<→ℚ₊ (fst δ ℚ.+ fst η) (fst ε)
           (ℚ.isTrans<≤ _ _ _
              ( let z = ((ℚ.≤Monotone+
                       (fst δ) (fst θ)
                       (fst η)  (fst θ)
                         (subst (fst δ ℚ.≤_) (ℚ.·IdL (fst θ))
                          (ℚ.≤-·o ([ pos (suc (suc n)) / 1+ (suc n⊔) ]) 1
                             (fst θ) (ℚ.0≤ℚ₊ θ)
                               (subst2 ℤ._≤_ (sym (ℤ.·IdR _))
                                (ℤ.max-pos-pos (suc (suc n)) (suc (suc n'))
                                   ∙ sym (ℤ.·IdL _))
                                   (ℤ.≤max {pos (suc (suc n))}
                                      {pos (suc (suc n'))}))))
                         (subst (fst η ℚ.≤_) (ℚ.·IdL (fst θ))
                          ((ℚ.≤-·o ([ pos (suc (suc n')) / 1+ (suc n⊔) ]) 1
                             (fst θ) (ℚ.0≤ℚ₊ θ)
                              ((subst2 ℤ._≤_ (sym (ℤ.·IdR _))
                                (ℤ.maxComm _ _
                                  ∙ ℤ.max-pos-pos (suc (suc n)) (suc (suc n'))
                                  ∙ sym (ℤ.·IdL _))
                                   (ℤ.≤max {pos (suc (suc n'))}
                                      {pos (suc (suc n))}))))))))
                    z' = ℚ.<≤Monotone+
                          0 (fst θ)
                         (fst δ ℚ.+ (fst η))  (fst θ ℚ.+ (fst θ))
                         (ℚ.0<ℚ₊ θ) z
                in subst (ℚ._<
                      fst θ ℚ.+ (fst θ ℚ.+ fst θ))
                        (ℚ.+IdL (fst δ ℚ.+ (fst η))) z')

                      3θ≤ε))

      R' :
        fst (clampedSq (suc n)) (x υ)
         ∼[ (fst ε ℚ.- (fst δ ℚ.+ fst η)) , 0<ε-[δ+η] ]
          fst (clampedSq (suc n')) (x υ)
      R' = invEq (∼≃≡ _ _) (R υ ν<n ν<n') _
       where

        υ+υ<Δ : fst (υ ℚ₊+ υ) ℚ.< fst Δ
        υ+υ<Δ = ℚ.isTrans<≤
         (fst (υ ℚ₊+ υ)) (fst θ) (fst Δ)
          (subst2 (ℚ._<_)
           (ℚ.·DistR+
              (fst (invℚ₊ (2 ℚ₊· fromNat (suc (suc n⊔)))))
              (fst (invℚ₊ (2 ℚ₊· fromNat (suc (suc n⊔)))))
              (fst θ))
              (ℚ.·IdL (fst θ))
              ((ℚ.<-·o
                (((fst (invℚ₊ (2 ℚ₊· fromNat (suc (suc n⊔))))))
                 ℚ.+
                 ((fst (invℚ₊ (2 ℚ₊· fromNat (suc (suc n⊔)))))))
                 1 (fst θ)
               (ℚ.0<ℚ₊ θ)
                (subst (ℚ._< 1)
                  (sym (ℚ.ε/2+ε/2≡ε _) ∙ cong (λ x → x ℚ.+ x)
                    (ℚ.·Comm _ _ ∙ cong fst
                      (ℚ.invℚ₊Dist· 2 (fromNat (suc (suc n⊔))))))
                    (1/n<sucK _ _) ))))
                (ℚ.min≤' (fst (ℚ./3₊ ε)) (fst Δ))

        ν<n⊓ : absᵣ (x υ) <ᵣ (fromNat (suc n⊓))
        ν<n⊓ = isTrans≤<ᵣ (absᵣ (x υ))
                  (rat (q ℚ.+ fst (υ ℚ₊+ υ))) ((fromNat (suc n⊓)))
                  (∼→≤ _ _ lx≤q _ _
                       (∼→∼' _ _ _ (absᵣ-nonExpanding _ _ _
                             (sym∼ _ _ _ (𝕣-lim-self x p υ υ)))))
                     (isTrans<≤ᵣ
                        (rat (q ℚ.+ fst (υ ℚ₊+ υ)))
                        (rat q')
                        (rat [ pos (suc n⊓) / 1+ 0 ])
                         (subst {x = rat (q ℚ.+ fst Δ) }
                             (rat (q ℚ.+ fst (υ ℚ₊+ υ)) <ᵣ_)
                           (cong rat (lem--05 {q} {q'}))
                            (<ℚ→<ᵣ _ _ (ℚ.<-o+ _ _ q υ+υ<Δ))) q'≤n)

        ν<n : absᵣ (x υ) <ᵣ fromNat (suc n)
        ν<n = isTrans<≤ᵣ (absᵣ (x υ)) (fromNat (suc n⊓)) (fromNat (suc n))
                 ν<n⊓ (≤ℚ→≤ᵣ _ _
                   (subst (λ n* → [ n* / 1+ 0 ] ℚ.≤ (fromNat (suc n)))
                     (ℤ.min-pos-pos (suc n) (suc n'))
                      (ℚ.≤ℤ→≤ℚ _ _ (ℤ.min≤ {pos (suc n)} {pos (suc n')})) ))

        ν<n' : absᵣ (x υ) <ᵣ fromNat (suc n')
        ν<n' = isTrans<≤ᵣ (absᵣ (x υ)) (fromNat (suc n⊓)) (fromNat (suc n'))
                 ν<n⊓ (≤ℚ→≤ᵣ _ _
                   (subst (λ n* → [ n* / 1+ 0 ] ℚ.≤ (fromNat (suc n')))
                     (ℤ.minComm (pos (suc n')) (pos (suc n))
                       ∙ ℤ.min-pos-pos (suc n) (suc n'))
                      (ℚ.≤ℤ→≤ℚ _ _ (ℤ.min≤ {pos (suc n')} {pos (suc n)})) ))


      ll : fst (clampedSq (suc n))
             (x (invℚ₊ (2 ℚ₊· fromNat (suc (suc n))) ℚ₊· δ))
             ∼[ (fst ε ℚ.- (fst δ ℚ.+ fst η)) , 0<ε-[δ+η] ]
              fst (clampedSq (suc n'))
             (x (invℚ₊ (2 ℚ₊· fromNat (suc (suc n'))) ℚ₊· η))
      ll = cong (fst (clampedSq (suc n)) ∘S x) (ℚ₊≡ (ν-δη n))
              subst∼[ refl ]
            cong (fst (clampedSq (suc n')) ∘S x) (ℚ₊≡ (ν-δη n')) $ R'

   w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isSetℝ _ _

  f' : ∀ r → Σ ℕ₊₁ (λ n → absᵣ r <ᵣ rat [ pos (ℕ₊₁→ℕ n) / 1+ 0 ])  → ℝ
  f' r = (λ ((1+ n) , <n) → fst (clampedSq (suc n)) r )

  f : ∀ r → ∃[ n ∈ ℕ₊₁ ] absᵣ r <ᵣ fromNat (ℕ₊₁→ℕ n) → ℝ
  f r = PT.rec→Set {B = ℝ} isSetℝ
     (f' r)
     (λ (n , u) (n' , u') → 2co n n' r u u')

 sqᵣ : ℝ → ℝ
 sqᵣ = fst sqᵣ'

 /2ᵣ-L : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ ([ 1 / 2 ] , _))
 /2ᵣ-L = fromLipschitz ([ 1 / 2 ] , _)
   (_ , Lipschitz-rat∘ ([ 1 / 2 ] , _) (ℚ._· [ 1 / 2 ])
    λ q r ε x →
      subst (ℚ._< ([ 1 / 2 ]) ℚ.· (fst ε))
       (sym (ℚ.pos·abs [ 1 / 2 ] (q ℚ.- r)
        (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 1 / 2 ]} _ ))
        ∙ cong ℚ.abs (ℚ.·Comm _ _ ∙ ℚ.·DistR+ q (ℚ.- r) [ 1 / 2 ]
         ∙ cong ((q ℚ.· [ 1 / 2 ]) ℚ.+_)
             (sym (ℚ.·Assoc -1 r [ 1 / 2 ]))))
       (ℚ.<-o· (ℚ.abs (q ℚ.- r)) (fst ε) [ 1 / 2 ]
        ((𝟚.toWitness {Q = ℚ.<Dec 0 [ 1 / 2 ]} _ )) x))

 /2ᵣ : ℝ → ℝ
 /2ᵣ = fst /2ᵣ-L


 sqᵣ-rat : ∀ r → sqᵣ (rat r) ≡ rat (r ℚ.· r)
 sqᵣ-rat = ElimProp.go w
  where
  w : ElimProp (λ z → sqᵣ (rat z) ≡ rat (z ℚ.· z))
  w .ElimProp.isPropB _ = isSetℝ _ _
  w .ElimProp.f x = cong
        (λ x → rat (x ℚ.· x))
         (ℚ.inClamps (ℚ.- c) c _
          -c<x x<c)

     where
     x' : ℚ
     x' = (_//_.[ x ])

     c : ℚ
     c = (fst (fromNat (suc (suc (getClampsOnQ x' .fst .ℕ₊₁.n))))
         ℚ.- _//_.[ 1 , 4 ])


     c' : ℚ
     c' = fromNat ((suc (getClampsOnQ x' .fst .ℕ₊₁.n)))

     <c' : ℚ.abs' x' ℚ.< c'
     <c' = <ᵣ→<ℚ _ _ (snd (getClampsOnQ x'))

     c'≤c : c' ℚ.≤ c
     c'≤c = subst2 ℚ._≤_
              (ℚ.+IdR c') (ℚ.+Assoc c' 1 (ℚ.- [ 1 / 4 ])
                ∙ cong ((ℚ._- [ 1 / 4 ])) (ℚ.+Comm c' 1 ∙
                 ℚ.ℕ+→ℚ+ _ _))
              (ℚ.≤-o+ 0 (1 ℚ.- [ 1 / 4 ]) c' ℚ.decℚ≤?  )

     <c : ℚ.abs' x' ℚ.≤ c
     <c = ℚ.isTrans≤ (ℚ.abs' x') c' c
        (ℚ.<Weaken≤ (ℚ.abs' x') c' <c') c'≤c


     -c<x : ℚ.- c ℚ.≤ x'
     -c<x = subst (ℚ.- c ℚ.≤_) (ℚ.-Invol x') (ℚ.minus-≤ (ℚ.- x') c
        (ℚ.isTrans≤ (ℚ.- x') (ℚ.abs' x') c (ℚ.-≤abs' x') <c))


     x<c :  _//_.[ x ] ℚ.≤ c
     x<c = ℚ.isTrans≤ x' (ℚ.abs' x') c (ℚ.≤abs' x') <c


 IsContinuous/2ᵣ : IsContinuous /2ᵣ
 IsContinuous/2ᵣ = Lipschitz→IsContinuous _ /2ᵣ (snd /2ᵣ-L)


 IsContinuousSqᵣ : IsContinuous sqᵣ
 IsContinuousSqᵣ = snd sqᵣ'






 _·ᵣ_ : ℝ → ℝ → ℝ
 u ·ᵣ v = /2ᵣ ((sqᵣ (u +ᵣ v)) +ᵣ (-ᵣ (sqᵣ u +ᵣ sqᵣ v)))





 rat·ᵣrat : ∀ r q → rat (r ℚ.· q) ≡ rat r ·ᵣ rat q
 rat·ᵣrat r q =
   cong rat (
      distℚ! (r ℚ.· q) ·[ ge1 ≡ (ge1 +ge ge1) ·ge ge[ [ 1 / 2 ] ] ]
        ∙ cong (ℚ._· [ 1 / 2 ]) (lem--058 {r} {q})) ∙
    λ i → /2ᵣ ((sqᵣ-rat (r ℚ.+ q) (~ i))
     +ᵣ (-ᵣ (sqᵣ-rat r (~ i) +ᵣ sqᵣ-rat q (~ i))))


 ·ᵣComm : ∀ x y → x ·ᵣ y ≡ y ·ᵣ x
 ·ᵣComm u v i =
   /2ᵣ ((sqᵣ (+ᵣComm u v i)) +ᵣ (-ᵣ (+ᵣComm (sqᵣ u) (sqᵣ v) i)))


 IsContinuous·ᵣR : ∀ x → IsContinuous (_·ᵣ x)
 IsContinuous·ᵣR x =
   IsContinuous∘ _
    (λ u → (sqᵣ (u +ᵣ x)) +ᵣ (-ᵣ ((sqᵣ u) +ᵣ (sqᵣ x))))
     IsContinuous/2ᵣ
       (cont₂+ᵣ (λ u → (sqᵣ (u +ᵣ x)))
         (λ u → (-ᵣ ((sqᵣ u) +ᵣ (sqᵣ x))))
          (IsContinuous∘ _ _ IsContinuousSqᵣ (IsContinuous+ᵣR x))
           (IsContinuous∘ _ _ IsContinuous-ᵣ
              (IsContinuous∘ _ _ (IsContinuous+ᵣR (sqᵣ x)) IsContinuousSqᵣ)))

 cont₂·ᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
   → IsContinuous (λ x → f x ·ᵣ g x)
 cont₂·ᵣ f g fC gC = IsContinuous∘ _
    (λ u → (sqᵣ (f u +ᵣ g u)) +ᵣ (-ᵣ ((sqᵣ (f u)) +ᵣ (sqᵣ (g u)))))
     IsContinuous/2ᵣ
      (cont₂+ᵣ _ _
        (IsContinuous∘ _ _
          IsContinuousSqᵣ
           (cont₂+ᵣ _ _ fC gC))
        (IsContinuous∘ _ _
           IsContinuous-ᵣ
           (cont₂+ᵣ _ _
             (IsContinuous∘ _ _ IsContinuousSqᵣ fC)
             ((IsContinuous∘ _ _ IsContinuousSqᵣ gC)))))

cont₂·₂ᵣ : ∀ {f₀ f₁} → (IsContinuous₂ f₀) → (IsContinuous₂ f₁)
  → IsContinuous₂ (λ x x' → f₀ x x' ·ᵣ f₁ x x')
cont₂·₂ᵣ {f₀} {f₁} f₀C f₁C =
  (λ x → cont₂·ᵣ _ _ (fst f₀C x) (fst f₁C x)) ,
  λ x → cont₂·ᵣ _ _ (snd f₀C x) (snd f₁C x)

IsContinuous·ᵣL : ∀ x → IsContinuous (x ·ᵣ_)
IsContinuous·ᵣL x = subst IsContinuous
  (funExt λ z → ·ᵣComm z x) (IsContinuous·ᵣR x)



·ᵣAssoc : ∀ x y z →  x ·ᵣ (y ·ᵣ z) ≡ (x ·ᵣ y) ·ᵣ z
·ᵣAssoc r r' r'' =
  ≡Continuous (_·ᵣ (r' ·ᵣ r'')) (λ x → (x ·ᵣ r') ·ᵣ r'')
     (IsContinuous·ᵣR (r' ·ᵣ r''))
     (IsContinuous∘ _ _ (IsContinuous·ᵣR r'') (IsContinuous·ᵣR r'))
      (λ q →
        ≡Continuous
          (λ x → (rat q ·ᵣ (x ·ᵣ r'')))
          (λ x → ((rat q ·ᵣ x) ·ᵣ r''))
          ((IsContinuous∘ _ _ (IsContinuous·ᵣL (rat q))
             (IsContinuous·ᵣR r'')))
          (IsContinuous∘ _ _
           (IsContinuous·ᵣR r'')
           (IsContinuous·ᵣL (rat q)))
          (λ q' →
            ≡Continuous
               (λ x → (rat q ·ᵣ (rat q' ·ᵣ x)))
               (λ x → ((rat q ·ᵣ rat q') ·ᵣ x))
               (IsContinuous∘ _ _
                 (IsContinuous·ᵣL (rat q))
                 (IsContinuous·ᵣL (rat q')))
               (IsContinuous·ᵣL (rat q ·ᵣ rat q'))
               (λ q'' →
                 cong (rat q ·ᵣ_) (sym (rat·ᵣrat q' q''))
                   ∙∙ sym (rat·ᵣrat q (q' ℚ.· q'')) ∙∙
                   cong rat (ℚ.·Assoc _ _ _)
                   ∙∙ rat·ᵣrat (q ℚ.· q') q'' ∙∙
                   cong (_·ᵣ rat q'') (rat·ᵣrat q q')) r'') r') r

·IdR : ∀ x → x ·ᵣ 1 ≡ x
·IdR = ≡Continuous _ _ (IsContinuous·ᵣR 1) IsContinuousId
  (λ r → sym (rat·ᵣrat r 1) ∙ cong rat (ℚ.·IdR r) )

·IdL : ∀ x → 1 ·ᵣ x ≡ x
·IdL = ≡Continuous _ _ (IsContinuous·ᵣL 1) IsContinuousId
  (λ r → sym (rat·ᵣrat 1 r) ∙ cong rat (ℚ.·IdL r) )

opaque
 unfolding _+ᵣ_
 ·DistL+ : (x y z : ℝ) → (x ·ᵣ (y +ᵣ z)) ≡ ((x ·ᵣ y) +ᵣ (x ·ᵣ z))
 ·DistL+ x y z =
   ≡Continuous _ _
    (IsContinuous·ᵣR (y +ᵣ z))
    (cont₂+ᵣ _ _ (IsContinuous·ᵣR y) (IsContinuous·ᵣR z))
    (λ x' →
      ≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuous·ᵣL (rat x')) (IsContinuous+ᵣR z))
        (IsContinuous∘ _ _
         (IsContinuous+ᵣR (rat x' ·ᵣ z)) (IsContinuous·ᵣL (rat x')))
        (λ y' →
          ≡Continuous _ _
            (IsContinuous∘ _ _ (IsContinuous·ᵣL (rat x'))
              (IsContinuous+ᵣL (rat y')))
            (IsContinuous∘ _ _ (IsContinuous+ᵣL (rat x' ·ᵣ rat y'))
                 (IsContinuous·ᵣL (rat x')) )
            (λ z' → sym (rat·ᵣrat _ _)
                   ∙∙ cong rat (ℚ.·DistL+ x' y' z') ∙∙
                      cong₂ _+ᵣ_ (rat·ᵣrat _ _) (rat·ᵣrat _ _)) z)
        y)
    x


 ·DistR+ : (x y z : ℝ) → ((x +ᵣ y) ·ᵣ z) ≡ ((x ·ᵣ z) +ᵣ (y ·ᵣ z))
 ·DistR+ x y z = ·ᵣComm _ _ ∙∙ ·DistL+ z x y
   ∙∙ cong₂ _+ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _)

IsCommRingℝ : CR.IsCommRing 0 1 (_+ᵣ_) (_·ᵣ_) (-ᵣ_)
IsCommRingℝ = CR.makeIsCommRing
 isSetℝ
  +ᵣAssoc +IdR +-ᵣ +ᵣComm ·ᵣAssoc
   ·IdR ·DistL+ ·ᵣComm

x+x≡2x : ∀ x → x +ᵣ x ≡ 2 ·ᵣ x
x+x≡2x x = cong₂ _+ᵣ_
    (sym (·IdL x))
    (sym (·IdL x))
    ∙ sym (·DistR+ 1 1 x)
    ∙ cong (_·ᵣ x) (+ᵣ-rat _ _)


·ᵣMaxDistrPos : ∀ x y z → 0 ℚ.≤ z →  (maxᵣ x y) ·ᵣ (rat z) ≡ maxᵣ (x ·ᵣ rat z) (y ·ᵣ rat z)
·ᵣMaxDistrPos x y z 0<z =
  ≡Continuous _ _
     (IsContinuous∘ _ _ (IsContinuous·ᵣR (rat z)) (IsContinuousMaxR y))
     (IsContinuous∘ _ _ (IsContinuousMaxR
       (y ·ᵣ (rat z))) (IsContinuous·ᵣR (rat z)))
     (λ x' →
       ≡Continuous _ _
         (IsContinuous∘ _ _ (IsContinuous·ᵣR (rat z)) (IsContinuousMaxL (rat x')))
         ((IsContinuous∘ _ _ (IsContinuousMaxL (rat x' ·ᵣ (rat z)))
                                (IsContinuous·ᵣR (rat z))))
         (λ y' → sym (rat·ᵣrat _ _)
             ∙∙ cong rat (ℚ.·MaxDistrℚ' x' y' z 0<z) ∙∙
              (cong₂ maxᵣ (rat·ᵣrat x' z) (rat·ᵣrat y' z)))
         y)
     x



𝕣-lim-dist : ∀ x y ε → absᵣ ((x (ℚ./2₊ ε)) +ᵣ (-ᵣ lim x y)) <ᵣ rat (fst ε)
𝕣-lim-dist x y ε =
   fst (∼≃abs<ε _ _ ε) $ subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
     $ 𝕣-lim-self x y (ℚ./2₊ ε) (ℚ./2₊ ε)







opaque

 unfolding _·ᵣ_

 cont₂·ᵣWP : ∀ P f g
   → (IsContinuousWithPred P f)
   → (IsContinuousWithPred P g)
   → IsContinuousWithPred P (λ x x∈ → f x x∈ ·ᵣ g x x∈)
 cont₂·ᵣWP P f g fC gC = IsContinuousWP∘' P _
    (λ u x∈ → (sqᵣ (f u x∈ +ᵣ g u x∈)) +ᵣ
     (-ᵣ ((sqᵣ (f u x∈)) +ᵣ (sqᵣ (g u x∈)))))
     IsContinuous/2ᵣ
     (contDiagNE₂WP sumR P _ _
       ((IsContinuousWP∘' P _ _
          IsContinuousSqᵣ
           (contDiagNE₂WP sumR P _ _ fC gC)))
       ((IsContinuousWP∘' P _ _
           IsContinuous-ᵣ
           (contDiagNE₂WP sumR P _ _
             (IsContinuousWP∘' P _ _ IsContinuousSqᵣ fC)
             ((IsContinuousWP∘' P _ _ IsContinuousSqᵣ gC))))))


·-ᵣ : ∀ x y → x ·ᵣ (-ᵣ y) ≡ -ᵣ (x ·ᵣ y)
·-ᵣ x =
  ≡Continuous _ _ (IsContinuous∘ _ _
       (IsContinuous·ᵣL x) IsContinuous-ᵣ)
      (IsContinuous∘ _ _ IsContinuous-ᵣ (IsContinuous·ᵣL x))
       λ y' →
         ≡Continuous _ _
             (IsContinuous·ᵣR (-ᵣ (rat y')))
              ((IsContinuous∘ _ _ IsContinuous-ᵣ (IsContinuous·ᵣR (rat y'))))
          (λ x' → cong (rat x' ·ᵣ_) (-ᵣ-rat _) ∙ sym (rat·ᵣrat _ _) ∙∙ cong rat (·- x' y') ∙∙
              sym (-ᵣ-rat _) ∙ (cong -ᵣ_ (rat·ᵣrat _ _)))
          x

·DistL- : (x y z : ℝ) → (x ·ᵣ (y -ᵣ z)) ≡ ((x ·ᵣ y) -ᵣ (x ·ᵣ z))
·DistL- x y z = ·DistL+ x y (-ᵣ z) ∙ cong ((x ·ᵣ y) +ᵣ_) (·-ᵣ _ _)


-ᵣ· : ∀ x y →  ((-ᵣ x) ·ᵣ y) ≡  -ᵣ (x ·ᵣ y)
-ᵣ· x y = ·ᵣComm _ _ ∙∙ ·-ᵣ y x ∙∙ cong -ᵣ_ (·ᵣComm _ _)

-ᵣ·-ᵣ : ∀ x y →  ((-ᵣ x) ·ᵣ (-ᵣ y)) ≡  (x ·ᵣ y)
-ᵣ·-ᵣ x y = -ᵣ· x (-ᵣ y) ∙ cong (-ᵣ_) (·-ᵣ x y) ∙ -ᵣInvol _


_^ⁿ_ : ℝ → ℕ → ℝ
x ^ⁿ zero = 1
x ^ⁿ suc n = (x ^ⁿ n) ·ᵣ x


^ⁿ-ℚ^ⁿ : ∀ n q → ((rat q) ^ⁿ n) ≡ rat (q ℚ.ℚ^ⁿ n)
^ⁿ-ℚ^ⁿ zero _ = refl
^ⁿ-ℚ^ⁿ (suc n) a =
  cong (_·ᵣ rat a) (^ⁿ-ℚ^ⁿ n a) ∙
          sym (rat·ᵣrat _ _)


opaque
 unfolding absᵣ
 ·absᵣ : ∀ x y → absᵣ (x ·ᵣ y) ≡ absᵣ x ·ᵣ absᵣ y
 ·absᵣ x = ≡Continuous _ _
   ((IsContinuous∘ _ _  IsContinuousAbsᵣ (IsContinuous·ᵣL x)
                     ))
   (IsContinuous∘ _ _ (IsContinuous·ᵣL (absᵣ x))
                     IsContinuousAbsᵣ)
   λ y' →
     ≡Continuous _ _
   ((IsContinuous∘ _ _  IsContinuousAbsᵣ (IsContinuous·ᵣR (rat y'))
                     ))
   (IsContinuous∘ _ _ (IsContinuous·ᵣR (absᵣ (rat y')))
                     IsContinuousAbsᵣ)
                      (λ x' →
                        cong absᵣ (sym (rat·ᵣrat _ _)) ∙∙
                         cong rat (sym (ℚ.abs'·abs' _ _)) ∙∙ rat·ᵣrat _ _) x


IsContinuous₂·ᵣ :  IsContinuous₂ _·ᵣ_
IsContinuous₂·ᵣ = IsContinuous·ᵣL , IsContinuous·ᵣR

