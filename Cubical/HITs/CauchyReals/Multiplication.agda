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
open import Cubical.Data.Int.Fast as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.NatPlusOne

import Cubical.Algebra.CommRing as CR

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊)


open import Cubical.HITs.CauchyReals.Base

open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous

open import Cubical.HITs.SequentialColimit as SCL
open import Cubical.Data.Sequence

open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection
open import Cubical.Tactics.CommRingSolverFast.IntReflection

open import Cubical.HITs.CauchyReals.LiftingExpr

private
  variable
    ℓ ℓ' : Level



record Seq⊆ : Type₁ where
 field
  𝕡 : ℕ → ℙ ℝ
  𝕡⊆ : ∀ n → 𝕡 n ⊆ 𝕡 (suc n)


 𝕡⊆+ : ∀ n m → 𝕡 n ⊆ 𝕡 (m ℕ.+ n)
 𝕡⊆+ n zero = ⊆-refl (𝕡 n)
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
Seq⊆-abs<N .Seq⊆.𝕡 n = ointervalℙ (fromNeg (suc n)) (fromNat (suc n)) 

Seq⊆-abs<N .Seq⊆.𝕡⊆ n x (<x , x<) =
  isTrans<ᵣ _ _ _
   (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤)) <x
   , isTrans<ᵣ _ _ _ x<
   (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤))

Seq⊆-[0,N⟩ : Seq⊆
Seq⊆-[0,N⟩ .Seq⊆.𝕡 n = pred≤< 0 (fromNat (suc n))
Seq⊆-[0,N⟩ .Seq⊆.𝕡⊆ n x (0≤x , x<sn) = 0≤x , 
  isTrans<ᵣ _ _ _ x<sn
   (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤))

Seq⊆-abs<N-s⊇-⊤Pred : Seq⊆-abs<N Seq⊆.s⊇ ⊤Pred
Seq⊆-abs<N-s⊇-⊤Pred x _ =     PT.map
      (λ (1+ n , X) →
        n , (isTrans≡<ᵣ _ _ _ (cong rat ℚ! ∙ sym (-ᵣ-rat _) ) $ isTrans<≤ᵣ _ _ _ (-ᵣ<ᵣ _ _ X)
                  (isTrans≡≤ᵣ _ _ _ (cong -ᵣ_ (-absᵣ x) )
                    (isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _ (≤absᵣ (-ᵣ x)))
                       (-ᵣInvol _))))
           , isTrans≤<ᵣ _ _ _ (≤absᵣ x) X)
      (getClamps x)


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
        subst2 B (2c _ _ _ _ _) (2c _ _ _ ((𝕡⊆' s _ _ (ℕ.right-≤-max {m = n}) y y∈)) _)
         (g (ℕ.max n m) (𝕡⊆' s _ _ ℕ.left-≤-max x x∈) (𝕡⊆' s _ _ (ℕ.right-≤-max {m = n}) y y∈)))
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
                           (∼-monotone≤ (ℚ.min≤' (fst δ) _) x∼v)
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
                           (∼-monotone≤ (ℚ.min≤' (fst δ) _) x∼v)
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
                           (∼-monotone≤ (ℚ.min≤' (fst δ) _) x∼v)
          in subst2 _∼[ ε ]_
               (sym (Seq⊆→.FromIntersection.∩$-∈ₙ {A = ℝ} {s = s} r isSetℝ P s⊇P
                _ _ _ _))
               (sym (Seq⊆→.FromIntersection.∩$-∈ₙ {A = ℝ} {s = s} r isSetℝ P s⊇P
                _ _ _ _)) z)
     (op n x p) (cₙ (suc n) x ε (𝕡⊆ s n x p)))

  (Seq⊆→.FromIntersection.∩$-lem {A = ℝ} {s = s} r isSetℝ P s⊇P
     x x∈)



restrSq : ∀ n → Lipschitz-ℚ→ℚ-restr (fromNat (suc n))
                  ((2 ℚ₊· fromNat (suc n)))
                  λ x → x ℚ.· x

restrSq n q r x x₁ ε x₂ =

  subst (ℚ._< 2 ℚ.· fst (fromNat (suc n)) ℚ.· fst ε)
    (ℚ.abs·abs (q ℚ.+ r) (q ℚ.- r) ∙
      cong {x = ((q ℚ.+ r) ℚ.· (q ℚ.- r))}
            {y = ((q ℚ.· q) ℚ.- (r ℚ.· r))}
            ℚ.abs ℚ!!) z

 where
  zz : ℚ.abs (q ℚ.+ r) ℚ.< 2 ℚ.· fst (fromNat (suc n))
  zz = subst (ℚ.abs (q ℚ.+ r) ℚ.<_)
           ℚ!
          (ℚ.isTrans≤< _ _ _ (ℚ.abs+≤abs+abs q r)
              ((ℚ.<Monotone+ _ _ _ _ x x₁ )))

  z : ℚ.abs (q ℚ.+ r) ℚ.· ℚ.abs (q ℚ.- r) ℚ.<
        2 ℚ.· fst (fromNat (suc n)) ℚ.· fst ε
  z = ℚ.<Monotone·-onPos _ _ _ _
      zz x₂ (ℚ.0≤abs (q ℚ.+ r)) ((ℚ.0≤abs (q ℚ.- r)))






clampedSq : ∀ (n : ℕ) → Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (2 ℚ₊· fromNat (suc n)))
clampedSq n =
  let ex = Lipschitz-ℚ→ℚ-extend _
             (((2 ℚ₊· fromNat (suc n)))) (λ x → x ℚ.· x) (ℚ.[ (1 , 4) ] , _) (ℚ.<Δ n) (restrSq n)
  in fromLipschitz (((2 ℚ₊· fromNat (suc n)))) (_ , Lipschitz-rat∘ ((2 ℚ₊· fromNat (suc n)))
   (((λ x → x ℚ.· x) ∘
       ℚ.clamp (ℚ.- ([ pos (suc n) , 1 ] ℚ.- [ 1 , 4 ]))
       ([ pos (suc n) , 1 ] ℚ.- [ 1 , 4 ]))) ex)

sqSeq→ : Seq⊆→ ℝ Seq⊆-abs<N
sqSeq→ .Seq⊆→.fun x n _ = fst (clampedSq (suc n)) x
sqSeq→ .Seq⊆→.fun⊆ x n m x∈ x∈' n<m =
  ≡ContinuousWithPred (ointervalℙ _ _) (ointervalℙ _ _)
    (openIintervalℙ _ _) (openIintervalℙ _ _)
   (λ x _ → fst (clampedSq (suc n)) x) (λ x _ → fst (clampedSq (suc m)) x) 
   (AsContinuousWithPred (ointervalℙ (fromNeg (suc n)) (fromNat (suc n)))
     _ ((Lipschitz→IsContinuous ((2 ℚ₊· fromNat (suc (suc n))))
     ((fst (clampedSq (suc n)))) ((snd (clampedSq (suc n)))))))
   (AsContinuousWithPred (ointervalℙ (fromNeg (suc m)) (fromNat (suc m)))
    _ ((Lipschitz→IsContinuous ((2 ℚ₊· fromNat (suc (suc m))))
        ((fst (clampedSq (suc m)))) ((snd (clampedSq (suc m)))))))
   (λ r r∈ r∈' →
      let Q  = ([ pos (suc (suc n)) , 1 ] ℚ.- [ 1 , 4 ])
          Q' = ([ pos (suc (suc m)) , 1 ] ℚ.- [ 1 , 4 ])
          Q'<Q : Q ℚ.≤ Q'
          Q'<Q = ℚ.≤-+o [ pos (suc (suc n)) , 1 ] [ pos (suc (suc m)) , 1 ] (ℚ.- [ 1 , 4 ])
                 (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→≤ (ℕ.≤-k+ {k = 2} (ℕ.<-weaken n<m))) )
          sn≤Q : [ pos (suc n) / 1 ] ℚ.≤ Q
          sn≤Q = ℚ.inj (3 , ℤ!)
      in cong {x = ℚ.clamp (ℚ.- Q) Q r} {y = ℚ.clamp (ℚ.- Q') Q' r}
        (λ x → rat (x ℚ.· x))
      (sym (ℚ.clamp-contained-agree (ℚ.- Q') Q' (ℚ.- Q) Q
        r (ℚ.minus-≤ _ _ Q'<Q) Q'<Q
         (∈intervalℙ→∈ℚintervalℙ (ℚ.- Q) Q r (ontervalℙ⊂intervalℙ (rat r)
          (ointervalℙ⊆ointervalℙ
           (isTrans≤≡ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.minus-≤ _ _ sn≤Q)) (cong rat ℚ!))
           (≤ℚ→≤ᵣ _ _ sn≤Q)
           (rat r) r∈)))))) 
   x x∈ x∈'
    

infixl 7 _·ᵣ_

opaque

 open Seq⊆→.FromIntersection sqSeq→ isSetℝ ℝU Seq⊆-abs<N-s⊇-⊤Pred
 
 sqᵣ : ℝ → ℝ
 sqᵣ x = ∩$ x _
  
  

 IsContinuousSqᵣ : IsContinuous sqᵣ
 IsContinuousSqᵣ = contDropPred sqᵣ
   (∩$-cont ⊤Pred Seq⊆-abs<N (λ _ → openIintervalℙ _ _) sqSeq→ Seq⊆-abs<N-s⊇-⊤Pred
    λ n → AsContinuousWithPred (ointervalℙ (fromNeg (suc n)) (fromNat (suc n)))
         (flip (λ x n₁ → fst (clampedSq (suc n₁)) x) n)
          (Lipschitz→IsContinuous (2 ℚ₊· fromNat (suc (suc n)))
           (fst (clampedSq (suc n))) (snd (clampedSq (suc n))))) 
 




-- open ℚ.HLP


-- HoTT (11.3.46)


 /2ᵣ-L : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ ([ 1 / 2 ] , _))
 /2ᵣ-L = fromLipschitz ([ 1 / 2 ] , _)
   (_ , Lipschitz-rat∘ ([ 1 / 2 ] , _) (ℚ._· [ 1 / 2 ])
    λ q r ε x →
      subst (ℚ._< ([ 1 / 2 ]) ℚ.· (fst ε))
       (sym (ℚ.pos·abs [ 1 / 2 ] (q ℚ.- r)
        (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 1 / 2 ]} _ ))
        ∙ cong {x = ([ 1 / 2 ] ℚ.· (q ℚ.- r))}
               {y = ((q ℚ.· [ 1 / 2 ]) ℚ.- (r ℚ.· [ 1 / 2 ]))}
               ℚ.abs ℚ!!)
       (ℚ.<-o· (ℚ.abs (q ℚ.- r)) (fst ε) [ 1 / 2 ]
        ((𝟚.toWitness {Q = ℚ.<Dec 0 [ 1 / 2 ]} _ )) x))

 /2ᵣ : ℝ → ℝ
 /2ᵣ = fst /2ᵣ-L


 sqᵣ-rat : ∀ r → sqᵣ (rat r) ≡ rat (r ℚ.· r)
 sqᵣ-rat r = PT.rec (isSetℝ _ _)
  (λ (n , (r∈ , p)) →
   let sn≤Q = ℚ.inj (3 , ℤ!)
       pp = (cong (λ x → x ℚ.· x) ((ℚ.∈ℚintervalℙ→clam≡
            ((ℚ.- ([ pos (suc (suc n)) , 1 ] ℚ.- [ 1 , 4 ])))
            (([ pos (suc (suc n)) , 1 ] ℚ.- [ 1 , 4 ])) r
             (∈intervalℙ→∈ℚintervalℙ _ _ r (
               intervalℙ⊆intervalℙ
                 (isTrans≤≡ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.minus-≤ _ _ sn≤Q)) (cong rat ℚ!))
                 (≤ℚ→≤ᵣ _ _ sn≤Q) _
                (ointervalℙ⊆intervalℙ _ _ _ r∈) )))))
   in p ∙ cong rat (sym pp))
   (∩$-lem (rat r) _)


 IsContinuous/2ᵣ : IsContinuous /2ᵣ
 IsContinuous/2ᵣ = Lipschitz→IsContinuous ([ 1 / 2 ] , _) /2ᵣ (snd /2ᵣ-L)







 _·ᵣ_ : ℝ → ℝ → ℝ
 u ·ᵣ v = /2ᵣ ((sqᵣ (u +ᵣ v)) +ᵣ (-ᵣ (sqᵣ u +ᵣ sqᵣ v)))

 ·ᵣ-impl : ∀ u v → u ·ᵣ v ≡ /2ᵣ ((sqᵣ (u +ᵣ v)) +ᵣ (-ᵣ (sqᵣ u +ᵣ sqᵣ v)))
 ·ᵣ-impl _ _ = refl

  
 rat·ᵣrat : ∀ r q → rat (r ℚ.· q) ≡ rat r ·ᵣ rat q
 rat·ᵣrat r q = cong rat ℚ!!
   ∙ cong /2ᵣ
     (sym (-ᵣ-rat₂ _ _) ∙ cong₂ _-ᵣ_ (sym (sqᵣ-rat (r ℚ.+ q)) ∙ cong sqᵣ (sym (+ᵣ-rat r q)))
      (sym (+ᵣ-rat _ _) ∙ cong₂ _+ᵣ_ (sym (sqᵣ-rat r)) (sym (sqᵣ-rat q))))


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
                   cong rat (ℚ.·Assoc q q' q'')
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

opaque
 unfolding maxᵣ
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
          y) x
      
opaque

 unfolding _·ᵣ_ _+ᵣ_

 cont₂·ᵣWP : ∀ P f g
   → (IsContinuousWithPred P f)
   → (IsContinuousWithPred P g)
   → IsContinuousWithPred P (λ x x∈ → f x x∈ ·ᵣ g x x∈)
 cont₂·ᵣWP P f g fC gC = 
   IsContinuousWP∘' P _
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
                         cong rat (sym (ℚ.abs'·abs' x' y')) ∙∙ rat·ᵣrat _ _) x


IsContinuous₂·ᵣ :  IsContinuous₂ _·ᵣ_
IsContinuous₂·ᵣ = IsContinuous·ᵣL , IsContinuous·ᵣR
