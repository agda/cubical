{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.NthRoot where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos; ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

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
open import Cubical.HITs.CauchyReals.Bisect




sqrRestr< : ∀ n → (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) ℚ.< (fromNat (2 ℕ.+ n))
sqrRestr< n =
  (ℚ.isTrans< (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) 1 (fromNat (2 ℕ.+ n))
               (fst (ℚ.invℚ₊-<-invℚ₊ 1 _)
                 (ℚ.<ℤ→<ℚ 1 _ (ℤ.suc-≤-suc (ℤ.suc-≤-suc (ℤ.zero-≤pos {n})))))
               (ℚ.<ℤ→<ℚ 1 _
               (ℤ.suc-≤-suc (ℤ.suc-≤-suc (ℤ.zero-≤pos {n})))))

module NthRoot (m : ℕ) where


 module _ (n : ℕ) where


  open bⁿ-aⁿ m hiding (n)


  A B : ℝ
  A = rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
  B = (fromNat (2 ℕ.+ n))
  0<A = (snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))))
  0<B = (snd (ℚ₊→ℝ₊ (fromNat (2 ℕ.+ n))))
  A<B : A <ᵣ B
  A<B = <ℚ→<ᵣ _ _ (sqrRestr< n)



  L = (((fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m))
      ℚ₊· (fromNat (2 ℕ.+ m)))

  K = (fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m)

  incrF : isIncrasingℙ
   (ℚintervalℙ (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
               (fromNat (2 ℕ.+ n))) (λ x _ → x ℚ^ⁿ (2 ℕ.+ m))
  incrF  x x∈ y y∈ =
    ℚ^ⁿ-StrictMonotone (2 ℕ.+ m)
     (ℕ.≤-suc (ℕ.suc-≤-suc (ℕ.zero-≤ {m})))
     (ℚ.isTrans≤ 0 (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
          x (ℚ.0≤ℚ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))) (fst x∈))
     (ℚ.isTrans≤ 0 (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
          y (ℚ.0≤ℚ₊ (invℚ₊ (fromNat (2 ℕ.+ n)))) (fst y∈))

  1/K<L : fst (invℚ₊ K) ℚ.< fst L
  1/K<L = ℚ.isTrans≤< _ 1 _
    (subst (ℚ._≤ 1) (sym (ℚ.invℚ₊-ℚ^ⁿ _ _))
      (ℚ.x^ⁿ≤1 _ _ ℤ.zero-≤pos
       (fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (2 ℕ.+ n)))
        (ℚ.≤ℤ→≤ℚ _ _ (ℤ.suc-≤-suc ℤ.zero-≤pos)))))
         (ℚ.isTrans≤< _ _ _
           (ℚ.1≤x^ⁿ (fromNat (2 ℕ.+ n))
            (fromNat (1 ℕ.+ m)) (ℚ.≤ℤ→≤ℚ 1 _ (ℤ.suc-≤-suc ℤ.zero-≤pos)))
            (subst (ℚ._< fst L)

               (ℚ.·IdR _)
                 (ℚ.<-o· 1 (fromNat (2 ℕ.+ m))
                   _ (ℚ.0<ℚ₊ ((fromNat (2 ℕ.+ n)) ℚ₊^ⁿ (suc m)))
            ((ℚ.<ℤ→<ℚ 1 (ℤ.pos (suc (suc m)))
             ( ℤ.suc-≤-suc (ℤ.suc-≤-suc (ℤ.zero-≤pos {m})))))))
            )


  rootRest : IsBilipschitz
               (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
               (fromNat (2 ℕ.+ n))
               (sqrRestr< n)
               λ x _ → x ℚ^ⁿ (2 ℕ.+ m)
  rootRest .IsBilipschitz.incrF = incrF
  rootRest .IsBilipschitz.L = L
  rootRest .IsBilipschitz.K = K
  rootRest .IsBilipschitz.1/K≤L = ℚ.<Weaken≤ _ _ 1/K<L

  rootRest .IsBilipschitz.lipF =
    Lipschitz-ℚ→ℝℙ<→Lipschitz-ℚ→ℝℙ _ _ _
      λ q q∈ r r∈ r<q  →
       let 0<r : 0 <ᵣ (rat r)
           0<r = isTrans<≤ᵣ 0 A (rat r) 0<A (fst r∈)
           0<q : 0 <ᵣ (rat q)
           0<q = isTrans<ᵣ 0 (rat r) (rat q) 0<r (<ℚ→<ᵣ _ _ r<q)

           ineqL : (rat q ^ⁿ suc (suc m)) -ᵣ (rat r ^ⁿ suc (suc m))
                      ≤ᵣ rat ((fst L) ℚ.· (q ℚ.- r))

           ineqL =
             isTrans≡≤ᵣ _ _ _ (sym $
                  [b-a]·S≡bⁿ-aⁿ (rat r) (rat q)
                     0<r 0<q)
               (isTrans≤≡ᵣ _ _ _ (≤ᵣ-o·ᵣ _ _ _
                      (isTrans≤≡ᵣ _ _ _  (≤ℚ→≤ᵣ _ _  $ ℚ.<Weaken≤ _ _ (ℚ.<→<minus _ _ r<q))
                       (sym (-ᵣ-rat₂ _ _))) --
                    (isTrans≤≡ᵣ _ _ _
               (S≤Bⁿ·n (rat r) (rat q) 0<r 0<q A B 0<A
                     (isTrans≤<ᵣ _ _ _
                       (fst r∈ ) (<ℚ→<ᵣ _ _ r<q)) 0<B A<B
                  (snd q∈)
                  (<ℚ→<ᵣ _ _ r<q))
                      (sym ((rat·ᵣrat _ _
                        ∙ cong (_·ᵣ (rat ((fromNat (2 ℕ.+ m)))))
                          (sym (^ⁿ-ℚ^ⁿ _ _)))))
                          ))
                           (cong₂ _·ᵣ_ (-ᵣ-rat₂ _ _) refl ∙ (sym (rat·ᵣrat _ _) ∙ (cong rat (ℚ.·Comm _ _)))) --
                           )


       in isTrans≡≤ᵣ _ _ _ (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣPos _
            (<ℚ→<ᵣ _ _  (ℚ.<→<minus _ _ (incrF r
                     (∈intervalℙ→∈ℚintervalℙ _ _ _ r∈)
                     q
                     (∈intervalℙ→∈ℚintervalℙ _ _ _ q∈)
                     r<q)))
                 ∙ sym (-ᵣ-rat₂ _ _)  ∙ cong₂ _-ᵣ_
                   (sym (^ⁿ-ℚ^ⁿ _ _))
                   (sym (^ⁿ-ℚ^ⁿ _ _))) ineqL

  rootRest .IsBilipschitz.lip⁻¹F =
    Invlipschitz-ℚ→ℚℙ'<→Invlipschitz-ℚ→ℚℙ _ _ _
       λ q q∈ r r∈ r<q →
          let r∈' = (∈ℚintervalℙ→∈intervalℙ _ _ _ r∈)
              q∈' = (∈ℚintervalℙ→∈intervalℙ
                      (fst (invℚ₊ (fromNat (2 ℕ.+ n)))) _ _ q∈)
              0<r : 0 <ᵣ (rat r)
              0<r = isTrans<≤ᵣ 0 A (rat r) 0<A (fst r∈')
              0<q : 0 <ᵣ (rat q)
              0<q = isTrans<ᵣ 0 (rat r) (rat q) 0<r (<ℚ→<ᵣ _ _ r<q)

          in ℚ.x·invℚ₊y≤z→x≤y·z _ _ _ (≤ᵣ→≤ℚ _ _
                $ isTrans≡≤ᵣ _ _ _ (cong rat
                  (cong ((q ℚ.+ ℚ.- r) ℚ.·_)
                    (ℚ.invℚ₊-ℚ^ⁿ _ (suc m)) )
                  ∙ rat·ᵣrat _ _) $
                isTrans≤≡ᵣ _ _ _
                  (≤ᵣ-o·ᵣ _ _ _
                        (≤ℚ→≤ᵣ _ _  $ ℚ.<Weaken≤ _ _ (ℚ.<→<minus _ _ r<q))
                  (isTrans≡≤ᵣ _ _ _
                     (sym (^ⁿ-ℚ^ⁿ _ _))
                             (Aⁿ≤S (rat r) (rat q) 0<r 0<q
                              A B 0<A
                              (isTrans≤<ᵣ _ _ _
                                (fst r∈' ) (<ℚ→<ᵣ _ _ r<q))
                              0<B A<B
                             (snd q∈')
                             (<ℚ→<ᵣ _ _ r<q))
                             ))
                    (cong₂ _·ᵣ_ (sym (-ᵣ-rat₂ _ _)) refl ∙ [b-a]·S≡bⁿ-aⁿ (rat r) (rat q) 0<r 0<q
                       ∙
                      cong₂ _-ᵣ_ (^ⁿ-ℚ^ⁿ _ _) (^ⁿ-ℚ^ⁿ _ _)
                      ∙ -ᵣ-rat₂ _ _ ∙ cong rat (sym (ℚ.absPos _
                      (ℚ.<→<minus _ _ (incrF r r∈ q q∈ r<q))) ∙
                       ℚ.abs'≡abs _))
                       )




 loB hiB : ∀ n → ℚ
 loB n = (((fst (invℚ₊ (fromNat (2 ℕ.+ n))))) ℚ^ⁿ (2 ℕ.+ m))
 hiB n = ((fromNat (2 ℕ.+ n)) ℚ^ⁿ (2 ℕ.+ m))

 loB-mon : ∀ n → loB (suc n) ℚ.< loB n
 loB-mon n = (
     (ℚ^ⁿ-StrictMonotone (2 ℕ.+ m) (ℕ.suc-≤-suc ℕ.zero-≤)
      (ℚ.0≤ℚ₊ _) (ℚ.0≤ℚ₊ _)
      (fst (ℚ.invℚ₊-<-invℚ₊
    (fromNat (2 ℕ.+ n)) (fromNat (3 ℕ.+ n)))
      (ℚ.<ℤ→<ℚ _ _ ℤ.isRefl≤))))

 hiB-mon : ∀ n → hiB n ℚ.< hiB (suc n)
 hiB-mon n = ℚ^ⁿ-StrictMonotone (2 ℕ.+ m)
        (ℕ.suc-≤-suc ℕ.zero-≤) (ℚ.0≤ℚ₊ _) (ℚ.0≤ℚ₊ _)
      ((ℚ.<ℤ→<ℚ _ _ (ℤ.suc-≤-suc ℤ.isRefl≤)))

 rootSeq⊆ : Seq⊆
 rootSeq⊆ .Seq⊆.𝕡 n = intervalℙ
   (rat (loB n))
   (rat (hiB n))
 rootSeq⊆ .Seq⊆.𝕡⊆ n x (≤x , x≤) =
   isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (loB-mon n))) ≤x ,
   isTrans≤ᵣ _ _ _ x≤ (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (hiB-mon n)))




 f⊆ : (x : ℝ) (n n' : ℕ)
      (x∈ : x ∈ intervalℙ (rat (loB n)) (rat (hiB n)))
      (x∈' : x ∈ intervalℙ (rat (loB n')) (rat (hiB n'))) →
      n ℕ.< n' →
      IsBilipschitz.𝒇⁻¹ (rootRest n) x ≡
      IsBilipschitz.𝒇⁻¹ (rootRest n') x
 f⊆ x n n' x∈ x∈' n<n' =
   h

  where
  open IsBilipschitz
  ib = rootRest n
  ib' = rootRest n'

  -- zz' : {!!}
  -- zz' =

  𝒇'≡𝒇 : ∀ y → y ∈
      intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n)))))
            (rat (fromNat (2 ℕ.+ n)))
    → (𝒇 ib') y ≡ (𝒇 ib) y
  𝒇'≡𝒇 = elimInClampsᵣ _ _
    (≡Continuous _ _
       ((IsContinuous∘ _ _
             (Lipschitz→IsContinuous _ _ (snd (fl-ebl ib')))
             (IsContinuousClamp (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))) _)))
       (IsContinuous∘ _ _
             (Lipschitz→IsContinuous _ _ (snd (fl-ebl ib)))
              (IsContinuousClamp (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n))))) _))
      λ r → cong rat
           ( ((ebl ib') .snd .snd .snd  _
             (inClmp' r))

         ∙ sym
          (((ebl ib) .snd .snd .snd  _
        (clam∈ℚintervalℙ _ _ (ℚ.<Weaken≤ _ _ (sqrRestr< n)) r))))
        )
    where
    h = ℚ.≤ℤ→≤ℚ _ _ (ℤ.suc-≤-suc (ℤ.≤-suc (ℤ.ℕ≤→pos-≤-pos _ _ n<n')))
    inClmp' : ∀ r → ℚ.clamp (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
      [ pos (suc (suc n)) / 1+ 0 ] r
      ∈
      ℚintervalℙ (fst (invℚ₊ (ℚ.[ pos (suc (suc n')) , (1+ 0) ] , tt)))
      [ pos (suc (suc n')) / 1+ 0 ]
    inClmp' r =
       ℚ.isTrans≤
         (fst (invℚ₊ (ℚ.[ pos (suc (suc n')) , (1+ 0) ] , tt)))
         (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
         (ℚ.clamp (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ]
        , tt)))
      [ pos (suc (suc n)) / 1+ 0 ] r)
         ((fst (ℚ.invℚ₊-≤-invℚ₊
           ([ pos (suc (suc n)) / 1+ 0 ] , _)
           ([ pos (suc (suc n')) / 1+ 0 ] , _)) h))
          (ℚ.≤clamp (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
      [ pos (suc (suc n)) / 1+ 0 ] r (
        (ℚ.<Weaken≤
          (fst (invℚ₊ (fromNat (2 ℕ.+ n))))
          (fromNat (2 ℕ.+ n))

         (sqrRestr< n))))
       , ℚ.isTrans≤ _
            (ℚ.[ pos (suc (suc n)) , (1+ 0) ]) _
           (ℚ.clamp≤
             (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))
             _ r)
           h


  2+n≤ℚ2+n' = (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.<-weaken (ℕ.<-k+ n<n'))))

  x⁻¹∈ : 𝒇⁻¹ ib x ∈
            intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n')))))
            (rat (fromNat (2 ℕ.+ n')))
  x⁻¹∈ = (isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _
           (fst (ℚ.invℚ₊-≤-invℚ₊ (fromNat (2 ℕ.+ n)) (fromNat (2 ℕ.+ n')))
        2+n≤ℚ2+n'))
       (fst x∈*))
    , (isTrans≤ᵣ _ _ _ (snd x∈*) (≤ℚ→≤ᵣ _ _ 2+n≤ℚ2+n'))

   where
   x∈* : 𝒇⁻¹ ib x ∈
            intervalℙ (rat (fst (invℚ₊ (fromNat (2 ℕ.+ n)))))
            (rat (fromNat (2 ℕ.+ n)))
   x∈* = 𝒇⁻¹∈ ib x x∈

  h : 𝒇⁻¹ ib x ≡ 𝒇⁻¹ ib' x
  h = sym (𝒇⁻¹∘𝒇 ib' (𝒇⁻¹ ib x) x⁻¹∈ )
    ∙ cong (𝒇⁻¹ ib') (𝒇'≡𝒇 (𝒇⁻¹ ib x) (𝒇⁻¹∈ ib x x∈)
       ∙ 𝒇∘𝒇⁻¹ ib _ x∈ )



 rootSeq⊆→ : Seq⊆→ ℝ rootSeq⊆
 rootSeq⊆→ .Seq⊆→.fun x n _ = IsBilipschitz.𝒇⁻¹ (rootRest n) x
 rootSeq⊆→ .Seq⊆→.fun⊆ = f⊆

 getBounds : ∀ x → 0 <ᵣ x → Σ ℚ (λ q → (0 <ᵣ rat q) × (rat q <ᵣ x)) →
      Σ[ M ∈ ℕ₊₁ ] (absᵣ x <ᵣ fromNat (ℕ₊₁→ℕ M)) →
      Σ[ N ∈ ℕ   ] (x ∈ intervalℙ (rat (loB N)) (rat (hiB N)))
 getBounds x 0<x (q , 0<q , q<x) ((1+ M) , x<1+M ) =
    𝑵 , loB≤x , x≤hiB
    -- 𝑵 ,
   -- (loB≤x , x≤hiB)
  where

  q₊ : ℚ₊
  q₊ = (q , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<q))

  flr-q = ℚ.floor-fracℚ₊ (invℚ₊ q₊)

  lo𝑵 = suc (fst (fst flr-q))
  hi𝑵 = M

  𝑵 = ℕ.max lo𝑵 hi𝑵

  loB≤q : loB 𝑵 ℚ.≤ q
  loB≤q = subst2 (ℚ._≤_)
     (ℚ.invℚ₊-ℚ^ⁿ _ _) (ℚ.invℚ₊-invol q₊)
     (fst (ℚ.invℚ₊-≤-invℚ₊ _ _)
      (ℚ.isTrans≤ (fst (ℚ.invℚ₊ q₊)) _ _
        (ℚ.<Weaken≤ _ _ (ℚ.≤floor-fracℚ₊ (invℚ₊ q₊))) -- (ℚ.≤floor-fracℚ₊ (invℚ₊ q₊))
         (ℚ.isTrans≤ _ _ _
           (ℚ.isTrans≤ _ _ _ (ℚ.≤ℤ→≤ℚ _ _
             (ℤ.ℕ≤→pos-≤-pos _ _
                 (subst (ℕ._≤ (lo𝑵 ^ suc (suc m)))
                   (ℕ.·-identityʳ lo𝑵)
                    ((ℕ.^-monotone lo𝑵 0 (suc m) ℕ.zero-≤)))))
             (ℚ.≡Weaken≤ (fromNat (lo𝑵 ^ suc (suc m)))
               ((fromNat lo𝑵 ℚ^ⁿ (2 ℕ.+ m)))
                (sym ((ℚ.fromNat-^ lo𝑵 (suc (suc m)))))))
           (ℚ^ⁿ-Monotone {fromNat lo𝑵} (suc (suc m))
             (ℚ.≤ℤ→≤ℚ _ _ ℤ.zero-≤pos)
             (ℚ.≤ℤ→≤ℚ _ _ ℤ.zero-≤pos)
             (((ℚ.≤ℤ→≤ℚ _ _
          (ℤ.ℕ≤→pos-≤-pos _ _
          (ℕ.≤-trans (ℕ.≤-suc (ℕ.≤-suc ℕ.≤-refl))
           (ℕ.left-≤-max {suc (suc lo𝑵)} {suc (suc hi𝑵)}))))))))
          ))

  loB≤x : rat (loB 𝑵) ≤ᵣ x
  loB≤x = isTrans≤ᵣ _ _ _
    (≤ℚ→≤ᵣ _ _ loB≤q)
      (<ᵣWeaken≤ᵣ _ _ q<x)

  1+M≤hiB : fromNat (suc M) ℚ.≤ (hiB M)
  1+M≤hiB =
   subst (fromNat (suc M) ℚ.≤_) (sym (ℚ.fromNat-^ _ _))
    ((ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
      (ℕ.≤-trans (ℕ.≤-suc ℕ.≤-refl) (subst (ℕ._≤ (suc (suc M) ^ suc (suc m)))
          (sym (cong (suc ∘ suc) (sym (·-identityʳ M))))
           (ℕ.^-monotone (suc (suc M)) 0 (suc m) ℕ.zero-≤ )))
      )))


  x≤hiB : x ≤ᵣ rat (hiB 𝑵)
  x≤hiB =
   isTrans≡≤ᵣ _ _ _  (sym (absᵣPos _ 0<x))
      (isTrans≤ᵣ _ _ _
       (<ᵣWeaken≤ᵣ _ _ x<1+M)
         ((≤ℚ→≤ᵣ _ _ (ℚ.isTrans≤ (fromNat (suc M)) _ _ 1+M≤hiB
           ((ℚ^ⁿ-Monotone (suc (suc m))
              (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.zero-≤))
              (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.zero-≤))
            (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
             ((ℕ.right-≤-max {suc (suc hi𝑵)} {suc (suc lo𝑵)})) ))
             )))
             ))

             )

 ℝ₊⊆rootSeq : rootSeq⊆ Seq⊆.s⊇ (λ x → (0 <ᵣ x ) , isProp<ᵣ _ _)
 ℝ₊⊆rootSeq x 0<x =
   PT.map2
     (getBounds x 0<x)
      (denseℚinℝ _ _ 0<x)
      (getClamps x)


 0<root : (x : ℝ) (n : ℕ)
     (x∈ : x ∈ intervalℙ (rat (loB n)) (rat (hiB n))) →
     rat [ pos 0 / 1+ 0 ] <ᵣ IsBilipschitz.𝒇⁻¹ (rootRest n) x
 0<root x n x∈ =
   isTrans<≤ᵣ _ _ _
     (<ℚ→<ᵣ _ _ (ℚ.0<ℚ₊ (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt))))
     (fst (IsBilipschitz.𝒇⁻¹∈ (rootRest n) x x∈))


 open Seq⊆→.FromIntersection rootSeq⊆→ isSetℝ (λ x → (0 <ᵣ x ) , isProp<ᵣ _ _) ℝ₊⊆rootSeq public


 𝒇=f : ∀ n x → x ∈ intervalℙ
                     (rat (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt))))
                     (rat (fromNat (2 ℕ.+ n)))  →
          (x ^ⁿ (suc (suc m))) ≡ fst (IsBilipschitz.fl-ebl (rootRest n)) x
 𝒇=f n = elimInClampsᵣ (rat (fst (invℚ₊ (ℚ.[ pos (suc (suc n)) , (1+ 0) ] , tt)))) (rat _)
  (≡Continuous _ _
       (IsContinuous∘ _ _ (IsContinuous^ⁿ (suc (suc m)) ) (IsContinuousClamp (rat _) (rat _)))
       (IsContinuous∘ _ _ (IsBilipschitz.isCont𝒇 (rootRest n)) (IsContinuousClamp (rat _) (rat _)))
      λ r → ^ⁿ-ℚ^ⁿ (suc (suc m)) _ ∙ cong rat (sym (IsBilipschitz.ebl (rootRest n) .snd .snd .snd
              (ℚ.clamp _ _ r) (clam∈ℚintervalℙ _ _
               (ℚ.<Weaken≤ _ _ (sqrRestr< n)) r))))



 bounds⊂ : (n : ℕ) (x : ℝ) →
      x ∈ (λ z → Seq⊆.𝕡 rootSeq⊆ n z) →
      ∃-syntax ℚ₊
      (λ δ →
         (y : ℝ) → x ∼[ δ ] y → y ∈ (λ z → Seq⊆.𝕡 rootSeq⊆ (suc n) z))
 bounds⊂ n x (lo<x , x<hi)  = ∣ δ
         , (λ y → (λ abs< →
             let u = isTrans≤ᵣ (x -ᵣ y) _
                        (rat (loB n ℚ.- loB (suc n) )) (≤absᵣ (x -ᵣ y))
                        (<ᵣWeaken≤ᵣ (absᵣ (x -ᵣ y)) _
                           (isTrans<≤ᵣ _ (rat (fst δ)) _ abs<
                       (≤ℚ→≤ᵣ _ _ (ℚ.min≤ _ _))))
                 v =
                   isTrans≤ᵣ (y -ᵣ x) _
                        (rat (hiB (suc n) ℚ.- hiB n )) (≤absᵣ (y -ᵣ x))
                      (isTrans≡≤ᵣ _ _ _ (minusComm-absᵣ _ _)
                        (<ᵣWeaken≤ᵣ (absᵣ (x -ᵣ y)) _ (isTrans<≤ᵣ _ _ _ abs<
                       (≤ℚ→≤ᵣ _ _ (ℚ.min≤' _ _)))))
             in  subst2 _≤ᵣ_
                    (L𝐑.lem--079 {rat (loB n)})
                     L𝐑.lem--079
                    (≤ᵣMonotone+ᵣ _ _ _ _
                       lo<x (-ᵣ≤ᵣ _ _ (isTrans≤≡ᵣ _ _ _ u (sym (-ᵣ-rat₂ _ _) ))))
                    , subst2 _≤ᵣ_
                          (𝐑'.minusPlus _ x)
                          (𝐑'.minusPlus (rat (hiB (suc n))) (rat (hiB n)))
                          (isTrans≤≡ᵣ _ _ _ (≤ᵣMonotone+ᵣ _ _ _ _
                             v x<hi) (cong (_+ᵣ rat (hiB n)) (sym (-ᵣ-rat₂ _ _))))

                             )
             ∘ fst (∼≃abs<ε _ _ _)) ∣₁
  where
  δ = ℚ.min₊ (ℚ.<→ℚ₊ _ _ (loB-mon n))
                        (ℚ.<→ℚ₊ _ _ (hiB-mon n))
 opaque
  nth-root : ℝ₊ → ℝ₊
  nth-root (x , 0<x) =
      ∩$ x 0<x
    , ∩$-elimProp x 0<x {B = λ y → 0 <ᵣ y} (λ _ → isProp<ᵣ _ _)
       (0<root x)

  ^ⁿ∘ⁿ√ : ∀ x 0<x → (fst (nth-root (x , 0<x)) ^ⁿ (2 ℕ.+ m)) ≡ x
  ^ⁿ∘ⁿ√ x 0<x = ∩$-elimProp x 0<x
    {B = λ a → (a ^ⁿ (2 ℕ.+ m)) ≡ x}
    (λ _ → isSetℝ _ _)
      λ n x∈ →
           𝒇=f _ _ (IsBilipschitz.𝒇⁻¹∈ (rootRest n) x x∈)
        ∙ IsBilipschitz.𝒇∘𝒇⁻¹ (rootRest n) x x∈

  ⁿ√∘^ⁿ : ∀ x 0<x → fst (nth-root (x  ^ⁿ (2 ℕ.+ m) , 0<x^ⁿ x (2 ℕ.+ m) 0<x)) ≡ x
  ⁿ√∘^ⁿ x 0<x = ∩$-elimProp (x  ^ⁿ (2 ℕ.+ m)) (0<x^ⁿ x (2 ℕ.+ m) 0<x)
    {B = λ a → a ≡ x}
    (λ _ → isSetℝ _ _)
     λ n x∈' →
      let 0<n = ℕ.suc-≤-suc ℕ.zero-≤
          zzs : rat (fst (invℚ₊ (_/_.[ pos (suc (suc n)) , (1+ 0) ] , tt))) ≤ᵣ x
          zzs = (^ⁿMonotone⁻¹ (suc (suc m)) 0<n
                 (0<A n) 0<x (isTrans≡≤ᵣ _ _ _ (^ⁿ-ℚ^ⁿ _ _) (fst x∈')))

          zzss : x ≤ᵣ rat [ pos (suc (suc n)) / 1+ 0 ]
          zzss = (^ⁿMonotone⁻¹ (suc (suc m)) 0<n 0<x (0<B n)
                     (isTrans≤≡ᵣ _ _ _ (snd x∈') (sym (^ⁿ-ℚ^ⁿ _ _))))
          x∈ : (rat (fst (invℚ₊ (_/_.[ pos (suc (suc n)) , (1+ 0) ] , tt))) ≤ᵣ x) ×
               (x ≤ᵣ rat (fromNat (2 ℕ.+ n)))
          x∈ =  zzs , zzss




      in cong (fst (IsBilipschitz.f⁻¹R-L (rootRest n)))
                 (𝒇=f n x x∈)
                ∙ IsBilipschitz.𝒇⁻¹∘𝒇 (rootRest n) x x∈


  nth-root-cont : IsContinuousWithPred
          (λ x → _ , isProp<ᵣ _ _) (curry (fst ∘ nth-root))
  nth-root-cont = ∩$-cont' _ _
     bounds⊂ _ _
      λ n → AsContinuousWithPred _ _
               (IsBilipschitz.isCont𝒇⁻¹ (rootRest n))

  ℚApproxℙ-nth-root : ℚApproxℙ'
                          (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                          (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                          (curry (nth-root))
  ℚApproxℙ-nth-root q q∈ =
   let q₊ = (q , ℚ.<→0< _ (<ᵣ→<ℚ _ _ q∈))
       (m , q<m) = ℚ.ceilℚ₊ q₊
       (n' , q∈') = getBounds (rat q) q∈
          (fst (/2₊ q₊) ,
            snd (ℚ₊→ℝ₊ (/2₊ q₊))
              , <ℚ→<ᵣ _ _ (x/2<x q₊))
               (1+ (ℕ₊₁→ℕ m) , isTrans<ᵣ _ _ _
                   (isTrans≡<ᵣ _ _ _
                     (absᵣPos _ (snd (ℚ₊→ℝ₊ q₊)))
                     (<ℚ→<ᵣ _ _ q<m))
                   (<ℚ→<ᵣ _ _ (ℚ.<ℤ→<ℚ _ _
                     ℤ.isRefl≤)))
       (a , b , c , d) =
          ( (IsBilipschitz.ℚApproxℙ-𝒇⁻¹ (rootRest n')))
   in a q q∈' , (λ ε →
      isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (2 ℕ.+ _)))))
         (fst (b q q∈' ε))) , c q q∈' ,
      d q q∈'
      ∙ sym (∩$-∈ₙ (rat q) q∈ n' q∈')


 nth-pow-root-iso₊₂ : Iso ℝ₊ ℝ₊
 nth-pow-root-iso₊₂ .Iso.fun (x , 0<x) =
   (x ^ⁿ (2 ℕ.+ m)) , 0<x^ⁿ _ _ 0<x
 nth-pow-root-iso₊₂ .Iso.inv = nth-root
 nth-pow-root-iso₊₂ .Iso.rightInv =
   ℝ₊≡ ∘ uncurry ^ⁿ∘ⁿ√
 nth-pow-root-iso₊₂ .Iso.leftInv =
   ℝ₊≡ ∘ uncurry ⁿ√∘^ⁿ


root : ℕ₊₁ → ℝ₊ →  ℝ₊
root one x = x
root (2+ n) x = NthRoot.nth-root n x

ℚApproxℙ-root : ∀ n → ℚApproxℙ'
                        (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                        (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                        (curry ((root n)))
ℚApproxℙ-root one q q∈ = (λ _ → q) , (λ _ → q∈) , (λ _ _ → refl∼ _ _) , limConstRat _ _

ℚApproxℙ-root (2+ n) = NthRoot.ℚApproxℙ-nth-root n

IsContinuousRoot : ∀ n → IsContinuousWithPred
         (λ x → _ , isProp<ᵣ _ _)
         λ x 0<x → fst (root n (x , 0<x))
IsContinuousRoot one =
  AsContinuousWithPred _ _ IsContinuousId
IsContinuousRoot (2+ n) = NthRoot.nth-root-cont n


nth-pow-root-iso : ℕ₊₁ → Iso ℝ₊ ℝ₊
nth-pow-root-iso k .Iso.fun (x , 0<x) = (x ^ⁿ ℕ₊₁→ℕ k) , 0<x^ⁿ _ _ 0<x
nth-pow-root-iso k .Iso.inv = root k
nth-pow-root-iso one .Iso.rightInv _ = ℝ₊≡ (·IdL _)
nth-pow-root-iso (2+ n) .Iso.rightInv = Iso.rightInv
  (NthRoot.nth-pow-root-iso₊₂ n)
nth-pow-root-iso one .Iso.leftInv _ = ℝ₊≡ (·IdL _)
nth-pow-root-iso (2+ n) .Iso.leftInv = Iso.leftInv
  (NthRoot.nth-pow-root-iso₊₂ n)
