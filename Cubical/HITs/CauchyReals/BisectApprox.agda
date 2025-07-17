{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.BisectApprox where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
import Cubical.Functions.Logic as L
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

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
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationMore


fromLipshitzℚ→ℝℙ→Cont : ∀ L a b
                       → ∀ f
                       → Lipschitz-ℝ→ℝℙ L (ointervalℙ a b) f
                       → IsContinuousWithPred (ointervalℙ a b) f
fromLipshitzℚ→ℝℙ→Cont L a b f lipF u ε u∈P =
  ∣ ((ℚ.invℚ₊ L) ℚ₊· ε ) ,
    (λ v v∈P u∼v →
      subst∼ (ℚ.y·[x/y] L (fst ε))
        (lipF u u∈P v v∈P ((invℚ₊ L) ℚ₊· ε) u∼v)) ∣₁

fromLipshitzℚ→ℝℙ→Cont0< : ∀ L
                       → ∀ f
                       → Lipschitz-ℝ→ℝℙ L pred0< f
                       → IsContinuousWithPred pred0< f
fromLipshitzℚ→ℝℙ→Cont0< L f lipF u ε u∈P =
  ∣ ((ℚ.invℚ₊ L) ℚ₊· ε ) ,
    (λ v v∈P u∼v →
      subst∼ (ℚ.y·[x/y] L (fst ε))
        (lipF u u∈P v v∈P ((invℚ₊ L) ℚ₊· ε) u∼v)) ∣₁



[n/m]<1 : ∀ n m → ([ pos n / m ] ℚ.< 1) ≃ (n ℕ.< ℕ₊₁→ℕ m)
[n/m]<1 n m = subst2Equiv (ℤ._<_) (ℤ.·IdR _)
        (sym (ℤ.pos·pos _ _) ∙ cong pos (ℕ.·-identityˡ _))
         ∙ₑ ℤ.pos-<-pos≃ℕ< _ _

<^n' : ∀ N n (q : ℚ₊) → fst q ℚ.< 1 → N ℕ.< n →
        (fst q ℚ^ⁿ n) ℚ.< (fst q ℚ^ⁿ N)
<^n' N n q q<1 N<n =
  let z' = (^ℚ-StrictMonotoneR
           {ℚ₊→ℝ₊ (invℚ₊ q)}
             (<ℚ→<ᵣ _ _
               (fst (ℚ.invℚ₊-<-invℚ₊ q 1) q<1))
             (fromNat N) (fromNat n)
               (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos  _ _ N<n)))
      z = <ᵣ→<ℚ _ _ $ subst2 _<ᵣ_
          (^ⁿ-ℚ^ⁿ _ _ ∙ cong rat (sym (ℚ.invℚ₊-ℚ^ⁿ _ _)))
          (^ⁿ-ℚ^ⁿ _ _ ∙ cong rat (sym (ℚ.invℚ₊-ℚ^ⁿ _ _)))
           z'
  in invEq (ℚ.invℚ₊-<-invℚ₊ _ _) z


1/n-1/sn : ∀ n →  [ pos 1 / 1+ n ] ℚ.- [ pos 1 / 2+ n ] ≡
                  [ pos 1 / ((1+ n) ·₊₁ (2+ n)) ]
1/n-1/sn n = eq/ _ _ h

 where
 h : (ℚ.ℕ₊₁→ℤ (1 ·₊₁ (2+ n)) ℤ.- ℚ.ℕ₊₁→ℤ (1+ n))
         ℤ.· ℚ.ℕ₊₁→ℤ ((1+ n) ·₊₁ (2+ n)) ≡
      1 ℤ.· ℚ.ℕ₊₁→ℤ ((1+ n) ·₊₁ (1 ·₊₁ (2+ n)))
 h = cong₂ (λ u v → v ℤ.· ℚ.ℕ₊₁→ℤ ((1+ n) ·₊₁ u))
      (sym (·₊₁-identityˡ _))
      (cong ((ℤ._- ℚ.ℕ₊₁→ℤ (1+ n))) (cong ℚ.ℕ₊₁→ℤ (·₊₁-identityˡ _)
       ∙  ℤ.+Comm _ _)
       ∙ ℤ.plusMinus (ℚ.ℕ₊₁→ℤ (1+ n)) 1)


apartFrom-Invlipschitz-ℝ→ℝℙ : ∀ K P f →
    Invlipschitz-ℝ→ℝℙ K P f →
     (∀ u u∈ v v∈ → (ε : ℚ₊) →
         rat (fst (K ℚ₊· ε)) ≤ᵣ absᵣ (u -ᵣ v)   →
           rat (fst ε) ≤ᵣ absᵣ (f u u∈ -ᵣ f v v∈))
apartFrom-Invlipschitz-ℝ→ℝℙ K P f X u u∈ v v∈ ρ Y =
 let Δ = absᵣ (f u u∈ -ᵣ f v v∈)
 in x<y+δ→x≤y _ _ λ ε →
      PT.rec (isProp<ᵣ _ _) -- u ∼[ K ℚ₊· (q , ?3) ] v
        (λ (q , Δ<q , q<Δ+ε) →
          let 0<q = ℚ.<→0< _ (<ᵣ→<ℚ 0 q
                     (isTrans≤<ᵣ _ _ _
                       (0≤absᵣ _) Δ<q))
              zzz : (fst (K ℚ₊· ρ)) ℚ.< (fst (K ℚ₊· (q , 0<q)))
              zzz = <ᵣ→<ℚ _ _ $ isTrans≤<ᵣ _ _ _
                       Y
                       (fst (∼≃abs<ε _ _ _)
                      $ X u u∈ v v∈ (q , 0<q)
                       (invEq (∼≃abs<ε _ _ _)
                         Δ<q))
              zzz' = ℚ.<-·o-cancel _ _ _
                         (ℚ.0<ℚ₊ K)
                      (subst2 ℚ._<_ (ℚ.·Comm _ _) (ℚ.·Comm _ _)
                          zzz)
              zz : rat (fst ρ) <ᵣ Δ +ᵣ rat (fst ε)
              zz = isTrans<ᵣ _ _ _
                      (<ℚ→<ᵣ _ _ zzz')
                       q<Δ+ε
          in zz
          )
        ((denseℚinℝ Δ (Δ +ᵣ rat (fst (ε)))
             (≤Weaken<+ᵣ _ _ (ℚ₊→ℝ₊ (ε)) (≤ᵣ-refl _))))

a≤b-c⇒a+c≤b : ∀ a b c → a ≤ᵣ b -ᵣ c → a +ᵣ c ≤ᵣ b
a≤b-c⇒a+c≤b a b c p =
   subst ((a +ᵣ c) ≤ᵣ_)
        (L𝐑.lem--00 {b} {c})
     (≤ᵣ-+o _ _ c p)


1ℚ^ⁿ : ∀ a → 1 ℚ^ⁿ a ≡ 1
1ℚ^ⁿ zero = refl
1ℚ^ⁿ (suc a) = ℚ.·IdR _ ∙ 1ℚ^ⁿ a

ℚ^-· : ∀ x a b → ((x ℚ^ⁿ a) ℚ^ⁿ b) ≡ (x ℚ^ⁿ (a ℕ.· b))
ℚ^-· x a zero = cong (x ℚ^ⁿ_) (0≡m·0 a)
ℚ^-· x a (suc b) = cong (ℚ._· (x ℚ^ⁿ a))
     (ℚ^-· x a b) ∙
       (ℚ.·-ℚ^ⁿ (a ℕ.· b) a x)
      ∙ cong (x ℚ^ⁿ_) ((λ i → ℕ.+-comm (ℕ.·-comm a b i) a i) ∙
          ℕ.·-comm _ _)

¾ⁿ<ε : ∀ (ε : ℚ₊) → Σ[ n ∈ ℕ ] [ 3 / 4 ] ℚ^ⁿ n ℚ.< fst ε
¾ⁿ<ε ε =
  let (n , X) = 1/2ⁿ<ε ε
      ¾³≤½ = ℚ^ⁿ-Monotone
              {[ 3 / 4 ] ℚ^ⁿ 3} {[ 1 / 2 ]}
              n (ℚ.decℚ≤? {0} {[ 3 / 4 ] ℚ^ⁿ 3})
               (ℚ.decℚ≤? {0} {[ 1 / 2 ]} )
                 (ℚ.decℚ≤? {[ 3 / 4 ] ℚ^ⁿ 3} {[ 1 / 2 ]})
  in 3 ℕ.· n , ℚ.isTrans≤< _ _ _
    (ℚ.isTrans≤ _ _ _
      (ℚ.≡Weaken≤ _ _ (sym (ℚ^-· [ 3 / 4 ] 3 n)))
        ¾³≤½) X



map-fromCauchySequence'ℙ : ∀ L s ics P f → (Lipschitz-ℝ→ℝℙ L P f) →
   ∀ lim∈ →
   (s∈ : ∀ n → s n ∈ P) →
    Σ _ λ icsf →
       f (fromCauchySequence' s ics) lim∈ ≡
        fromCauchySequence' (λ n → f (s n) (s∈ n))
          icsf
map-fromCauchySequence'ℙ L s ics P f lf lim∈ s∈ =
  icsf , sym (fromCauchySequence'≡ _ _ _ h)


 where
 open ℚ.HLP

 icsf : IsCauchySequence' (λ n → f (s n) (s∈ n))
 icsf ε = map-snd
   (λ X m n <m <n →
      let z = X m n <m <n
          z' = lf (s n) (s∈ n) (s m) (s∈ m) (invℚ₊ L ℚ₊· ε)
                (invEq (∼≃abs<ε _ _ _) z)
       in fst (∼≃abs<ε _ _ ε) (subst∼ (ℚ.y·[x/y] L (fst ε)) z'))
   (ics (invℚ₊ L ℚ₊· ε))

 h : (ε : ℚ₊) →
       ∃-syntax ℕ
       (λ N →
          (n : ℕ) →
          N ℕ.< n →
          absᵣ (f (s n) (s∈ n)
            -ᵣ f (fromCauchySequence' s ics) lim∈) <ᵣ rat (fst ε))
 h ε =
   let (N , X) = ics ((invℚ₊ L ℚ₊· (/4₊ ε)))
       (N' , X') = icsf (/4₊ ε)
       midN = suc (ℕ.max N N')
       midV = f (s midN)

   in ∣ midN , (λ n midN<n →
        let 3ε/4<ε = subst (ℚ._< (fst ε))
                            (cong (fst (/4₊ ε) ℚ.+_)
                              (sym (ℚ.y·[x/y] L _)
                               ∙ cong (fst L ℚ.·_) (ℚ.·DistL+ _ _ _) ))

                               (distℚ<! ε [ ((ge[ ℚ.[ 1 / 4 ] ]) +ge
                                   (ge[ ℚ.[ 1 / 4 ] ] +ge ge[ ℚ.[ 1 / 4 ] ]))
                                   < ge1 ])
            z' = invEq (∼≃abs<ε _ _ (/4₊ ε)) (X' ((suc N')) n
                 (ℕ.<-trans (ℕ.suc-≤-suc ℕ.right-≤-max) midN<n)
                  ℕ.≤-refl )

            zzzz' =
                (𝕣-lim-self _ (fromCauchySequence'-isCA s ics)
                      ((invℚ₊ L ℚ₊· (/4₊ ε))) ( (invℚ₊ L ℚ₊· (/4₊ ε))))

        in fst (∼≃abs<ε _ _ ε)
             (∼-monotone< 3ε/4<ε
                (triangle∼ z' (lf _ _ _ _ _ zzzz')))) ∣₁

x+y≤x'-y'≃x+y'≤x'-y : ∀ x y x' y' →
       (x +ᵣ y ≤ᵣ x' -ᵣ y') ≃ (x +ᵣ y' ≤ᵣ x' -ᵣ y)
x+y≤x'-y'≃x+y'≤x'-y x y x' y' =
      subst2Equiv _≤ᵣ_
        (cong (x +ᵣ_) (sym L𝐑.lem--063) ∙
          +ᵣAssoc _ _ _ ∙ cong (_-ᵣ y') (+ᵣAssoc _ _ _))
        (cong (_-ᵣ y') (sym (𝐑'.minusPlus _ _)))
   ∙ₑ x+y≤z+y≃x≤z _ _ (-ᵣ y')
   ∙ₑ x+y≤z+y≃x≤z _ _ y

x+y<x'-y'≃x+y'<x'-y : ∀ x y x' y' →
       (x +ᵣ y <ᵣ x' -ᵣ y') ≃ (x +ᵣ y' <ᵣ x' -ᵣ y)
x+y<x'-y'≃x+y'<x'-y x y x' y' =
      subst2Equiv _<ᵣ_
        (cong (x +ᵣ_) (sym L𝐑.lem--063) ∙
          +ᵣAssoc _ _ _ ∙ cong (_-ᵣ y') (+ᵣAssoc _ _ _))
        (cong (_-ᵣ y') (sym (𝐑'.minusPlus _ _)))
   ∙ₑ x+y<z+y≃x<z _ _ (-ᵣ y')
   ∙ₑ x+y<z+y≃x<z _ _ y


1/m·1/n : ∀ {n m} → [ 1 / n ] ℚ.· [ 1 / m ] ≡ [ 1 / (n ·₊₁ m) ]
1/m·1/n = refl

invL→embed : ∀ a b (a≤b : rat a ≤ᵣ rat b) f (f∈ : ∀ x x∈ → f x x∈ ∈ intervalℙ
                         (f (rat a) ((≤ᵣ-refl _) , a≤b))
                         (f (rat b) (a≤b , ≤ᵣ-refl _)))
                K → Invlipschitz-ℝ→ℝℙ K (intervalℙ (rat a) (rat b)) f
               → isEmbedding {A = Σ _ _} {B = Σ _ (_∈ intervalℙ
                         (f (rat a) ((≤ᵣ-refl _) , a≤b))
                         (f (rat b) (a≤b , ≤ᵣ-refl _)))}
                  λ (x , x∈) → (f x x∈ , f∈ x x∈)
invL→embed a b a≤b f f∈ K il (x , x∈) (y , y∈) =
 snd (propBiimpl→Equiv (isSetΣ isSetℝ
   (isProp→isSet ∘ snd ∘ intervalℙ (rat a) (rat b) ) _ _)
   (isSetΣ isSetℝ (isProp→isSet ∘ snd ∘ intervalℙ _ _ ) _ _) _
     (Σ≡Prop (snd ∘ intervalℙ (rat a) (rat b)) ∘S fst (∼≃≡ _ _) ∘ (λ p ε →
        subst∼ (ℚ.y·[x/y] K (fst ε))
     (il x x∈ y y∈ ((invℚ₊ K) ℚ₊· ε) (p (invℚ₊ K ℚ₊· ε))))
      ∘S invEq (∼≃≡ _ _) ∘S cong fst))




module IsBilipschitz' (a b : ℚ)  (a<b : a ℚ.< b)
         (f : ∀ (x : ℝ) → x ∈ (intervalℙ (rat a) (rat b)) → ℝ)
         (fC : IsContinuousWithPred (intervalℙ (rat a) (rat b)) f)
          (incrF : isIncrasingℙᵣ (intervalℙ (rat a) (rat b)) f)
          (nondF : isNondecrasingℙᵣ (intervalℙ (rat a) (rat b)) f)
           where


 a∈ : rat a ∈ (intervalℙ (rat a) (rat b))

 a∈ = (≤ᵣ-refl (rat a) , <ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ a<b))
 b∈ : rat b ∈ (intervalℙ (rat a) (rat b))
 b∈ = (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ a<b) , ≤ᵣ-refl (rat b))

 fa = f (rat a) a∈
 fb = f (rat b) b∈

 f∈ : ∀ x x∈ → f x x∈ ∈ (intervalℙ fa fb)
 f∈ x x∈ =
   nondF (rat a) _ x x∈ (fst x∈) ,
    nondF x x∈  (rat b) _ (snd x∈)

 f' : ∀ x x∈ → Σ ℝ (_∈ intervalℙ fa fb)
 f' x x∈ = _ , f∈ x x∈

 fa<fb : fa <ᵣ fb
 fa<fb = incrF
   (rat a) a∈
   (rat b) b∈
   (<ℚ→<ᵣ _ _ a<b)

 a≤b = ℚ.<Weaken≤ _ _ a<b

 Δ₀ = b ℚ.- a
 Δ₀₊ = ℚ.<→ℚ₊ _ _ a<b


 fo : (x : ℝ) → x ∈ ointervalℙ (rat a) (rat b)
              → Σ ℝ (_∈ ointervalℙ fa fb)
 fo x (<x , x<)  = (f x (<ᵣWeaken≤ᵣ _ _ <x , <ᵣWeaken≤ᵣ _ _ x<))
         , (incrF (rat a) a∈  x (<ᵣWeaken≤ᵣ _ _ <x , <ᵣWeaken≤ᵣ _ _ x<) <x)
         , (incrF x (<ᵣWeaken≤ᵣ _ _ <x , <ᵣWeaken≤ᵣ _ _ x<) (rat b) b∈   x<)


 module Inv
    (approxF : ℚApproxℙ' (intervalℙ (rat a) (rat b)) (intervalℙ fa fb) f')
    (L K : ℚ₊)
    (lipF : Lipschitz-ℝ→ℝℙ L (intervalℙ (rat a) (rat b)) f)
    (1/K≤L : fst (invℚ₊ K) ℚ.≤ fst L)
    (lip⁻¹F : Invlipschitz-ℝ→ℝℙ K (intervalℙ (rat a) (rat b)) f)

   where

  fApart : ∀ x x∈ y y∈ → (ε : ℚ₊) → rat (fst (K ℚ₊· ε)) ≤ᵣ absᵣ (x -ᵣ y) →
                                    rat (fst ε) ≤ᵣ absᵣ (f x x∈ -ᵣ f y y∈)
  fApart = apartFrom-Invlipschitz-ℝ→ℝℙ
           K _ f lip⁻¹F

  invApart : ∀ x x∈ y y∈ → (ε : ℚ₊) →
         rat (fst (L ℚ₊· ε)) ≤ᵣ absᵣ (f x x∈ -ᵣ f y y∈)   →
           rat (fst ε) ≤ᵣ absᵣ (x -ᵣ y)
  invApart x x∈ y y∈ ρ z =
   let Δ = absᵣ (x -ᵣ y)
   in x<y+δ→x≤y _  _
       λ ε →
            PT.rec (isProp<ᵣ _ _)
        (λ (q , Δ<q , q<Δ+ε) →
           let z' : f x x∈ ∼[
                      L ℚ₊·
                      (q ,
                       ℚ.<→0< q
                       (<ᵣ→<ℚ [ pos 0 / 1 ] q
                        (isTrans≤<ᵣ 0 Δ (rat q) (0≤absᵣ (x -ᵣ y)) Δ<q)))
                      ] f y y∈
               z' = lipF x x∈ y y∈
                     (q , ℚ.<→0< _ (<ᵣ→<ℚ _ _
                       (isTrans≤<ᵣ _ _ _
                         (0≤absᵣ _) Δ<q)))
                    (invEq (∼≃abs<ε _ _ _) Δ<q )

               zz' = ℚ.<-·o-cancel _ _ _ (ℚ.0<ℚ₊ L)
                 (subst2 ℚ._<_ (ℚ.·Comm _ _) (ℚ.·Comm _ _)
                      (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _
                       z
                       (fst (∼≃abs<ε _ _ _) z'))))


           in isTrans<ᵣ _ _ _
                 (<ℚ→<ᵣ _ _ zz') q<Δ+ε
          )
        ((denseℚinℝ Δ (Δ +ᵣ rat (fst (ε)))
             (≤Weaken<+ᵣ _ _ (ℚ₊→ℝ₊ (ε)) (≤ᵣ-refl _))))

  invApart' : ∀ x x∈ y y∈ → (ε : ℚ₊) →
         rat (fst ε) ≤ᵣ absᵣ (f x x∈ -ᵣ f y y∈)   →
           rat (fst ((invℚ₊ L) ℚ₊· ε)) ≤ᵣ absᵣ (x -ᵣ y)
  invApart' x x∈ y y∈ ε z =
    invApart x x∈ y y∈ ((invℚ₊ L) ℚ₊· ε)
      (isTrans≡≤ᵣ _ _ _ (cong rat (ℚ.y·[x/y] L (fst ε) )) z)

  invMon : ∀ x x∈ y y∈ →
          f x x∈ <ᵣ f y y∈   →
           x <ᵣ y
  invMon x x∈ y y∈ fx<fy =
   PT.rec (isProp<ᵣ _ _)
      (λ (δ , X) →
         let z = isTrans<≤ᵣ _ _ _
                    (snd (ℚ₊→ℝ₊ ((invℚ₊ L) ℚ₊· δ)))
                    (invApart y y∈ x x∈  ((invℚ₊ L) ℚ₊· δ)
                      (isTrans≡≤ᵣ _ _ _
                         (cong rat (ℚ.y·[x/y] L (fst δ)))
                          (isTrans≤ᵣ _ _ _
                           (<ᵣWeaken≤ᵣ _ _ X) (≤absᵣ _))))
         in ⊎.rec (⊥.rec ∘ isAsym<ᵣ (f x x∈) (f y y∈) fx<fy
              ∘S incrF y y∈ x x∈ ) (idfun _)
              (invEq (＃≃0<dist _ _) z)
              )
     (<ᵣ→Δ _ _ fx<fy)

  isEmbed-fo : isEmbedding (uncurry fo)
  isEmbed-fo (x , x∈) (y , y∈) =
    snd (propBiimpl→Equiv (isSetΣ isSetℝ
    (isProp→isSet ∘ snd ∘ ointervalℙ (rat a) (rat b) ) _ _)
    (isSetΣ isSetℝ (isProp→isSet ∘ snd ∘ ointervalℙ _ _ ) _ _) _
      (Σ≡Prop (snd ∘ ointervalℙ (rat a) (rat b)) ∘S fst (∼≃≡ _ _) ∘ (λ p ε →
         subst∼ (ℚ.y·[x/y] K (fst ε))
      (lip⁻¹F x _ y _ ((invℚ₊ K) ℚ₊· ε) (p (invℚ₊ K ℚ₊· ε))))
       ∘S invEq (∼≃≡ _ _) ∘S cong fst))

  module _ (y : ℚ) (y∈ : rat y ∈ (intervalℙ fa fb))  where

   record Step (Δ : ℚ) : Type where
    field
     a' b' : ℚ
     a'<b' : a' ℚ.< b'
     b'-a'≤Δ : b' ℚ.- a' ℚ.≤ Δ
     a'∈ : a' ∈ ℚintervalℙ a b
     b'∈ : b' ∈ ℚintervalℙ a b
     a'≤ : f (rat a') (∈ℚintervalℙ→∈intervalℙ _ _ _ a'∈) ≤ᵣ rat y
     ≤b' : rat y ≤ᵣ f (rat b') (∈ℚintervalℙ→∈intervalℙ _ _ _ b'∈)

    a'≤b' : a' ℚ.≤ b'
    a'≤b' = ℚ.<Weaken≤ _ _ a'<b'
    mid : ℚ
    mid = b' ℚ.· [ 1 / 2 ] ℚ.+ a' ℚ.· [ 1 / 2 ]

    Δ₊ : ℚ₊
    Δ₊ = Δ , ℚ.<→0< _ (ℚ.isTrans<≤ 0 _ _ (ℚ.-< a' b' a'<b') b'-a'≤Δ)

    p = ℚ.<-·o _ _ [ 1 / 2 ] (ℚ.decℚ<? {0} {[ 1 / 2 ]}) a'<b'

    a'<mid : a' ℚ.< mid
    a'<mid = ℚ.isTrans≤< _ _ _
      (ℚ.≡Weaken≤ _ _ (sym (ℚ.·IdR a') ∙ cong (a' ℚ.·_) ℚ.decℚ? ∙
        ℚ.·DistL+ a' _ _))
      (ℚ.<-+o _ _ (a' ℚ.· [ 1 / 2 ]) p)

    mid<b' : mid ℚ.< b'
    mid<b' = ℚ.isTrans<≤ _ _ _
      (ℚ.<-o+ _ _ (b' ℚ.· [ 1 / 2 ]) p)
      ((ℚ.≡Weaken≤ _ _ ((sym (ℚ.·DistL+ b' _ _) ∙ cong (b' ℚ.·_) ℚ.decℚ? ∙
        ℚ.·IdR b'))))

    mid∈ : mid ∈ ℚintervalℙ a b
    mid∈ = ℚ.isTrans≤ _ _ _ (fst (a'∈)) (ℚ.<Weaken≤ _ _ a'<mid) ,
            ℚ.isTrans≤ _ _ _ (ℚ.<Weaken≤ _ _ mid<b') (snd b'∈)

    mid∈' = (∈ℚintervalℙ→∈intervalℙ _ _ _ mid∈)

    fMidᵣ = f (rat mid) mid∈'

    y-fa' : absᵣ (f (rat a') (∈ℚintervalℙ→∈intervalℙ _ _ _ a'∈) -ᵣ rat y)
            <ᵣ rat (fst L ℚ.· (2 ℚ.· Δ))
    y-fa' = isTrans≡<ᵣ _ _ _
       (minusComm-absᵣ _ _)
       (isTrans≤<ᵣ _ _ _
          (subst2 _≤ᵣ_
            ((sym (absᵣNonNeg _ (x≤y→0≤y-x _ _
               (a'≤)))))
            (sym (absᵣPos _ (x<y→0<y-x _ _
              (incrF _ _ _ _ (<ℚ→<ᵣ _ _ a'<b')))))
            (≤ᵣ-+o _ _ _ (≤b')))
         (fst (∼≃abs<ε _ _ _)
          ((lipF (rat b') (∈ℚintervalℙ→∈intervalℙ _ _ _ b'∈)
                  (rat a') (∈ℚintervalℙ→∈intervalℙ _ _ _ a'∈)

                 (2 ℚ₊· Δ₊)
                  (invEq (∼≃abs<ε _ _ _)
                   (isTrans≤<ᵣ _ _ _
                    (isTrans≡≤ᵣ _ _ _
                       (cong absᵣ (cong₂ _+ᵣ_ refl (-ᵣ-rat _)
                        ∙ +ᵣ-rat _ _ )  ∙ (absᵣPos _ (<ℚ→<ᵣ _ _ (ℚ.-< _ _ a'<b')))) --
                        (≤ℚ→≤ᵣ _ _ b'-a'≤Δ))
                        (<ℚ→<ᵣ _ _
                          (ℚ.isTrans≤< _ _ _
                            (ℚ.≡Weaken≤ _ _
                               (sym (ℚ.·IdL _)))

                           (ℚ.<-·o 1 2 _ (ℚ.0<ℚ₊ Δ₊) (ℚ.decℚ<?))))))))))

   record Step⊃Step {Δ ΔS : _} (s : Step Δ) (sS : Step ΔS) : Type where

    field
     a'≤a'S : Step.a' s ℚ.≤ Step.a' sS
     bS≤b' : Step.b' sS ℚ.≤ Step.b' s
     -- distA' : (Step.a' sS) ℚ.≤ Δ ℚ.· [ 1 / 2 ] ℚ.+ (Step.a' s)

   step0 : Step Δ₀
   step0 .Step.a' = a
   step0 .Step.b' = b
   step0 .Step.a'<b' = a<b
   step0 .Step.b'-a'≤Δ = ℚ.isRefl≤ _
   step0 .Step.a'∈ = ℚ.isRefl≤ _  , a≤b
   step0 .Step.b'∈ = a≤b , (ℚ.isRefl≤ _)
   step0 .Step.a'≤ =
         subst (_≤ᵣ _)
           (cong (f (rat a)) (snd (intervalℙ _ _ _) _ _)) ( (fst y∈))
   step0 .Step.≤b' =
         subst (_ ≤ᵣ_)
           (cong (f (rat b)) (snd (intervalℙ _ _ _) _ _)) ( (snd y∈))

   stepS' : ∀ Δ → (s : Step Δ) → Σ (Step (Δ ℚ.· [ 3 / 4 ])) (Step⊃Step s)
   stepS' Δ s = w (ℚ.Dichotomyℚ y fMid)
    where
    open Step s


    Δ₊* : ℚ₊
    Δ₊* = ℚ.<→ℚ₊ _ _ a'<b'

    Δ* : ℚ
    Δ* = fst Δ₊*


    Δ*≤Δ : Δ* ℚ.≤ Δ
    Δ*≤Δ = b'-a'≤Δ


    mid=b-Δ/2 : mid ≡ b' ℚ.- fst (/2₊ Δ₊*)
    mid=b-Δ/2 =
          cong₂ ℚ._+_
           (sym lem--063 ∙
            cong₂ ℚ._+_
             (ℚ.ε/2+ε/2≡ε _) refl)
          (cong (ℚ._· [ 1 / 2 ]) (sym (ℚ.-Invol _))
            ∙ sym (ℚ.·Assoc -1 _ _))
       ∙∙ sym (ℚ.+Assoc _ _ _)
       ∙∙ cong (ℚ._+_ b')
         (sym (ℚ.-Distr (b' ℚ.· [ 1 / 2 ])
            (ℚ.- a' ℚ.· [ 1 / 2 ]))
           ∙ cong ℚ.-_ (sym (ℚ.·DistR+ b' (ℚ.- a') [ 1 / 2 ])))


    Φ : ℚ₊
    Φ = /2₊ (invℚ₊ K ℚ₊· /4₊ Δ₊*)

    fMid = fst (approxF mid mid∈') Φ

    fMidDist : rat fMid ∼[ (invℚ₊ K ℚ₊· /4₊ Δ₊*) ] f (rat mid) mid∈'
    fMidDist =
      subst∼ (ℚ.ε/2+ε/2≡ε _) (subst (rat fMid ∼[ Φ ℚ₊+ Φ ]_)
                (snd (snd (snd (approxF mid mid∈'))))
                 (𝕣-lim-self _ _ Φ Φ))


    a'-mid≡Δ/2 : (mid ℚ.- a') ≡ Δ* ℚ.· [ 1 / 2 ]
    a'-mid≡Δ/2 =
       ((sym (ℚ.+Assoc _ _ _) ∙
          cong (b' ℚ.· [ 1 / 2 ] ℚ.+_)
           (cong (a' ℚ.· [ 1 / 2 ] ℚ.+_) (ℚ.·Comm -1 a')
            ∙ sym (ℚ.·DistL+ a' _ _) ∙
             ℚ.·Comm _ _ ∙
              sym (ℚ.·Assoc [ 1 / 2 ] -1 a') ∙  ℚ.·Comm [ 1 / 2 ] _)
           ∙ sym (ℚ.·DistR+ _ _ _)))

    w : (y ℚ.≤ fMid) ⊎ (fMid ℚ.< y) → Σ (Step (Δ ℚ.· [ 3 / 4 ]))
              (Step⊃Step s)
    w (inl x) = ww
     where

     ab-dist = ℚ.isTrans≤
      ((mid ℚ.+ (Δ* ℚ.· [ 1 / 4 ])) ℚ.- a') _ _
       (ℚ.≡Weaken≤ _ _
         (cong (ℚ._- a') (ℚ.+Comm _ _) ∙ sym (ℚ.+Assoc _ _ _)))
        ((ℚ.isTrans≤ _ _ _
          (ℚ.≤-o+ _ _ _ (ℚ.≡Weaken≤ _ _ a'-mid≡Δ/2))
            (ℚ.≡Weaken≤ _ _ (sym (ℚ.·DistL+ Δ* _ _) ∙
              cong (Δ* ℚ.·_) ℚ.decℚ?))))

     newb' = mid ℚ.+ (Δ* ℚ.· [ 1 / 4 ])


     newb'+Δ/4≡b' : newb' ℚ.+ (Δ* ℚ.· [ 1 / 4 ]) ≡ b'
     newb'+Δ/4≡b' = sym (ℚ.+Assoc _ _ _) ∙
       cong₂ ℚ._+_
         mid=b-Δ/2
         (cong fst (ℚ./4₊+/4₊≡/2₊ Δ₊*))
       ∙ lem--00

     y≤fnewb' : rat y ≤ᵣ f (rat newb') _
     y≤fnewb' =
      (isTrans≤ᵣ _ _ _
        (≤ℚ→≤ᵣ _ _ x) (isTrans≤ᵣ _ _ _
           (a-b≤c⇒a≤c+b _ _ _
             (isTrans≤ᵣ _ _ _ (≤absᵣ _ )
               (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _) fMidDist)))) mid-dist))
        where
         mid-dist : rat (fst (invℚ₊ K ℚ₊· /4₊ Δ₊*))
                      +ᵣ f (rat mid) mid∈' ≤ᵣ
                      f _ _
         mid-dist = a≤b-c⇒a+c≤b _ _ _ $ isTrans≤≡ᵣ _ _ _
          (apartFrom-Invlipschitz-ℝ→ℝℙ
           K _ f lip⁻¹F (rat newb')
             _
             (rat mid) mid∈'
             (invℚ₊ K ℚ₊· (/4₊ Δ₊*))
                (isTrans≤≡ᵣ _ _ _(≤ℚ→≤ᵣ _ _

                  (subst2 ℚ._≤_ (sym (ℚ.y·[x/y] K (fst (/4₊ Δ₊*))))
                    (cong ℚ.abs' (sym lem--063))
                  (ℚ.≤abs' _))
                  ) (cong rat (sym (ℚ.abs'≡abs _)) ∙ sym (absᵣ-rat _) ∙
                   cong absᵣ
                    (sym (-ᵣ-rat₂ _ _))))

                  )
              (absᵣPos _ (x<y→0<y-x _ _
                (incrF _ mid∈' _ _
                    (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' mid mid ((Δ₊* ℚ₊· ([ 1 / 4 ] , _))) (ℚ.isRefl≤ mid) )))))

     a'<newb' : a' ℚ.< newb'
     a'<newb' =  ℚ.isTrans≤< _ _ _
         (ℚ.≡Weaken≤ _ _ (sym (ℚ.+IdR _))) (ℚ.<Monotone+ _ _ 0 (Δ* ℚ.· [ 1 / 4 ])
              a'<mid (ℚ.0<ℚ₊ (Δ₊* ℚ₊· ([ 1 / 4 ] , _))))

     newb'≤b' : newb' ℚ.≤ b'
     newb'≤b' =
      subst (newb' ℚ.≤_) newb'+Δ/4≡b'
       (ℚ.≤+ℚ₊ _ _ (Δ₊* ℚ₊· _) (ℚ.isRefl≤ _))

     newb'∈ : newb' ∈ ℚintervalℙ a b
     newb'∈ = ℚ.isTrans≤ _ _ _
              (fst a'∈) (ℚ.<Weaken≤ _ _ a'<newb')
       , ℚ.isTrans≤ _ _ _ newb'≤b' (snd b'∈)


     ww : Σ (Step (Δ ℚ.· [ 3 / 4 ])) (Step⊃Step s)
     ww .fst .Step.a' = a'
     ww .fst .Step.b' = newb'
     ww .fst .Step.a'<b' = a'<newb'
     ww .fst .Step.b'-a'≤Δ = ℚ.isTrans≤
           _ _ _ ab-dist (ℚ.≤-·o Δ* Δ [ 3 / 4 ]
             (ℚ.<Weaken≤ 0 [ 3 / 4 ] (ℚ.0<pos 2 4)) Δ*≤Δ)
     ww .fst .Step.a'∈ = a'∈
     ww .fst .Step.b'∈ = newb'∈
     ww .fst .Step.a'≤ = a'≤
     ww .fst .Step.≤b' =  y≤fnewb'
     ww .snd .Step⊃Step.a'≤a'S = ℚ.isRefl≤ a'
     ww .snd .Step⊃Step.bS≤b' = newb'≤b'
    w (inr x) = ww
     where
     newa' = mid ℚ.- (Δ* ℚ.· [ 1 / 4 ])

     ≡newa' : a' ℚ.+ Δ* ℚ.· [ 1 / 4 ] ≡ newa'
     ≡newa' = (cong (a' ℚ.+_)
                     (cong (Δ* ℚ.·_) ℚ.decℚ? ∙ 𝐐'.·DistR- Δ* _ _)
                     ∙ ℚ.+Assoc _  _ _)
                  ∙ cong (ℚ._- (Δ* ℚ.· [ 1 / 4 ]))
                    (  ℚ.+Comm _ _
                     ∙∙ sym (cong (ℚ._+ a') a'-mid≡Δ/2)
                     ∙∙ 𝐐'.minusPlus _ _)


     newa'<b' : newa' ℚ.< b'
     newa'<b' = ℚ.isTrans<≤ _ _ _
        (ℚ.<Monotone+ _ _ _ _
         mid<b' (ℚ.minus-< 0 _ (ℚ.0<ℚ₊ (Δ₊* ℚ₊· ([ 1 / 4 ] , _)))))
        (ℚ.≡Weaken≤ _ _ (ℚ.+IdR _))

     ab-dist =
       ℚ.≡Weaken≤ (b' ℚ.- newa') (Δ* ℚ.· [ 3 / 4 ])
         (cong (ℚ._-_ b')
           (cong (ℚ._- (Δ* ℚ.· [ 1 / 4 ]))
             mid=b-Δ/2 ∙
              sym (ℚ.+Assoc _ _ _))
              ∙ sym lem--050
           ∙ ℚ.-[x-y]≡y-x _ _ ∙
            cong (ℚ._+_ (Δ* ℚ.· [ 1 / 4 ]))
              (ℚ.-Invol _) ∙
               sym (ℚ.·DistL+ Δ* _ _) ∙
                cong (Δ* ℚ.·_) ℚ.decℚ?  )

     a'≤newa' : a' ℚ.≤ newa'
     a'≤newa' =
       ℚ.isTrans≤ _ _ _ (ℚ.≤+ℚ₊ a' a' ((Δ₊* ℚ₊· ([ 1 / 4 ] , _)))
                (ℚ.isRefl≤ a'))
                 (ℚ.≡Weaken≤ _ _ ≡newa')

     newa'<mid : newa' ℚ.< mid
     newa'<mid = ℚ.<-ℚ₊' _ _ (Δ₊* ℚ₊· ([ 1 / 4 ] , _))
        (ℚ.isRefl≤ mid)

     newa'∈ : newa' ∈ ℚintervalℙ a b
     newa'∈ =
        ℚ.isTrans≤ _ _ _
               (fst a'∈) a'≤newa'
       , ℚ.isTrans≤ _ _ _
               (ℚ.<Weaken≤ _ _ newa'<b') (snd b'∈)

     newa'∈ᵣ = ∈ℚintervalℙ→∈intervalℙ _ _ _ newa'∈

     fnewa'≤y : f (rat newa') _ ≤ᵣ rat y
     fnewa'≤y = isTrans≤ᵣ _ _ _
        (isTrans≤ᵣ _ _ _ mid-dist
           (a-b≤c⇒a-c≤b _ _ _
                 (isTrans≤ᵣ _ _ _ (≤absᵣ _ )
                   (<ᵣWeaken≤ᵣ _ _
                   (fst (∼≃abs<ε _ _ _) (sym∼ _ _ _ fMidDist))))))
        (≤ℚ→≤ᵣ fMid _ (ℚ.<Weaken≤ _ _ x))

       where
         hh = isTrans≤≡ᵣ _ _ _ (apartFrom-Invlipschitz-ℝ→ℝℙ
           K _ f lip⁻¹F
            (rat mid) mid∈'
            (rat newa') newa'∈ᵣ
            (invℚ₊ K ℚ₊· (/4₊ Δ₊*))
              (isTrans≡≤ᵣ _ _ _
                (cong rat (ℚ.y·[x/y] K (fst (/4₊ Δ₊*)))
                 ∙ cong rat (sym lem--079)
                 ∙ sym (-ᵣ-rat₂ _ _))
                (≤absᵣ _)))
             (absᵣPos _ (x<y→0<y-x _ _
               (incrF _ _  _ _ (<ℚ→<ᵣ _ _ newa'<mid) )))

         mid-dist :  f (rat newa') newa'∈ᵣ
                    ≤ᵣ f (rat mid) mid∈' -ᵣ
                       rat (fst (invℚ₊ K ℚ₊· /4₊ Δ₊*))


         mid-dist = a≤b-c⇒c≤b-a _ _ _ hh


     ww : Σ (Step (Δ ℚ.· [ 3 / 4 ])) (Step⊃Step s)
     ww .fst .Step.a' = newa'
     ww .fst .Step.b' = b'
     ww .fst .Step.a'<b' = newa'<b'
     ww .fst .Step.b'-a'≤Δ =
        ℚ.isTrans≤
           _ _ _ ab-dist (ℚ.≤-·o Δ* Δ [ 3 / 4 ]
             (ℚ.<Weaken≤ 0 [ 3 / 4 ] (ℚ.0<pos 2 4)) Δ*≤Δ)
     ww .fst .Step.a'∈ = newa'∈
     ww .fst .Step.b'∈ = b'∈
     ww .fst .Step.a'≤ =  fnewa'≤y
     ww .fst .Step.≤b' = ≤b'
     ww .snd .Step⊃Step.a'≤a'S = a'≤newa'
     ww .snd .Step⊃Step.bS≤b' = ℚ.isRefl≤ b'


   stepS : ∀ Δ → Step Δ → Step (Δ ℚ.· [ 3 / 4 ])
   stepS Δ s = fst (stepS' Δ s)

   ww : ∀ n → Step (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n))
   ww zero = subst (Step) (sym (ℚ.·IdR Δ₀)) step0
   ww (suc n) = subst (Step) (sym (ℚ.·Assoc _ _ _)) (stepS _ (ww n))

   s : ℕ → ℚ
   s = Step.a' ∘ ww

   s' : ℕ → ℚ
   s' = Step.b' ∘ ww

   ss≤-suc : ∀ n (z : Step (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n))) → Step.a' z ℚ.≤
       Step.a' (subst (Step) (sym (ℚ.·Assoc _ _ _)) (stepS
        (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)) z))
   ss≤-suc n z = ℚ.isTrans≤ _ _ _ (Step⊃Step.a'≤a'S (snd (stepS'
        (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)) z)))
          (ℚ.≡Weaken≤ _ _ (sym (transportRefl _)))

   ≤ss'-suc : ∀ n (z : Step (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n))) →
        Step.b' (subst (Step) (sym (ℚ.·Assoc _ _ _)) (stepS
        (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)) z))
       ℚ.≤
        Step.b' z
   ≤ss'-suc n z =  ℚ.isTrans≤ _ _ _
          (ℚ.≡Weaken≤ _ _  (transportRefl _))
            ((Step⊃Step.bS≤b' (snd (stepS'
        (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)) z))))
   ss≤ : ∀ n m → s n ℚ.≤ s (m ℕ.+ n)
   ss≤ n zero = ℚ.isRefl≤ _
   ss≤ n (suc m) = ℚ.isTrans≤ _ _ _ (ss≤ n m) (ss≤-suc (m ℕ.+ n) (ww (m ℕ.+ n)))

   ≤ss' : ∀ n m →  s' (m ℕ.+ n) ℚ.≤ s' n
   ≤ss' n zero = ℚ.isRefl≤ _
   ≤ss' n (suc m) = ℚ.isTrans≤ _ _ _
     (≤ss'-suc (m ℕ.+ n) (ww (m ℕ.+ n))) (≤ss' n m)



   ww⊂ : ∀ n m → (s (m ℕ.+ n) ℚ.- s n) ℚ.≤ Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ n)
   ww⊂ n m = ℚ.isTrans≤
     (s (m ℕ.+ n) ℚ.- s n) (s' n ℚ.- s n) _
       (ℚ.≤-+o (s (m ℕ.+ n)) (s' n) (ℚ.- (s n))
        (ℚ.isTrans≤ _ _ _ (Step.a'≤b' (ww (m ℕ.+ n))) (≤ss' n m)))
    (Step.b'-a'≤Δ (ww n))

   www : {ε : ℚ₊}
           → (Σ[ n ∈ ℕ ] [ 3 / 4 ] ℚ^ⁿ n ℚ.<
             fst (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)))
          → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
               absᵣ (rat (s n) -ᵣ rat (s m)) <ᵣ rat (fst ε))
   www (N , P) .fst = N
   www {ε} (N , P) .snd = ℕ.elimBy≤+
     (λ n m X m< n< → subst (_<ᵣ (rat (fst ε)))
       (minusComm-absᵣ (rat (s m)) (rat (s n))) (X n< m<))
     λ n m p N<n →
       let P' : Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ N) ℚ.< fst ε
           P' = ℚ.isTrans<≤ _ _ (fst ε) (ℚ.<-o· _ _ _ (ℚ.-< a b a<b) P)
                  (ℚ.≡Weaken≤ _ _
                     ((cong (fst (ℚ.<→ℚ₊ a b a<b) ℚ.·_) (ℚ.·Comm _ _))
                      ∙ ℚ.y·[x/y] (ℚ.<→ℚ₊ _ _ a<b) (fst ε)))
           zz = ℚ.isTrans≤< _ _ _
                   (ℚ.isTrans≤ _ ((s (m ℕ.+ n)) ℚ.- (s n)) _
                     (ℚ.≡Weaken≤ _ _ (ℚ.absNonNeg (s (m ℕ.+ n) ℚ.- s n)
                       (ℚ.-≤ (s n) (s (m ℕ.+ n)) (ss≤ n m))))
                       (ww⊂ n m))
                   (ℚ.isTrans< _ (Δ₀ ℚ.· ([ 3 / 4 ] ℚ^ⁿ (N))) _
                     (ℚ.<-o· _ _ Δ₀ (ℚ.-< a b a<b)
                      (<^n' N n _ ℚ.decℚ<? N<n)) P')
       in isTrans≡<ᵣ _ _ _ (cong absᵣ (-ᵣ-rat₂ _  _) ∙ absᵣ-rat _)
            (<ℚ→<ᵣ _ _ zz)


   s-cauchy : IsCauchySequence' (rat ∘ s)
   s-cauchy ε = www {ε} (¾ⁿ<ε (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)))

   f⁻¹ : ℝ
   f⁻¹ = fromCauchySequence' (rat ∘ s)
         s-cauchy




   f⁻¹∈ : f⁻¹ ∈ intervalℙ (rat a) (rat b)
   f⁻¹∈ = ((≤lim _ _ _
            λ δ → ≤ℚ→≤ᵣ _ _ $ fst (Step.a'∈
             (ww (suc (¾ⁿ<ε (δ ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)) .fst))))))
      , (lim≤ _ _ _
            λ δ → ≤ℚ→≤ᵣ _ _ $ snd (Step.a'∈
             (ww (suc (¾ⁿ<ε (δ ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b)) .fst)))))


   s∈ : ∀ n → rat (s n) ∈ intervalℙ (rat a) (rat b)
   s∈ n = ((≤ℚ→≤ᵣ _ _ $ fst (Step.a'∈
             (ww n))))
      , (≤ℚ→≤ᵣ _ _ $ snd (Step.a'∈
             (ww n)))


   s~y : (ε : ℚ₊) →
           ∃-syntax ℕ
           (λ N →
              (n : ℕ) →
              N ℕ.< n →
              absᵣ (f (rat (s n)) (s∈ n) -ᵣ rat y) <ᵣ rat (fst ε))
   s~y ε =
     let (N , X) = (¾ⁿ<ε (invℚ₊ (L ℚ₊· (2 ℚ₊· Δ₀₊)) ℚ₊· ε))

     in ∣ suc N ,
        (λ { zero x → ⊥.rec (ℕ.¬-<-zero x)
           ; (suc n) x →
              let 𝒔 = ww (suc n)
                  XX : ([ pos 3 / 1+ 3 ] ℚ^ⁿ (suc n))
                         ℚ.· fst  (L ℚ₊· (2 ℚ₊· Δ₀₊))
                          ℚ.< fst ε
                  XX =  ℚ.isTrans< _ _ _
                        (ℚ.<-·o _ _ _
                           (ℚ.0<ℚ₊ (L ℚ₊· (2 ℚ₊· Δ₀₊)))
                           (<^n' N (suc n) ([ 3 / 4 ] , _)
                              (ℚ.decℚ<? {[ 3 / 4 ]} {1})
                              (ℕ.<-weaken x)))
                        (subst (ℚ._< _) (
                        cong (([ pos 3 / 1+ 3 ] ℚ^ⁿ N) ℚ.·_)
                        (ℚ.invℚ₊-invol (L ℚ₊· (2 ℚ₊· Δ₀₊))))
                          (ℚ.x<y·z→x·invℚ₊y<z _ _
                            (invℚ₊ (L ℚ₊· (2 ℚ₊· Δ₀₊))) X))


              in isTrans<ᵣ _ _ _ (Step.y-fa' (ww (suc n)))
                     (<ℚ→<ᵣ _ _ (ℚ.isTrans≤<
                       _ _ _
                       (ℚ.≡Weaken≤ _ _
                         (    cong (fst L ℚ.·_)
                               (ℚ.·Assoc _ _ _)
                           ∙∙ ℚ.·Assoc _ _ _
                           ∙∙ ℚ.·Comm _ _))
                       XX)) }) ∣₁


   f∘f⁻¹ : f f⁻¹ f⁻¹∈ ≡ rat y
   f∘f⁻¹ = snd (map-fromCauchySequence'ℙ
          L (rat ∘ s)
            (λ ε → www {ε} (¾ⁿ<ε  (ε ℚ₊· invℚ₊ (ℚ.<→ℚ₊ a b a<b))))
            (intervalℙ (rat a) (rat b)) f lipF f⁻¹∈ s∈) ∙
               fromCauchySequence'≡ _ _ _ s~y



  f⁻¹-L : Lipschitz-ℚ→ℝℙ K (intervalℙ fa fb) f⁻¹
  f⁻¹-L y y∈ r r∈ ε x =
    let zz = lip⁻¹F _ _ _ _ ε
             (subst2 _∼[ ε ]_
               (sym (f∘f⁻¹ y y∈))
               (sym (f∘f⁻¹ r r∈)) (invEq (∼≃abs<ε _ _ _)
                  (isTrans≡<ᵣ _ _ _
                      (cong absᵣ (-ᵣ-rat₂ _ _)
                        ∙ absᵣ-rat _)
                      (<ℚ→<ᵣ (ℚ.abs (y ℚ.- r)) (fst ε) x))

                    ))

    in fst (∼≃abs<ε (f⁻¹ y y∈) (f⁻¹ r r∈) _) zz

  f⁻¹-L-o : Lipschitz-ℚ→ℝℙ K (ointervalℙ fa fb)
                 (λ x x∈ → f⁻¹ x (ointervalℙ⊆intervalℙ fa fb (rat x) x∈ ))
  f⁻¹-L-o y y∈ r r∈ ε x =
    let zz = lip⁻¹F _ _ _ _ ε
             (subst2 _∼[ ε ]_
               (sym (f∘f⁻¹ y (ointervalℙ⊆intervalℙ fa fb _ y∈)))
               (sym (f∘f⁻¹ r (ointervalℙ⊆intervalℙ fa fb _ r∈)))
                (invEq (∼≃abs<ε _ _ _)
                  ((isTrans≡<ᵣ _ _ _
                      (cong absᵣ (-ᵣ-rat₂ _ _)
                        ∙ absᵣ-rat _)
                      (<ℚ→<ᵣ (ℚ.abs (y ℚ.- r)) (fst ε) x)))))

    in fst (∼≃abs<ε (f⁻¹ y (ointervalℙ⊆intervalℙ fa fb _ y∈))
           (f⁻¹ r (ointervalℙ⊆intervalℙ fa fb _ r∈)) _) zz


  δₙ : ℕ → ℚ₊
  δₙ n = /2₊ ([ 1 / ((2+ n) ·₊₁ (2+ (suc n))) ] , _)

  δₙ₊₁≤δₙ : ∀ n → fst (δₙ (suc n )) ℚ.≤ fst (δₙ n)
  δₙ₊₁≤δₙ n =  ℚ.≤-·o _ _ [ 1 / 2 ]  (ℚ.0≤ℚ₊ ([ 1 / 2 ] , tt))
                (fst (ℚ.invℚ₊-≤-invℚ₊
                   (fromNat (ℕ₊₁→ℕ ((2+ n) ·₊₁ (2+ (suc n)))))
                   (fromNat (ℕ₊₁→ℕ ((2+ (suc n)) ·₊₁ (2+ (suc (suc n)))))))
                  (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos
                    (ℕ₊₁→ℕ ((2+ n) ·₊₁ (2+ (suc n))))
                    (ℕ₊₁→ℕ ((2+ (suc n)) ·₊₁ (2+ (suc (suc n)))))
                    (ℕ.≤monotone·
                      (ℕ.≤-sucℕ {2 ℕ.+ n})
                      (ℕ.≤-sucℕ {3 ℕ.+ n})))))


  δₙ< : ∀ n →  Δ₀ ℚ.· [ pos 1 / 2+ n ]
                 ℚ.< Δ₀

  δₙ< n = subst (Δ₀ ℚ.· [ pos 1 / 2+ n ] ℚ.<_) (ℚ.·IdR _)
        ((ℚ.<-o· _ 1 _ (ℚ.0<ℚ₊ Δ₀₊)
                      (fst (ℚ.invℚ₊-<-invℚ₊ 1 (fromNat (suc (suc n))))
                       (ℚ.<ℤ→<ℚ _ _
                         (ℤ.ℕ≤→pos-≤-pos _ _
                           (ℕ.suc-≤-suc ℕ.zero-<-suc))) )))
  Ψ₊ : ℚ₊
  Ψ₊ = invℚ₊ K ℚ₊· Δ₀₊

  Ψ = fst Ψ₊

  Ψ≤fb-fa : rat (fst Ψ₊) ≤ᵣ fb -ᵣ fa
  Ψ≤fb-fa =
     isTrans≤≡ᵣ _ _ _
       (apartFrom-Invlipschitz-ℝ→ℝℙ
                  K _ f lip⁻¹F (rat b) b∈ (rat a) a∈
                   (invℚ₊ K ℚ₊· Δ₀₊)
                    (isTrans≡≤ᵣ _ _ _
                     (cong rat (ℚ.y·[x/y] K _) ∙ sym (-ᵣ-rat₂ _ _))
                     (≤absᵣ _)
                     ) )
                   (absᵣPos _ (x<y→0<y-x _ _ fa<fb))


  a* b* : ℕ → Σ[ q ∈ ℚ ] (rat q ∈ intervalℙ (rat a) (rat b))
  a* n = (a ℚ.+ Δ₀ ℚ.· [ 1 / 1+ (suc n) ]) ,
           (≤ℚ→≤ᵣ _ _
           (ℚ.≤+ℚ₊ a a (Δ₀₊ ℚ₊· ([ 1 / 1+ (suc n) ] , _)) (ℚ.isRefl≤ _)))
            ,
              isTrans≤≡ᵣ _ _ _
                ((≤ℚ→≤ᵣ _ _ (ℚ.≤-o+ _ _ a (ℚ.<Weaken≤ _ _ (δₙ< n)))))
                (cong rat
                  (lem--05 ))
  b* n = b ℚ.- (Δ₀ ℚ.· [ 1 / 1+ (suc n) ]) ,
              isTrans≡≤ᵣ _
          (rat (b ℚ.- Δ₀)) _
         (cong rat (sym lem--079))
         (≤ℚ→≤ᵣ _ _
           (ℚ.≤-o+ _ _ b (ℚ.minus-≤ _ _ (ℚ.<Weaken≤ _ _ (δₙ< n)))))
      , ≤ℚ→≤ᵣ _ _
           ((ℚ.≤-ℚ₊ b b (Δ₀₊ ℚ₊· ([ 1 / 1+ (suc n) ] , _))
            (ℚ.isRefl≤ _)))

  a*<b* : ∀ n → fst (a* (suc n)) ℚ.< fst (b* (suc n))
  a*<b* n =
   subst (ℚ._< fst (b* (suc n)))
    (ℚ.+Comm _ _)
     zz
   where
   zz : (b ℚ.- a) ℚ.· [ 1 / 2+ suc n ] ℚ.+ a ℚ.<
           b ℚ.- ((b ℚ.- a) ℚ.· [ 1 / 2+ (suc n) ])
   zz = ℚ.<-+o-cancel _ (b ℚ.- ((b ℚ.- a) ℚ.· [ 1 / 2+ (suc n) ])) (ℚ.- a)
         (subst2 ℚ._<_
           ((sym (𝐐'.plusMinus ((b ℚ.- a) ℚ.· [ 1 / 2+ suc n ]) a)))
           (    cong₂ ℚ._·_ refl (sym (ℚ.n/k-m/k _ _ (2+ suc n)))
              ∙ 𝐐'.·DistR- _ _ [ 1 / 2+ suc n ]
              ∙ cong₂ ℚ._+_ (𝐐'.·IdR' _ _ (ℚ.[n/n]≡[m/m] (suc (suc n)) 0)) refl
              ∙ sym (ℚ.+Assoc b (ℚ.- a) _)
              ∙ cong₂ ℚ._+_ refl (ℚ.+Comm _ _ )
              ∙ ℚ.+Assoc _ _ _)

           (ℚ.<-o· _ _ (b ℚ.- a)
             (ℚ.0<ℚ₊ Δ₀₊) (ℚ.[k/n]<[k'/n] _ _ _
               (subst (1 ℤ.<_)
                 (cong (ℤ.sucℤ ∘ ℤ.sucℤ)
                   (ℤ.pos+ 0 n ∙ sym (ℤ.sucℤ+ -1 (pos n)))
                   ∙ ℤ.+Comm _ _)
                 (ℤ.suc-≤-suc (ℤ.suc-≤-suc ℤ.zero-≤pos))))))

  a*-desc : ∀ n → fst (a* (suc n)) ℚ.< fst (a* n)
  a*-desc n = ℚ.<-o+ _ _ _
    (ℚ.<-o· _ _ _ (ℚ.0<ℚ₊ Δ₀₊)
      ((fst (ℚ.invℚ₊-<-invℚ₊
        (fromNat (suc (suc n))) ((fromNat (suc (suc (suc n))))))
                       (ℚ.<ℤ→<ℚ _ _
                         (ℤ.ℕ≤→pos-≤-pos _ _
                           ℕ.≤-refl)) )))

  b*-asc : ∀ n → fst (b* n) ℚ.< fst (b* (suc n))
  b*-asc n = ℚ.<-o+ _ _ _
   (ℚ.minus-< _ _ (ℚ.<-o· _ _ _ (ℚ.0<ℚ₊ Δ₀₊)
      (
         ((fst (ℚ.invℚ₊-<-invℚ₊
        (fromNat (suc (suc n))) ((fromNat (suc (suc (suc n))))))
                       (ℚ.<ℤ→<ℚ _ _
                         (ℤ.ℕ≤→pos-≤-pos _ _
                           ℕ.≤-refl)) )))))

  fa* : ∀ n → Σ[ r ∈ ℚ ] ((rat r ∈ intervalℙ fa fb)
             × (absᵣ (rat r -ᵣ f _  (snd (a* n))) <ᵣ rat (fst (Ψ₊ ℚ₊· δₙ n))))
  fa* n =
   let (u , v , (_ , z)) = approxF (fst (a* n)) (snd (a* n))
   in    u (/2₊ (Ψ₊ ℚ₊· δₙ n))
       , v (/2₊ (Ψ₊ ℚ₊· δₙ n))
       , (fst (∼≃abs<ε (rat (u (/2₊ (Ψ₊ ℚ₊· δₙ n)))) _ (Ψ₊ ℚ₊· δₙ n))
         (subst∼ (sym (ℚ.+Assoc _ _ _) ∙
           cong (fst (/2₊ (Ψ₊ ℚ₊· δₙ n)) ℚ.+_)
              (cong fst (ℚ./4₊+/4₊≡/2₊ (Ψ₊ ℚ₊· δₙ n)) )
             ∙ ℚ.ε/2+ε/2≡ε (fst (Ψ₊ ℚ₊· δₙ n)))
           (triangle∼
            (𝕣-lim-self _ _ (/2₊ (Ψ₊ ℚ₊· δₙ n)) (/4₊ (Ψ₊ ℚ₊· δₙ n)))
            (≡→∼ {(/4₊ (Ψ₊ ℚ₊· δₙ n))} z))))

  fb* : ∀ n → Σ[ r ∈ ℚ ] ((rat r ∈ intervalℙ fa fb)
             × (absᵣ (rat r -ᵣ f _  (snd (b* n))) <ᵣ rat (fst (Ψ₊ ℚ₊· δₙ n))))
  fb* n =
   let (u , v , (_ , z)) = approxF (fst (b* n)) (snd (b* n))
   in    u (/2₊ (Ψ₊ ℚ₊· δₙ n))
       , v (/2₊ (Ψ₊ ℚ₊· δₙ n))
       , (fst (∼≃abs<ε (rat (u (/2₊ (Ψ₊ ℚ₊· δₙ n)))) _ (Ψ₊ ℚ₊· δₙ n))
         (subst∼ (sym (ℚ.+Assoc _ _ _) ∙
           cong (fst (/2₊ (Ψ₊ ℚ₊· δₙ n)) ℚ.+_)
              (cong fst (ℚ./4₊+/4₊≡/2₊ (Ψ₊ ℚ₊· δₙ n)) )
             ∙ ℚ.ε/2+ε/2≡ε (fst (Ψ₊ ℚ₊· δₙ n)))
           (triangle∼
            (𝕣-lim-self _ _ (/2₊ (Ψ₊ ℚ₊· δₙ n)) (/4₊ (Ψ₊ ℚ₊· δₙ n)))
            (≡→∼ {(/4₊ (Ψ₊ ℚ₊· δₙ n))} z))))

  faΔ : ∀ n → f (rat (fst (a* n))) (snd (a* n))
          ∼[ L ℚ₊· (2 ℚ₊· (Δ₀₊ ℚ₊· ([ 1 / 2+ n ] , tt))) ] fa
  faΔ n =
   let z = lipF (rat a) a∈
                (rat (fst (a* n))) ((snd (a* n)))
                 (2 ℚ₊· (Δ₀₊ ℚ₊· ([ 1 / 1+ (suc n) ] , _)))
                 ((+IdL _ subst∼[ refl ]
                            (+ᵣComm (rat (Δ₀ ℚ.· [ 1 / 2+ n ])) (rat a)
                             ∙ +ᵣ-rat _ _) )
                            (+ᵣ-∼ 0 (rat (Δ₀ ℚ.· [ 1 / 1+ (suc n) ]))
                              (rat a)
                              (2 ℚ₊· (Δ₀₊ ℚ₊· ([ 1 / 1+ (suc n) ] , _)))
                              (invEq (∼≃abs<ε _ _ _)
                                (isTrans≡<ᵣ _ _ _
                                  (minusComm-absᵣ _ _ ∙∙
                                    cong absᵣ (𝐑'.+IdR' _ _ (-ᵣ-rat 0)) ∙∙
                                      absᵣPos _
                                      (snd (ℚ₊→ℝ₊ (Δ₀₊ ℚ₊· ([ 1 / 1+ (suc n) ] , _))))
                                      ∙ cong rat (sym (ℚ.·IdL _)))
                                  (<ℚ→<ᵣ _ _
                                    (ℚ.<-·o 1 2 (fst (Δ₀₊ ℚ₊· ([ pos 1 / 2+ n ] , tt)))
                                     (ℚ.0<ℚ₊ (Δ₀₊ ℚ₊· ([ pos 1 / 2+ n ] , tt)))
                                     ℚ.decℚ<?
                                     ))))))

   in (sym∼ _ _ _ z)

  -- fa# : ∀ n → f (rat (fst (a* n))) (snd (a* n))
  --         ∼[ L ℚ₊· (2 ℚ₊· (Δ₀₊ ℚ₊· ([ 1 / 2+ n ] , tt))) ] fa
  -- fa# n =
  --  let z = {!!}
  --  in (sym∼ _ _ _ z)


  fbΔ : ∀ n → f (rat (fst (b* n))) (snd (b* n))
          ∼[ L ℚ₊· (2 ℚ₊· (Δ₀₊ ℚ₊· ([ 1 / 2+ n ] , tt))) ] fb
  fbΔ n =
   sym∼ _ _ _ $
     lipF (rat b) b∈
                (rat (fst (b* n))) ((snd (b* n)))
                 (2 ℚ₊· (Δ₀₊ ℚ₊· ([ 1 / 1+ (suc n) ] , _)))
                 (
                  (+IdL _ subst∼[ refl ]
                   (+ᵣComm (rat (ℚ.- (Δ₀ ℚ.· [ 1 / 2+ n ]))) (rat b)
                     ∙ +ᵣ-rat _ _) )
                   (+ᵣ-∼ 0 (rat (ℚ.- (Δ₀ ℚ.· [ 1 / 1+ (suc n) ])))
                     (rat b)
                     (2 ℚ₊· (Δ₀₊ ℚ₊· ([ 1 / 1+ (suc n) ] , _)))

                     ( (refl subst∼[ refl ] -ᵣ-rat _)
                       (invEq (∼≃abs<ε _ _ _)
                       ((isTrans≡<ᵣ _ _ _
                         (cong (absᵣ ∘ (0 +ᵣ_)) (-ᵣInvol _)
                           ∙∙
                           cong absᵣ (+IdL _) ∙∙
                             absᵣPos _
                             (snd (ℚ₊→ℝ₊ (Δ₀₊ ℚ₊· ([ 1 / 1+ (suc n) ] , _))))
                             ∙ cong rat (sym (ℚ.·IdL _)))
                         (<ℚ→<ᵣ _ _
                           (ℚ.<-·o 1 2 (fst (Δ₀₊ ℚ₊· ([ pos 1 / 2+ n ] , tt)))
                            (ℚ.0<ℚ₊ (Δ₀₊ ℚ₊· ([ pos 1 / 2+ n ] , tt)))
                            ℚ.decℚ<?
                            ))))))))


  Φ = (((L ℚ₊· 2) ℚ₊· Δ₀₊) ℚ₊+ (invℚ₊ K ℚ₊· Δ₀₊))

  fa*Δ : ∀ n → rat (fst (fa* n)) -ᵣ fa <ᵣ
                  rat ([ 1 / 1+ (suc n) ] ℚ.· fst Φ)

  fa*Δ n =
   let z = triangle∼ {w = rat (fst (fa* n))}
                (sym∼ _ _ _ (faΔ n)) ((sym∼ _ _ _)
                (invEq (∼≃abs<ε _ _ (Ψ₊ ℚ₊· (([ 1 / (2+ n) ] , _))))
                 ((isTrans<ᵣ _ _ _ (snd (snd (fa* n)))
                (<ℚ→<ᵣ _ _ (ℚ.<-o· (fst (δₙ n)) [ 1 / 2+ n ] Ψ
                (ℚ.0<ℚ₊ Ψ₊)
                 (ℚ.isTrans< (fst (δₙ n)) [ 1 / (2+ n) ·₊₁ (2+ (suc n)) ]
                  [ 1 / (2+ n) ]
                   (x/2<x ([ 1 / (2+ n) ·₊₁ (2+ (suc n)) ] , _))
                  (subst2 (ℚ._<_) (1/m·1/n {2+ n} {2+ (suc n)})
                   (ℚ.·IdR [ 1 / 2+ n ])
                   (ℚ.<-o· [ 1 / 2+ (suc n) ] 1 [ 1 / 2+ n ]
                   (ℚ.0<→< [ 1 / 2+ n ] tt)
                   (fst (ℚ.invℚ₊-<-invℚ₊ 1 (fromNat (3 ℕ.+ n)))
                    (ℚ.<ℤ→<ℚ _ _
                     (ℤ.ℕ≤→pos-≤-pos  _ _
                      (ℕ.≤-k+ {0} {k = 2} (ℕ.zero-≤ {suc n})))) ))))))))))
   in isTrans≤<ᵣ _ _ _
          (≤absᵣ _)
           (fst (∼≃abs<ε _ _
             (([ 1 / 1+ (suc n) ] , _) ℚ₊·
                 (((L ℚ₊· 2) ℚ₊· Δ₀₊) ℚ₊+ (invℚ₊ K ℚ₊· Δ₀₊)))) (subst∼
             (cong₂ ℚ._+_ (ℚ.·Assoc (fst L) 2 ((Δ₀ ℚ.· [ 1 / 1+ (suc n) ]))
                 ∙ ℚ.·Assoc _ _ _)
               refl
               ∙∙ sym (ℚ.·DistR+ _ _ [ 1 / 1+ (suc n) ])
               ∙∙ ℚ.·Comm _ _ )
           (sym∼ _ _ _ z)))

  fb*Δ : ∀ n → fb -ᵣ rat (fst (fb* n))  <ᵣ
                  rat ([ 1 / 1+ (suc n) ] ℚ.· fst Φ)
  fb*Δ n =
   let z = triangle∼ {w = rat (fst (fb* n))}
                (sym∼ _ _ _ (fbΔ n)) ((sym∼ _ _ _)
                (invEq (∼≃abs<ε _ _ (Ψ₊ ℚ₊· (([ 1 / (2+ n) ] , _))))
                 ((isTrans<ᵣ _ _ _ (snd (snd (fb* n)))
                (<ℚ→<ᵣ _ _ (ℚ.<-o· (fst (δₙ n)) [ 1 / 2+ n ] Ψ
                (ℚ.0<ℚ₊ Ψ₊)
                 (ℚ.isTrans< (fst (δₙ n)) [ 1 / (2+ n) ·₊₁ (2+ (suc n)) ]
                  [ 1 / (2+ n) ]
                   (x/2<x ([ 1 / (2+ n) ·₊₁ (2+ (suc n)) ] , _))
                  (subst2 (ℚ._<_) (1/m·1/n {2+ n} {2+ (suc n)})
                   (ℚ.·IdR [ 1 / 2+ n ])
                   (ℚ.<-o· [ 1 / 2+ (suc n) ] 1 [ 1 / 2+ n ]
                   (ℚ.0<→< [ 1 / 2+ n ] tt)
                   (fst (ℚ.invℚ₊-<-invℚ₊ 1 (fromNat (3 ℕ.+ n)))
                    (ℚ.<ℤ→<ℚ _ _
                     (ℤ.ℕ≤→pos-≤-pos  _ _
                      (ℕ.≤-k+ {0} {k = 2} (ℕ.zero-≤ {suc n})))) ))))))))))
   in isTrans≤<ᵣ _ _ _
          (≤absᵣ _)
           (fst (∼≃abs<ε _ _
             (([ 1 / 1+ (suc n) ] , _) ℚ₊·
                 (((L ℚ₊· 2) ℚ₊· Δ₀₊) ℚ₊+ (invℚ₊ K ℚ₊· Δ₀₊)))) (subst∼
             (cong₂ ℚ._+_ (ℚ.·Assoc (fst L) 2 ((Δ₀ ℚ.· [ 1 / 1+ (suc n) ]))
                 ∙ ℚ.·Assoc _ _ _)
               refl
               ∙∙ sym (ℚ.·DistR+ _ _ [ 1 / 1+ (suc n) ])
               ∙∙ ℚ.·Comm _ _ ) z))


  fa*-desc : ∀ n → rat (fst (fa* (suc n))) <ᵣ rat (fst (fa* n))
  fa*-desc n =
     isTrans<ᵣ _ _ _
       (a-b<c⇒a<c+b _ _ _
         (isTrans≤<ᵣ _ _ _ (≤absᵣ _) (snd (snd (fa* (suc n))))))
       (isTrans≤<ᵣ _ _ _
         (fst (x+y≤x'-y'≃x+y'≤x'-y _ _ _ _)
           (isTrans≤≡ᵣ _ _ _

            (isTrans≡≤ᵣ _ _ _
               (+ᵣ-rat _ _)
                (apartFrom-Invlipschitz-ℝ→ℝℙ
           K _ f lip⁻¹F _ _ _ _
                 ((Ψ₊ ℚ₊· δₙ (suc n)) ℚ₊+ (Ψ₊ ℚ₊· δₙ n))
                 (subst2 _≤ᵣ_
                   (cong rat (cong (ℚ._· (fst (δₙ (suc n)) ℚ.+ fst (δₙ n)))
                      (sym (ℚ.y·[x/y] K Δ₀)) ∙ sym (ℚ.·Assoc _ _ _)
                     ∙ cong ((fst K) ℚ.·_)
                     ((ℚ.·DistL+ Ψ (fst (δₙ (suc n)))
                       (fst (δₙ n))))))
                   (cong rat ((𝐐'.·DistR- Δ₀ _ _) ∙ sym lem--081)
                    ∙ sym (absᵣPos _ ((<ℚ→<ᵣ _ _ (ℚ.-< _ _ (a*-desc n)))))
                    ∙ cong absᵣ (sym (-ᵣ-rat₂ _ _)))
                   (≤ℚ→≤ᵣ _ _
                     (ℚ.≤-o·
                       (fst (δₙ (suc n)) ℚ.+ fst (δₙ n))
                        ([ 1 / 2+ n ] ℚ.- [ 1 / 2+ suc n ])
                        _ (ℚ.0≤ℚ₊ Δ₀₊)
                       (subst (fst (δₙ (suc n)) ℚ.+ fst (δₙ n) ℚ.≤_)
                         (sym (1/n-1/sn (suc n)))
                         (ℚ.isTrans≤
                           (fst (δₙ (suc n)) ℚ.+ fst (δₙ n))
                           (fst (δₙ n) ℚ.+ fst (δₙ n))
                           [ 1 / ((2+ n) ·₊₁ (2+ (suc n))) ]
                           ((ℚ.≤-+o (fst (δₙ (suc n)))
                             (fst (δₙ n)) (fst (δₙ n)) (δₙ₊₁≤δₙ n) ))
                           ((ℚ.≡Weaken≤
                             ((fst (δₙ n)) ℚ.+ (fst (δₙ n)))
                             [ 1 / ((2+ n) ·₊₁ (2+ (suc n))) ]
                            (ℚ.ε/2+ε/2≡ε
                             [ 1 / ((2+ n) ·₊₁ (2+ (suc n))) ]))))))))))
             (absᵣPos _ (x<y→0<y-x _ _
                (incrF _ _ _ _ (<ℚ→<ᵣ _ _ (a*-desc n)))))
           ))
         (a-b<c⇒a-c<b _ _ _ (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
           (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) (snd (snd (fa* (n))))))))


  fb*-asc : ∀ n → rat (fst (fb* n)) <ᵣ rat (fst (fb* (suc n)))
  fb*-asc n =
    isTrans<ᵣ _ _ _
      (isTrans<≤ᵣ _ _ _
        ( isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _
         (isTrans≤<ᵣ _ _ _ (≤absᵣ _) (snd (snd (fb* n)))))
         (+ᵣComm _ _))
        w )
      ((a-b<c⇒a-c<b _ _ _
         (isTrans≤<ᵣ _ _ _
         (isTrans≤≡ᵣ _ _ _
           (≤absᵣ _) (minusComm-absᵣ _ _))
         (snd (snd (fb* (suc n)))))))

   where
   w : f (rat (b* n .fst)) (snd (b* n))
        +ᵣ rat (fst ((Ψ₊ ℚ₊· δₙ n))) ≤ᵣ
        f (rat (b* (suc n) .fst)) (snd (b* (suc n))) +ᵣ
          -ᵣ rat (fst (Ψ₊ ℚ₊· δₙ (suc n)))
   w = isTrans≡≤ᵣ _ _ _ (+ᵣComm _ _) $
        fst (x+y≤x'-y'≃x+y'≤x'-y (rat (fst (Ψ₊ ℚ₊· δₙ n))) _ _ _)
          (isTrans≤≡ᵣ _ _ _
            (isTrans≡≤ᵣ _ _ _
             (+ᵣComm (rat (fst (Ψ₊ ℚ₊· δₙ n))) (rat (fst (Ψ₊ ℚ₊· δₙ (suc n))))
              ∙ +ᵣ-rat _ _)
             ((apartFrom-Invlipschitz-ℝ→ℝℙ
           K _ f lip⁻¹F _ (snd (b* (suc n))) _  (snd (b* n))
                 ((Ψ₊ ℚ₊· δₙ (suc n)) ℚ₊+ (Ψ₊ ℚ₊· δₙ n))
                 (subst2 _≤ᵣ_
                   (cong rat (cong (ℚ._· (fst (δₙ (suc n)) ℚ.+ fst (δₙ n)))
                      (sym (ℚ.y·[x/y] K Δ₀)) ∙ sym (ℚ.·Assoc _ _ _)
                     ∙ cong ((fst K) ℚ.·_)
                     ((ℚ.·DistL+ Ψ (fst (δₙ (suc n)))
                       (fst (δₙ n))))))
                       (((cong rat ((𝐐'.·DistR- Δ₀ _ _)
                         ∙ sym lem--062))
                    ∙ sym (absᵣPos _ ((<ℚ→<ᵣ _ _ (ℚ.-< _ _ (b*-asc n)))))
                      ∙ cong absᵣ
                       (sym (-ᵣ-rat₂ _ _))))
                   ((≤ℚ→≤ᵣ _ _
                     (ℚ.≤-o·
                       (fst (δₙ (suc n)) ℚ.+ fst (δₙ n))
                        ([ 1 / 2+ n ] ℚ.- [ 1 / 2+ suc n ])
                        _ (ℚ.0≤ℚ₊ Δ₀₊)
                       (subst (fst (δₙ (suc n)) ℚ.+ fst (δₙ n) ℚ.≤_)
                         (sym (1/n-1/sn (suc n)))
                         (ℚ.isTrans≤
                           (fst (δₙ (suc n)) ℚ.+ fst (δₙ n))
                           (fst (δₙ n) ℚ.+ fst (δₙ n))
                           [ 1 / ((2+ n) ·₊₁ (2+ (suc n))) ]
                           ((ℚ.≤-+o (fst (δₙ (suc n)))
                             (fst (δₙ n)) (fst (δₙ n)) (δₙ₊₁≤δₙ n) ))
                           ((ℚ.≡Weaken≤
                             ((fst (δₙ n)) ℚ.+ (fst (δₙ n)))
                             [ 1 / ((2+ n) ·₊₁ (2+ (suc n))) ]
                            (ℚ.ε/2+ε/2≡ε
                             [ 1 / ((2+ n) ·₊₁ (2+ (suc n))) ]))))))))))))
            (absᵣPos _ ((x<y→0<y-x _ _
                (incrF _ (snd (b* n)) _ (snd (b* (suc n)))
                                  (<ℚ→<ᵣ _ _ (b*-asc n)))))))


  fa*<fb* : ∀ n → fst (fa* (suc n)) ℚ.< fst (fb* (suc n))
  fa*<fb* n =
    let z = incrF _ (snd (a* (suc n))) _ (snd (b* (suc n)))
             (<ℚ→<ᵣ _ _ (a*<b* n))
        zz = isTrans≤≡ᵣ _ _ _ (apartFrom-Invlipschitz-ℝ→ℝℙ
                   K _ f lip⁻¹F
                   _ (snd (b* (suc n)))
                   _ (snd (a* (suc n)))
                   (invℚ₊ K ℚ₊· (Δ₀₊ ℚ₊·
                     (ℚ.<→ℚ₊ _ 1
                       (subst (ℚ._< 1)
                         (sym (ℚ.n/k+m/k 1 1 (2+ suc n)))
                          (invEq ([n/m]<1 _ _)
                            (ℕ.<-k+ {0} {k = 2} ℕ.zero-<-suc))) )))
                    (≡ᵣWeaken≤ᵣ _ _
                      (  cong rat
                           (((ℚ.y·[x/y] K _ ∙ 𝐐'.·DistR- Δ₀ _ _) ∙
                             cong₂ (ℚ._+_)
                               (ℚ.·IdR _)
                               (cong (ℚ.-_)
                               (ℚ.·DistL+ Δ₀ _ _) ∙ sym (𝐐'.-Dist _ _)))
                            ∙∙ 𝐐'.+ShufflePairs _ _ _ _
                            ∙∙ cong (b* (suc n) .fst ℚ.+_)
                                (𝐐'.-Dist _ _))
                       ∙ sym (-ᵣ-rat₂ _ _) ∙ sym
                          (absᵣPos _
                        (x<y→0<y-x _ _ (<ℚ→<ᵣ _ _ (a*<b* n))))

                        )))
                        (absᵣPos _ (x<y→0<y-x _ _ z))
        zA = a-b<c⇒a<c+b (rat (fst (fa* (suc n))))
                (f (rat (a* (suc n) .fst)) (snd (a* (suc n))))
                _
              ((isTrans≤<ᵣ _ _ _ (≤absᵣ _) (snd (snd (fa* (suc n))))))
        zB = a-b<c⇒a-c<b _ (rat (fst (fb* (suc n)))) _
              ((isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) (snd (snd (fb* (suc n)))))))
        1/sssn≤1/3 = (fst (ℚ.invℚ₊-≤-invℚ₊ 3 (fromNat (suc (suc (suc n))))))
                       (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
                        (ℕ.<-k+ {0} {k = 2} ℕ.zero-<-suc))
                         )
        zzs = (<ℚ→<ᵣ _ _
                              (ℚ.<≤Monotone+
                                _ _ _ _
                                 (ℚ.isTrans<≤ _ ([ 1 / 2+ suc n ]) _
                                  (subst2 (ℚ._<_)
                                    ( cong ([ 1 /_])
                                          (·₊₁-comm _ _)
                                     ∙ ℚ.riseQandD 1 _ _
                                     ∙∙ cong₂ ([_/_] ∘ ℚ.ℕ₊₁→ℤ)
                                          (·₊₁-identityˡ 2)
                                          refl
                                     ∙∙ sym (ℚ.n/k+m/k _ _ _))
                                     (cong ([ 1 /_]) (·₊₁-identityˡ _))
                                    ((fst (ℚ.invℚ₊-<-invℚ₊
                                      (fromNat (1 ℕ.· (suc (suc (suc n)))))
                                      (fromNat (ℕ₊₁→ℕ
                                         ((2+ suc (suc n)) ·₊₁ (2+ suc n)))))
                                        (ℚ.<ℤ→<ℚ _ _
                                         (ℤ.ℕ≤→pos-≤-pos _ _
                                           (ℕ.<-·sk {k = (suc (suc n))}
                                             ((ℕ.<-k+ {0} {k = 1} ℕ.zero-<-suc))))))))
                                  1/sssn≤1/3 )
                                (ℚ.≤Monotone+
                                 (([ 1 / 2+ suc n ])) [ 1 / 3 ]
                                 (([ 1 / 2+ suc n ])) [ 1 / 3 ]
                                 1/sssn≤1/3
                                 1/sssn≤1/3))
                              )
        qzz = (a+c<b⇒a<b-c _ 1
                           (rat ([ 1 / 2+ suc n ] ℚ.+ [ 1 / 2+ suc n ]))
                            (isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
                               (+ᵣ-rat _ _) zzs)
                              (cong rat (ℚ.ε/3+ε/3+ε/3≡ε 1))))
        wzqq = (<ℚ→<ᵣ _ _ (subst2 ℚ._<_
                        (ℚ.·DistL+ Ψ _ _)
                        (sym (ℚ.·Assoc (fst (invℚ₊ K)) Δ₀ _))
                        (ℚ.<-o· _ _ _ (ℚ.0<ℚ₊ Ψ₊)

                          (<ᵣ→<ℚ _ _ (isTrans<≡ᵣ _ _ _
                            qzz (-ᵣ-rat₂ _ _)))
                            )))
    in <ᵣ→<ℚ _ _ (isTrans<ᵣ _ _ _
                zA
                (isTrans<ᵣ _ _ _
                  (fst (x+y<x'-y'≃x+y'<x'-y _ _ _ _)
                    (isTrans<≤ᵣ _ _ _
                       (isTrans≡<ᵣ _ _ _
                         (+ᵣ-rat _ _)
                         wzqq)

                      zz) )
                  zB))

  interval*⊆ : ∀ n
    →  intervalℙ (rat (fst (fa* n))) (rat (fst (fb* n)))
     ⊆ intervalℙ fa fb
  interval*⊆ n x (≤x , x≤) =
     (isTrans≤ᵣ _ _ _ (fst (fst (snd (fa* n)))) ≤x)
   , (isTrans≤ᵣ _ _ _ x≤ (snd (fst (snd (fb* n)))))

  interval*⊆o : ∀ n
    →  intervalℙ (rat (fst (fa* n))) (rat (fst (fb* n)))
     ⊆ ointervalℙ fa fb
  interval*⊆o n x (≤x , x≤) =
     (isTrans<≤ᵣ _ _ _
        (isTrans≤<ᵣ _ _ _ ((fst (fst (snd (fa* (suc n))))))
           (fa*-desc n)) ≤x)
   , (isTrans≤<ᵣ _ _ _ x≤
       (isTrans<≤ᵣ _ _ _ (fb*-asc n)
         (snd (fst (snd (fb* (suc n)))))))


  module Fₙ (n : ℕ) where


   fₙ : Σ[ 𝒇⁻¹ ∈ (ℝ → ℝ) ] ((∀ x → x ∈ intervalℙ (rat (fst (fa* (suc n))))
                                 (rat (fst (fb* (suc n))))
                               → 𝒇⁻¹ x ∈ intervalℙ
                                      (𝒇⁻¹ (rat (fst (fa* (suc n)))))
                                      (𝒇⁻¹ (rat (fst (fb* (suc n))))) )
                           × ((Lipschitz-ℝ→ℝ K 𝒇⁻¹) ×
                (((x : ℚ)
                  (x∈ : rat x ∈ intervalℙ (rat (fst (fa* (suc n))))
                                 (rat (fst (fb* (suc n))))) →
                 𝒇⁻¹ (rat x) ≡ f⁻¹ x (interval*⊆ (suc n) (rat x) x∈)))))
   fₙ = flg , g∈ , X
    where

    g = extend-Lipshitzℚ→ℝ K _ _
         (ℚ.<Weaken≤ _ _ (fa*<fb* n))
          (λ x x∈ → f⁻¹ x (interval*⊆ (suc n) (rat x) x∈))
           λ q q∈ r r∈ → f⁻¹-L q _ r _

    flg = (λ z → fromLipschitz K (map-snd (λ r → fst r) g) .fst z)
    X = (snd (fromLipschitz K (map-snd fst g)) , λ x x∈ → snd (snd g) x x∈)



    flg-mon : (x : ℚ)
              (x∈ : rat x ∈ intervalℙ (rat (fst (fa* (suc n))))
                             (rat (fst (fb* (suc n)))))
              (y : ℚ)
              (y∈ : rat y ∈ intervalℙ (rat (fst (fa* (suc n))))
                             (rat (fst (fb* (suc n)))))
              → x ℚ.< y → flg (rat x) <ᵣ flg (rat y)
    flg-mon x x∈ y y∈ x<y =
       let xP = cong₂ f (snd X x x∈) {transport _ _}
                 {f⁻¹∈ x (interval*⊆ (suc n) (rat x) x∈)}
                  (symP (transport-filler _ _))
                  ∙ f∘f⁻¹ _ _
           yP = cong₂ f (snd X y y∈) {transport _ _}
                 {f⁻¹∈ y (interval*⊆ (suc n) (rat y) y∈)}
                  (symP (transport-filler _ _))
                  ∙ f∘f⁻¹ _ _
       in invMon (flg (rat x)) _ (flg (rat y)) _
                   (subst2 _<ᵣ_ (sym xP) (sym yP)
                     (<ℚ→<ᵣ _ _ x<y))

    flg-monNS : (x : ℚ)
              (x∈ : rat x ∈ intervalℙ (rat (fst (fa* (suc n))))
                             (rat (fst (fb* (suc n)))))
              (y : ℚ)
              (y∈ : rat y ∈ intervalℙ (rat (fst (fa* (suc n))))
                             (rat (fst (fb* (suc n)))))
              → x ℚ.≤ y → flg (rat x) ≤ᵣ flg (rat y)
    flg-monNS x x∈ y y∈ =
      ⊎.rec (≡ᵣWeaken≤ᵣ _ _ ∘ cong (flg ∘ rat) )
        (<ᵣWeaken≤ᵣ _ _ ∘ flg-mon x x∈ y y∈)
        ∘ ℚ.≤→≡⊎< _ _


    g∈ : ∀ x (x∈ : x ∈ intervalℙ
                (rat (fst (fa* (suc n))))
                (rat (fst (fb* (suc n)))))
           → flg x ∈ intervalℙ
            (flg (rat (fst (fa* (suc n)))))
            (flg (rat (fst (fb* (suc n)))))
    g∈ x x∈@(≤x , x≤) =
     (x<y+δ→x≤y (flg (rat (fst (fa* (suc n))))) (flg x) (λ ε →
      PT.rec (isProp<ᵣ (flg (rat (fst (fa* (suc n)))))
                (flg x +ᵣ rat (fst ε)))
        (λ (η' , x<η' , η<') →
          let η = ℚ.min η' (fst (fb* (suc n)))
              x≤η = ≤min-lem _ _ _ (<ᵣWeaken≤ᵣ _ _ x<η') x≤
              η< = isTrans≤<ᵣ _ _ _
                    (≤ℚ→≤ᵣ _ _  (ℚ.min≤ η' _)) η<'
              a*∈ : (rat (fst (fa* (suc n)))) ∈
                      intervalℙ (rat (fst (fa* (suc n))))
                             (rat (fst (fb* (suc n))))
              a*∈ = ((≤ᵣ-refl _) , (
                     ≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (fa*<fb* n))))
              η∈ : (rat η) ∈
                      intervalℙ (rat (fst (fa* (suc n))))
                             (rat (fst (fb* (suc n))))
              η∈ =  (isTrans≤ᵣ _ _ _ ≤x x≤η) ,
                    ≤ℚ→≤ᵣ _ _ (ℚ.min≤' η' _)
              z : flg (rat (fst (fa* (suc n)))) ≤ᵣ flg (rat η)
              z = flg-monNS (fst (fa* (suc n)))
                    a*∈
                    η η∈
                    (≤ᵣ→≤ℚ _ _
                      (isTrans≤ᵣ _ _ _
                        ≤x x≤η))
              zz' = (fst X (rat η) x  (invℚ₊ K ℚ₊· ε))
                   ((invEq (∼≃abs<ε _ _ _)
                      (isTrans≡<ᵣ _ _ _
                        (absᵣNonNeg _ (x≤y→0≤y-x _ _ x≤η))
                        (a<c+b⇒a-c<b _ _ _ η<))))
              z' : flg (rat η) <ᵣ flg x +ᵣ rat (fst ε)
              z' = isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _ (isTrans≤<ᵣ _ _ _
                     (≤absᵣ _) (fst (∼≃abs<ε _ _ _) zz')))

                     (+ᵣComm (rat (fst (K ℚ₊· (invℚ₊ K ℚ₊· ε)))) _ ∙
                      cong (flg x +ᵣ_) (cong rat
                        (ℚ.y·[x/y] K _)))
              zzz : flg (rat (fst (fa* (suc n))))
                     <ᵣ flg x +ᵣ rat (fst ε)
              zzz = isTrans≤<ᵣ (flg (rat (fst (fa* (suc n)))))
                   (flg (rat η))
                     (flg x +ᵣ rat (fst ε)) z z'
              in zzz)
        (denseℚinℝ x (x +ᵣ rat (fst (invℚ₊ K ℚ₊· ε)))
          (isTrans≡<ᵣ _ _ _
             (sym (+IdR _))
              (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ (invℚ₊ K ℚ₊· ε))))))
      ))
     ,
     x<y+δ→x≤y (flg x) (flg (rat (fst (fb* (suc n))))) λ ε →
      PT.rec (isProp<ᵣ (flg x) (flg (rat (fst (fb* (suc n)))) +ᵣ rat (fst ε)))
       (λ (η' , <η' , η'<x) →
         let η = ℚ.max η' (fst (fa* (suc n)))
             η≤x : rat η ≤ᵣ x
             η≤x = max≤-lem _ _ _ (<ᵣWeaken≤ᵣ _ _ η'<x) ≤x
             <η = isTrans<≤ᵣ _ _ _
                     <η' (≤ℚ→≤ᵣ _ _  (ℚ.≤max η' (fst (fa* (suc n)))))
             b*∈ : (rat (fst (fb* (suc n)))) ∈
                      intervalℙ (rat (fst (fa* (suc n))))
                             (rat (fst (fb* (suc n))))
             b*∈ = ≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (fa*<fb* n)) , ≤ᵣ-refl _
             η∈ : (rat η) ∈
                      intervalℙ (rat (fst (fa* (suc n))))
                             (rat (fst (fb* (suc n))))
             η∈ =  ≤ℚ→≤ᵣ _ _ (ℚ.≤max' η' _)
                  , (isTrans≤ᵣ _ _ _  η≤x x≤)
             z : flg (rat η) ≤ᵣ  flg (rat (fst (fb* (suc n))))
             z = flg-monNS η η∈
                   (fst (fb* (suc n))) b*∈
                    (≤ᵣ→≤ℚ _ _
                      (isTrans≤ᵣ _ _ _ η≤x x≤ ))
             zz' = (fst X x (rat η)  (invℚ₊ K ℚ₊· ε))
                   ((invEq (∼≃abs<ε _ _ _)
                      (isTrans≡<ᵣ _ _ _
                        (absᵣNonNeg _ (x≤y→0≤y-x _ _ η≤x))
                        (a-b<c⇒a-c<b _ _ _ <η))))
             z' : flg x <ᵣ flg (rat η)  +ᵣ rat (fst ε)
             z' = isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _ (isTrans≤<ᵣ _ _ _
                     (≤absᵣ _) (fst (∼≃abs<ε _ _ _) zz')))
                     (+ᵣComm (rat (fst (K ℚ₊· (invℚ₊ K ℚ₊· ε)))) (flg (rat η)) ∙
                      cong (flg (rat η) +ᵣ_) (cong rat
                        (ℚ.y·[x/y] K _)))
             zzz : flg x <ᵣ flg (rat (fst (fb* (suc n)))) +ᵣ rat (fst ε)
             zzz = isTrans<≤ᵣ _ _ _
                     z' (≤ᵣ-+o _ _ _ z)
         in zzz)
        ((denseℚinℝ (x -ᵣ rat (fst (invℚ₊ K ℚ₊· ε))) x
          (isTrans<≡ᵣ _ _ _
            ((<ᵣ-o+ _ _ _
              (-ᵣ<ᵣ _ _ (snd (ℚ₊→ℝ₊ (invℚ₊ K ℚ₊· ε)))))) (𝐑'.+IdR' _ _ (-ᵣ-rat 0)))))




  lem-fₙ∈ : ∀ n → rat a <ᵣ Fₙ.fₙ n .fst (rat (fst (fa* (suc n))))
  lem-fₙ∈ n =
   let a*∈ = (≤ᵣ-refl _) , (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (fa*<fb* n)))
       zz : _ <ᵣ _
       zz = invMon
               (rat a)
               a∈ _
               _ (isTrans<≡ᵣ _ _ _
                 (isTrans≤<ᵣ _ _ _
                   (fst (fst (snd (fa* (suc (suc n))))))
                   (fa*-desc (suc n)))
                  (sym (f∘f⁻¹ _ _)))

   in isTrans<≡ᵣ _ _ _ zz
       (sym (snd (snd (snd (Fₙ.fₙ n))) (fst (fa* (suc n)))
           a*∈))



  lem-fₙ∈' : ∀ n → Fₙ.fₙ n .fst (rat (fst (fb* (suc n)))) <ᵣ rat b
  lem-fₙ∈' n =
   let a*∈ = (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (fa*<fb* n))) , (≤ᵣ-refl _)
       zz : _ <ᵣ _
       zz = invMon _
               _ (rat b) b∈
               (isTrans≡<ᵣ _ _ _ ((f∘f⁻¹ _ _))
                 (isTrans<≤ᵣ _ _ _
                   (fb*-asc (suc n))
                   (snd (fst (snd (fb* (suc (suc n))))))))

   in isTrans≡<ᵣ _ _ _
       ((snd (snd (snd (Fₙ.fₙ n))) (fst (fb* (suc n)))
           a*∈)) zz


  fₙ∈ : ∀ n → ∀ x → x ∈ intervalℙ (rat (fst (fa* (suc n))))
                                 (rat (fst (fb* (suc n))))
                             → fst (Fₙ.fₙ n) x ∈ ointervalℙ (rat a) (rat b)
  fₙ∈ n x x∈ =
   let (<x , x<) = fst (snd (Fₙ.fₙ n)) x x∈
   in (isTrans<≤ᵣ _ _ _ (lem-fₙ∈ n) <x)
      , (isTrans≤<ᵣ _ _ _ x< (lem-fₙ∈' n))

  invSeq : Seq⊆
  invSeq .Seq⊆.𝕡 n =
    intervalℙ (rat (fst (fa* (suc n)))) (rat (fst (fb* (suc n))))
  invSeq .Seq⊆.𝕡⊆ n x (≤x , x≤) =
      isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ $ fa*-desc (suc n)) ≤x
    , isTrans≤ᵣ _ _ _ x≤ (<ᵣWeaken≤ᵣ _ _ $ fb*-asc (suc n))

  seg→ : Seq⊆→ ℝ invSeq
  seg→ .Seq⊆→.fun x n _ = fst (Fₙ.fₙ n) x

  seg→ .Seq⊆→.fun⊆ x n m x∈ x∈' n<m =
    cong (fst (Fₙ.fₙ n))
      (∈ℚintervalℙ→clampᵣ≡ _ _ _ x∈) ∙∙
     ≡Continuous _ _
       (IsContinuous∘ _ _
          ((Lipschitz→IsContinuous K _
        (fst (snd (snd (Fₙ.fₙ n))))))
         (IsContinuousClamp (rat (fst (fa* (suc n)))) _))
       (IsContinuous∘ _ _
          ((Lipschitz→IsContinuous K _
        (fst (snd (snd (Fₙ.fₙ m))))))
         (IsContinuousClamp (rat (fst (fa* (suc n)))) _))

       (λ r →
          let r∈ = ((clampᵣ∈ℚintervalℙ _ _
                 (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ ( fa*<fb* n)))
                  (rat r)))
          in (snd (snd (snd (Fₙ.fₙ n)))) _
                 r∈
                 ∙∙ cong (f⁻¹ _) (snd (intervalℙ fa fb _) _ _)
                   ∙∙
                  sym ((snd (snd (snd (Fₙ.fₙ m)))) _
                    (Seq⊆.𝕡⊆' invSeq n m ((ℕ.<-weaken n<m )) _ r∈)))
                    x
     ∙∙ cong (fst (Fₙ.fₙ m))
       (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _ x∈))

   where
    x∈'' = Seq⊆.𝕡⊆' invSeq n m ((ℕ.<-weaken n<m )) x x∈


  invSeq⊆⟨fa,fb⟩ : invSeq Seq⊆.s⊇ ointervalℙ fa fb
  invSeq⊆⟨fa,fb⟩ x (<x , x<) =
   PT.map2
     (λ (q , (<q , q<)) (r , (<r , r<)) →
      let q⊔r = ℚ.min₊ (q , ℚ.<→0< q (<ᵣ→<ℚ _ _ <q))
                   (r , ℚ.<→0< r (<ᵣ→<ℚ _ _ <r))

          (N₊ , <N') = map-snd
                (subst (ℚ._≤ fst q⊔r) (ℚ.·Comm _ _) ∘ ℚ.x≤y·z→x·invℚ₊y≤z _ _ _ ∘
                  subst (fst Φ ℚ.≤_) (ℚ.·Comm _ _)
                  ∘ ℚ.x·invℚ₊y≤z→x≤y·z _ _ _ ∘ ℚ.<Weaken≤ _ _)
                (ℚ.ceilℚ₊ (Φ ℚ₊· (invℚ₊ q⊔r) ))
          N = (ℕ₊₁→ℕ N₊)

          <N : ([ 1 / 2+ N ] ℚ.· fst Φ)
                ℚ.≤ fst q⊔r
          <N = ℚ.isTrans≤ _ ([ 1 / N₊ ] ℚ.· fst Φ) _
                   (ℚ.≤-·o _ _ (fst Φ)
                    (ℚ.0≤ℚ₊ Φ)
                    ((fst (ℚ.invℚ₊-≤-invℚ₊
                         (fromNat ((ℕ₊₁→ℕ N₊)))
                         (fromNat (suc (suc ((ℕ₊₁→ℕ N₊))))))
                    ((ℚ.≤ℤ→≤ℚ _ _
                     (ℤ.ℕ≤→pos-≤-pos  _ _
                       (ℕ.≤SumRight {k = 2})))) ))) <N'



      in _ ,
          (isTrans≤ᵣ _ _ _
           (a-b≤c⇒a≤c+b _ _ _
            (isTrans≤ᵣ _ _ _
              (<ᵣWeaken≤ᵣ _ _ (fa*Δ N))
              (≤ℚ→≤ᵣ _ _ (ℚ.isTrans≤ _ _ _
                <N (ℚ.min≤ q r) ))))
           (a≤b-c⇒a+c≤b (rat q) _ fa
            (<ᵣWeaken≤ᵣ _ _ q<)) ,
           isTrans≤ᵣ _ _ _
             (<ᵣWeaken≤ᵣ _ _ (a<b-c⇒c<b-a _ _ _ r<))
               (a-b≤c⇒a-c≤b _ _ _
                 (isTrans≤ᵣ _ _ _
                   (<ᵣWeaken≤ᵣ _ _ (fb*Δ N))
                   (≤ℚ→≤ᵣ _ _ (ℚ.isTrans≤ _ _ _
                      <N (ℚ.min≤' q r) ))))))
     (denseℚinℝ _ _ (x<y→0<y-x _ _ <x))
     (denseℚinℝ _ _ (x<y→0<y-x _ _ x<))


  open Seq⊆→.FromIntersection seg→ isSetℝ (ointervalℙ fa fb)
         invSeq⊆⟨fa,fb⟩


  𝒇⁻¹ = ∩$

  IsLip-𝒇⁻¹ : Lipschitz-ℝ→ℝℙ K (ointervalℙ fa fb) 𝒇⁻¹
  IsLip-𝒇⁻¹ u u∈ v v∈ ε =
    ∩$-elimProp2 u u∈ v v∈
      {B = λ fu fv → u ∼[ ε  ] v → fu ∼[ K ℚ₊· ε  ] fv}
      (λ _ _ → isPropΠ λ _ → isProp∼ _ _ _)
      λ n x∈ y∈ x →
         fst (snd (snd (Fₙ.fₙ n))) _ _ ε x

  IsContinuous-𝒇⁻¹ : IsContinuousWithPred (ointervalℙ fa fb) 𝒇⁻¹
  IsContinuous-𝒇⁻¹ = fromLipshitzℚ→ℝℙ→Cont K _ _ _
    IsLip-𝒇⁻¹

  𝒇⁻¹∈ : ∀ x x∈ →  (𝒇⁻¹ x x∈) ∈ ointervalℙ (rat a) (rat b)
  𝒇⁻¹∈ x x∈ = ∩$-elimProp x x∈
     {_∈ ointervalℙ (rat a) (rat b)}
     (snd ∘ ointervalℙ (rat a) (rat b))
     λ n x∈ₙ → fₙ∈ n x x∈ₙ



  f∘𝒇⁻¹ : ∀ x x∈ → fst (fo (𝒇⁻¹  x x∈) (𝒇⁻¹∈  x x∈)) ≡ x
  f∘𝒇⁻¹ x x∈ = ≡ContinuousWithPred (ointervalℙ fa fb) (ointervalℙ fa fb)
                (openIintervalℙ fa fb) (openIintervalℙ fa fb) _ _
                (IsContinuousWP∘ (ointervalℙ (rat a) (rat b)) _
                  (λ r r∈ → fst (fo r r∈)) 𝒇⁻¹ 𝒇⁻¹∈
                   (IsContinuousWithPred⊆ _ _ f
                     (ointervalℙ⊆intervalℙ (rat a) (rat b)) fC)
                      IsContinuous-𝒇⁻¹)
                (AsContinuousWithPred _ _ IsContinuousId)
                (λ r r∈ r∈' →
                 let zz : (𝒇⁻¹ (rat r) r∈)
                           ≡ (f⁻¹ r (ointervalℙ⊆intervalℙ fa fb (rat r) r∈))
                     zz = ∩$-elimProp (rat r) r∈
                            {λ x → x ≡
                             (f⁻¹ r
                              (ointervalℙ⊆intervalℙ fa fb (rat r) r∈))}
                               (λ _ → isSetℝ _ _)
                                λ n x∈ →
                                  snd (snd (snd (Fₙ.fₙ n))) r x∈ ∙
                                   cong (f⁻¹ r)
                                     (snd (intervalℙ fa fb (rat r)) _ _)
                 in cong (uncurry f)
                       (Σ≡Prop (λ x → snd (intervalℙ (rat a) (rat b) x))
                        zz )
                     ∙ f∘f⁻¹ r
                      (ointervalℙ⊆intervalℙ fa fb (rat r) r∈) ) x x∈ x∈


  isSurjection-fo : isSurjection (uncurry fo)
  isSurjection-fo (x , x∈) =
   ∣ _ ,
    (Σ≡Prop (snd ∘ ointervalℙ fa fb) (f∘𝒇⁻¹ x x∈)) ∣₁

  isEquivFo : isEquiv (uncurry fo)
  isEquivFo = isEmbedding×isSurjection→isEquiv (isEmbed-fo , isSurjection-fo)

  𝒇⁻¹∘f : ∀ x x∈ →  uncurry 𝒇⁻¹ (fo x x∈) ≡ x
  𝒇⁻¹∘f x x∈ =  cong fst (invEq (congEquiv (_ , isEquivFo))
    (Σ≡Prop (snd ∘ ointervalℙ fa fb) (uncurry  f∘𝒇⁻¹ (fo x x∈))))

  f-iso : Iso (Σ ℝ (_∈ ointervalℙ (rat a) (rat b)))
              (Σ ℝ (_∈ ointervalℙ fa fb))
  f-iso .Iso.fun = uncurry fo
  f-iso .Iso.inv (x , x∈) = (𝒇⁻¹  x x∈) , (𝒇⁻¹∈  x x∈)
  f-iso .Iso.rightInv (x , x∈) = Σ≡Prop (snd ∘ ointervalℙ _ _) (f∘𝒇⁻¹ x x∈)
  f-iso .Iso.leftInv (x , x∈) = Σ≡Prop (snd ∘ ointervalℙ _ _) (𝒇⁻¹∘f x x∈)
