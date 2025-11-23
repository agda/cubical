{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.PiNumber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv


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
open import Cubical.HITs.PropositionalTruncation.Monad

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
open import Cubical.HITs.CauchyReals.Uniform


0≤ᵣx² : ∀ x → 0 ≤ᵣ (x ^ⁿ 2)
0≤ᵣx² = ≤Cont
 (IsContinuousConst 0)
 (IsContinuous^ⁿ 2)
 (λ q → isTrans≤≡ᵣ _ _ _
   (≤ℚ→≤ᵣ _ _ (ℚ.0≤x² q))
   (rat·ᵣrat _ _ ∙
    cong₂ _·ᵣ_
     (sym (·IdL _))
     refl) )

x²≤1→∣x∣≤1 : ∀ x → x ^ⁿ 2 ≤ᵣ 1 → absᵣ x ≤ᵣ 1
x²≤1→∣x∣≤1 x x²≤1 =
  PT.rec (isProp≤ᵣ _ _)
    (⊎.rec
       (<ᵣWeaken≤ᵣ _ _ )
        (λ 1/2<∣x∣ →
             ^ⁿMonotone⁻¹ 2 (ℕ.≤-solver 1 2)
              (isTrans<ᵣ _ _ _
                (decℚ<ᵣ? {0} { [ 1 / 2 ] })
                1/2<∣x∣) (decℚ<ᵣ? {0} {1})
                (subst2 _≤ᵣ_
                  (abs[x^²ⁿ] 1 x ∙ absᵣ^ⁿ x 2) --
                  (sym (1^ⁿ 2))
                  x²≤1)
        ))
    (Dichotomyℝ' (rat [ 1 / 2 ]) (absᵣ x) 1
     (decℚ<ᵣ? { [ 1 / 2 ] } {1}))

x²<1→∣x∣<1 : ∀ x → x ^ⁿ 2 <ᵣ 1 → absᵣ x <ᵣ 1
x²<1→∣x∣<1 x x²<1 =
  PT.rec (isProp<ᵣ _ _)
    (⊎.rec (idfun _)
        (λ 1/2<∣x∣ →
             ^ⁿStrictMonotone⁻¹ 2 (ℕ.≤-solver 1 2)
              (isTrans<ᵣ _ _ _
                (decℚ<ᵣ? {0} { [ 1 / 2 ] })
                1/2<∣x∣) (decℚ<ᵣ? {0} {1})
                (subst2 _<ᵣ_
                  (abs[x^²ⁿ] 1 x ∙ absᵣ^ⁿ x 2) --
                  (sym (1^ⁿ 2))
                  x²<1)
        ))
    (Dichotomyℝ' (rat [ 1 / 2 ]) (absᵣ x) 1
     (decℚ<ᵣ? { [ 1 / 2 ] } {1}))

∣sin∣≤1 : ∀ x → absᵣ (sin x) ≤ᵣ 1
∣sin∣≤1 x = x²≤1→∣x∣≤1 (sin x)
  (isTrans≤≡ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _
      (sym (+IdR _)) (≤ᵣ-o+ _ _ _ (0≤ᵣx² _))) (sin²+cos²=1 x))

∣cos∣≤1 : ∀ x → absᵣ (cos x) ≤ᵣ 1
∣cos∣≤1 x = x²≤1→∣x∣≤1 (cos x)
  (isTrans≤≡ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _
      (sym (+IdR _)) (≤ᵣ-o+ _ _ _ (0≤ᵣx² _))) (+ᵣComm _ _ ∙ sin²+cos²=1 x))



bounded-sin : ∀ P → Bounded P (λ x _ → sin x)
bounded-sin P = 1 , λ x _ → ∣sin∣≤1 x

bounded-cos : ∀ P → Bounded P (λ x _ → cos x)
bounded-cos P = 1 , λ x _ → ∣cos∣≤1 x

Lipschitz-ℝ→ℝ→IsUContinuousℙ : ∀ L f → Lipschitz-ℝ→ℝ L f →
  ∀ P → IsUContinuousℙ P λ x _ → f x
Lipschitz-ℝ→ℝ→IsUContinuousℙ L f fLip P ε =
  invℚ₊ L ℚ₊· ε  , λ u v u∈ v∈ x →
   subst∼ (ℚ.y·[x/y] L (fst ε)) (fLip u v ( invℚ₊ L ℚ₊· ε ) x)


ℚ^ⁿ-dist· : ∀ p q n → (p ℚ.· q) ℚ^ⁿ n ≡ (p ℚ^ⁿ n) ℚ.· (q ℚ^ⁿ n)
ℚ^ⁿ-dist· p q zero = refl
ℚ^ⁿ-dist· p q (suc n) =
  cong₂ ℚ._·_ (ℚ^ⁿ-dist· p q n) refl ∙
    lem--086

^ⁿ-MonotoneR-inv
        : (x : ℝ) → 0 ≤ᵣ x → x ≤ᵣ 1 →  (m n : ℕ) →

           m ℕ.≤ n → (x ^ⁿ n) ≤ᵣ (x ^ⁿ m)
^ⁿ-MonotoneR-inv x 0≤x x≤1 zero zero _ = ≤ᵣ-refl _
^ⁿ-MonotoneR-inv x 0≤x x≤1 zero (suc n) _ =
  isTrans≤≡ᵣ _ _ _ (≤ᵣ₊Monotone·ᵣ _ _ _ _
    (decℚ≤ᵣ? {0} {1}) 0≤x
    (^ⁿ-MonotoneR-inv x 0≤x x≤1 zero n ℕ.zero-≤)
    x≤1)
     (sym (rat·ᵣrat 1 1))
^ⁿ-MonotoneR-inv x 0≤x x≤1 (suc m) zero m≤zero =
  ⊥.rec (ℕ.¬-<-zero m≤zero)
^ⁿ-MonotoneR-inv x 0≤x x≤1 (suc m) (suc n) sm≤sn =
  ≤ᵣ-·ᵣo _ _ x
    0≤x
    (^ⁿ-MonotoneR-inv x 0≤x x≤1 m n (ℕ.pred-≤-pred sm≤sn))


opaque
 lim0FromRatioBound : ∀ (s : Seq) (q : ℚ₊) → (q<1 : fst q ℚ.< 1)
      (sBound : Σ[ b ∈ ℚ₊ ] ∀ n → absᵣ (s n)  ≤ᵣ rat (fst b))
      → (0＃s : ∀ n → 0 ＃ s n)
      → ∀ N
      → ((n : ℕ) →
           N ℕ.< n →
           absᵣ ((s (suc n) ／ᵣ[ s n , 0＃s n ])) <ᵣ
           rat (fst q))
      → lim'ₙ→∞ s is 0
 lim0FromRatioBound s r r<1 (b , ≤b) 0＃s N Y η =
  let ε = η ℚ₊· invℚ₊ b
      (p' , 1+ q) , _ , p/q≡r = ℚ.reduced (fst r)
      (p , sp=p') = w p' q (subst ℚ.0<_ (sym p/q≡r) (snd r))
      (𝒑' , 1+ 𝒒) , _ , 𝒑/𝒒≡ε = ℚ.reduced (fst ε)
      (𝒑 , s𝒑=𝒑') = w 𝒑' 𝒒 (subst ℚ.0<_ (sym 𝒑/𝒒≡ε) (snd ε))
      uu = subst2 (ℤ._<_)
         (ℤ.·IdR p' ∙ sym (sp=p')) refl
          (subst (ℚ._< 1) (sym p/q≡r) r<1)
      M , X = ℕkⁿ<ε (suc 𝒒) (suc 𝒑) (suc q) (suc p) (ℕ.zero-<-suc {𝒑})
        (fst (ℤ.pos-<-pos≃ℕ<  _ _)
         uu)
  in (suc N ℕ.+ M) , λ n (u , =n) →
     let z : rat (fst (r ℚ₊^ⁿ M) ) <ᵣ rat (fst (invℚ₊ b)) ·ᵣ rat (fst η)
         z = subst2 _<ᵣ_
              (cong₂ _·ᵣ_ refl (invℝ₊-rat _) ∙
                 sym (rat·ᵣrat _ _) ∙
                  cong rat ((cong₂ ℚ._·_ refl (ℚ.invℚ₊-ℚ^ⁿ _ _))
                       ∙ sym (ℚ^ⁿ-dist· _ _ M) ∙ cong (_ℚ^ⁿ M)
                      (((invℚ₊-[/] (pos (suc p)) q
                   ∙ cong [_/ 1+ q ] sp=p') ∙ p/q≡r))) )
              (((cong₂ _·ᵣ_ refl (invℝ₊-rat _) ∙
                sym (rat·ᵣrat _ _) ∙
                 cong rat ((invℚ₊-[/] (pos (suc 𝒑)) 𝒒
                   ∙ cong [_/ 1+ 𝒒 ] s𝒑=𝒑') ∙ 𝒑/𝒒≡ε)) ∙ rat·ᵣrat _ _ ) ∙ ·ᵣComm _ _)
            (invEq (z/y'<x/y≃y₊·z<y'₊·x
                (rat [ pos (suc 𝒑) / 1 ])
                (rat ([ pos (suc p) / 1 ] ℚ^ⁿ M))
                     (ℚ₊→ℝ₊ ([ pos (suc 𝒒) / 1 ] , _))
                     (ℚ₊→ℝ₊ (([ pos (suc q) / 1 ] , _) ℚ₊^ⁿ M)))
               (subst2 _<ᵣ_
                  (cong rat (sym (ℚ.ℕ·→ℚ· _ _)
                     ∙ cong₂ ℚ._·_ refl (sym (ℚ.fromNat-^ (suc p) M) ))
                      ∙ rat·ᵣrat _ _)
                  (cong rat ((sym (ℚ.ℕ·→ℚ· _ _)
                     ∙ ℚ.·Comm _ _
                        ∙ cong₂ ℚ._·_ (sym (ℚ.fromNat-^ (suc q) M) ) refl))
                       ∙ rat·ᵣrat _ _)
                 (<ℚ→<ᵣ _ _
                   (ℚ.<ℤ→<ℚ _ _
                     (invEq (ℤ.pos-<-pos≃ℕ< _ _) X)))))

     in subst2 _<ᵣ_
             (cong absᵣ (sym (𝐑'.+IdR' _ _ (-ᵣ-rat 0))))
             refl
             (isTrans≤<ᵣ _ _ _
               (isTrans≤≡ᵣ _ _ _
                 (isTrans≤ᵣ _ _ _
                   (isTrans≤ᵣ _ _ _
                     (isTrans≡≤ᵣ _ _ _
                       (cong (absᵣ ∘ s) (sym =n ∙
                         ℕ.+-suc _ _ ∙ cong suc
                          (cong₂ ℕ._+_ refl (ℕ.+-comm _ _)
                           ∙ ℕ.+-assoc _ _ _)))
                       (Y' (u ℕ.+ M)))
                     (≤ᵣ-·ᵣo (rat (fst (r ℚ₊^ⁿ (suc u ℕ.+ M)))) _ _ (0≤absᵣ _)
                       (subst2 _≤ᵣ_
                         (^ⁿ-ℚ^ⁿ _ _)
                         (^ⁿ-ℚ^ⁿ _ _)
                         (^ⁿ-MonotoneR-inv _
                           (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ r)))
                           (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ r<1))
                           M
                           (suc u ℕ.+ M)
                           (ℕ.≤SumRight {M} {suc u}))))) (≤ᵣ-o· _ _ _
                     (ℚ.0≤ℚ₊ (r ℚ₊^ⁿ M))
                     (≤b (suc N))))
                 (cong₂ _·ᵣ_ refl
                  (cong fst (sym (invℝ₊Invol (ℚ₊→ℝ₊ b))) ∙
                   cong (fst ∘ invℝ₊)
                     (ℝ₊≡ (invℝ₊-rat _)))))
               (invEq (z/y<x₊≃z<y₊·x _ _ (ℚ₊→ℝ₊ (invℚ₊ b)))
                 z))

  where
   w : ∀ p' q → ℚ.0< [ p' / 1+ q ] → (Σ _ λ p → pos (suc p) ≡ p')
   w (pos (suc n)) q x = n , refl

   Y'' : ∀ M → absᵣ (s (suc M ℕ.+ suc N)) ≤ᵣ
      rat (r .fst) ·ᵣ absᵣ (s (M ℕ.+ suc N))
   Y'' M =
    let zz = isTrans≡<ᵣ _ _ _ (cong₂ _·ᵣ_ refl (sym (absᵣ-invℝ _ _))
              ∙ sym (·absᵣ _ _))
            (Y (M ℕ.+ suc N) (ℕ.≤-+-< (ℕ.zero-≤ {M}) (ℕ.≤-refl {suc N})))
    in isTrans≤≡ᵣ _ _ _
        (<ᵣWeaken≤ᵣ _ _ (fst (z/y<x₊≃z<y₊·x _ _ _) zz))
         (·ᵣComm _ _)


   Y' : ∀ M → absᵣ (s (suc M ℕ.+ (suc N))) ≤ᵣ
      rat (fst (r ℚ₊^ⁿ suc M)) ·ᵣ absᵣ (s (suc N))
   Y' zero = isTrans≤≡ᵣ _ _ _ (Y'' zero)
    (cong₂ _·ᵣ_ (cong rat (sym (ℚ.·IdL _))) refl)
   Y' (suc M) = isTrans≤ᵣ _ _ _
       (Y'' (suc M))
       (isTrans≤≡ᵣ _ _ _
        (≤ᵣ-o· _ _ _ (ℚ.0≤ℚ₊ r) (Y' M))
        (·ᵣAssoc _ _ _ ∙ cong₂ _·ᵣ_  (·ᵣComm _ _ ∙ sym (rat·ᵣrat _ _)) refl))

IntegralOf-clamp : ∀ (a b : ℝ) → a ≤ᵣ b → ∀ f s →
    on[ a , b ]IntegralOf (f ∘ clampᵣ a b) is' s
  ≃ on[ a , b ]IntegralOf f is' s
IntegralOf-clamp a b a≤b f s =
 substEquiv {A = {r : Partition[ a , b ]}
              (r₁ : Sample r) →
              (ℝ → ℝ) → ℝ }
           {a = λ {p} pt f → riemannSum' {a} {b} pt (f ∘ clampᵣ a b)}
            {riemannSum' {a} {b}}
  (λ rsf
     → (∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
     ∀ ((p , t) : TaggedPartition[ a , b ]) →
     (mesh≤ᵣ p (rat (fst δ)) →
       absᵣ (rsf t f -ᵣ s) <ᵣ rat (fst ε))))
  (implicitFunExt (funExt₂
   λ t f → riemannSum'≡ t _ _ λ x x∈ →
     sym (cong f (∈ℚintervalℙ→clampᵣ≡ a b x x∈)) ))

clampᵣ-IntegralOf
   : ∀ (a b : ℝ) (a≤b : a ≤ᵣ b) f
     (s : ℝ) →
     (on[ a , b ]IntegralOf f is' s)
     ≃ (on[ a , b ]IntegralOf (λ x _ _ → f x) is s)
clampᵣ-IntegralOf a b a≤b f s =
  invEquiv (IntegralOf-clamp a b a≤b f s)
   ∙ₑ clampᵣ-IntegralOf' a b a≤b (λ x _ → f x) s

Integrate-UContinuous∈ : ∀ (a b : ℝ) → a ≤ᵣ b → ∀ f
   → IsUContinuousℙ (intervalℙ a b) (λ x _ → f x)
   → Σ ℝ λ R → on[ a , b ]IntegralOf f is' R
Integrate-UContinuous∈ a b a≤b f icF =
 let z = Integrate-UContinuousℙ a b a≤b (λ x _ → f x) icF
     zz = invEq (clampᵣ-IntegralOf' a b a≤b (λ x _ → f x) _) (snd z)
 in _ , fst (IntegralOf-clamp a b a≤b _ _) zz


ratioTest₊≤' : ∀ (s : Seq) (q : ℚ₊) → (q<1 : fst q ℚ.< 1)
     → (sPos : ∀ n → rat 0 <ᵣ (s n))
     → lim'ₙ→∞ s is 0
     → (Σ[ N ∈ ℕ ]
       ((n : ℕ) →
          N ℕ.< n →
          absᵣ ((s (suc n) ／ᵣ[ s n , inl (sPos n) ])) <ᵣ
          rat (fst q)))
     → IsConvSeries' s
ratioTest₊≤' s q q<1 sPos l' N½ ε₊@(ε , 0<ε) =
  N , ww

 where


 ½ᵣ = (ℚ₊→ℝ₊ q)
 ε/2 : ℚ₊
 ε/2 = ε₊ ℚ₊· q

 1-q₊ : ℚ₊
 1-q₊ = ℚ.<→ℚ₊ _ _ q<1
 ε/2' : ℚ₊
 ε/2' = ε₊ ℚ₊· 1-q₊

 Nε = (l' ε/2')

 N : ℕ
 N = suc (ℕ.max (suc (fst N½)) (fst Nε))

 ww : ∀ m n → absᵣ (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n) <ᵣ (rat ε)
 ww m n = isTrans≤<ᵣ _ _ _
   (≡ᵣWeaken≤ᵣ _ _
     (absᵣNonNeg (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n)
     (0≤seqΣ _ (λ n → <ᵣWeaken≤ᵣ _ _ (sPos (n ℕ.+ (m ℕ.+ suc N)))) _))) pp

  where
  opaque
   unfolding -ᵣ_ _+ᵣ_

   s' : Seq
   s' = s ∘ (ℕ._+ (suc (m ℕ.+ N)))


   f' : ((n : ℕ) →  N ℕ.≤ n →
          (s (suc n)) ≤ᵣ
          s n ·ᵣ rat (fst q))
   f' n n< =
      subst2 {x = ((s (suc n) ／ᵣ[ s n , inl (sPos n) ])
                      ) ·ᵣ s n }
         _≤ᵣ_ (
           [x/y]·yᵣ _ _ _) (·ᵣComm _ _)
        ((<ᵣWeaken≤ᵣ _ _
           (<ᵣ-·ᵣo _ _ (s n , sPos _)
            (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
              (snd N½ n (
               ℕ.<-trans (ℕ.left-≤-max {suc (fst N½)} {fst Nε})
                n<))))))


   p : ∀ n → s' n ≤ᵣ geometricProgression (s (m ℕ.+ N)) (fst ½ᵣ) n
   p zero =
      isTrans≤ᵣ _ _ _ ((f' (m ℕ.+ N) (ℕ.≤SumRight {N} {m}) ))
              (subst ((s (m ℕ.+ N) ·ᵣ rat (fst q)) ≤ᵣ_)
                 (·IdR _)
                  (≤ᵣ-o·ᵣ (fst ½ᵣ) 1 (s (m ℕ.+ N))
                    (<ᵣWeaken≤ᵣ _ _ (sPos _))
                   (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ q<1))))

   p (suc n) =
     isTrans≤ᵣ _ _ _ (f' _
       (subst (N ℕ.≤_) (sym (ℕ.+-assoc n (1 ℕ.+ m) N))
         ℕ.≤SumRight))
       (≤ᵣ-·ᵣo _ _ (rat (fst q)) ((<ᵣWeaken≤ᵣ 0 (rat (fst q))
         (snd (ℚ₊→ℝ₊ q)))) (p n))

   p' : ∀ n → seqSumUpTo' s' n ≤ᵣ seqSumUpTo' (geometricProgression (s (m ℕ.+ N)) (fst ½ᵣ)) n
   p' = Seq'≤→Σ≤ s' (geometricProgression (s (m ℕ.+ N)) (fst ½ᵣ))
         p

   s<ε : (s (m ℕ.+ N)) <ᵣ rat (fst ε/2')
   s<ε = subst (_<ᵣ rat (fst ε/2')) (+IdR _)
            ((isTrans≤<ᵣ _ _ _
           (≤absᵣ ((s (m ℕ.+ N)) +ᵣ (-ᵣ 0))) (snd Nε _
            (ℕ.≤<-trans ℕ.right-≤-max ℕ.≤SumRight))))


   pp : (seqΣ (λ x → s (x ℕ.+ (m ℕ.+ suc N))) n) <ᵣ (rat ε)
   pp =
       subst {x = ℕ._+ suc (m ℕ.+ N) } {y = λ z → z ℕ.+ (m ℕ.+ suc N)}
            (λ h → seqΣ (s ∘S h) n <ᵣ rat ε)

           (funExt (λ x → cong (x ℕ.+_) (sym (ℕ.+-suc _ _)) ))
           (isTrans≤<ᵣ _ _ _ (p' n)
             (isTrans≤<ᵣ _ _ _
               (≡ᵣWeaken≤ᵣ _ _ (seqSumUpTo≡seqSumUpTo' _ _))
                 (isTrans<≤ᵣ _ _ _
                  (Sₙ-sup (s (m ℕ.+ N)) (fst ½ᵣ)
                    n (sPos _) (snd ½ᵣ)
                     (<ℚ→<ᵣ _ _ q<1))

                   ((isTrans≤ᵣ _ _ _
                   (≤ᵣ₊Monotone·ᵣ _ _ _ (rat (invℚ (fst 1-q₊) _))
                         (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ (ℚ.0<ℚ₊ ε/2')))
                           (<ᵣWeaken≤ᵣ _ _
                              ((0<1/x _ _ (snd (ℚ₊→ℝ₊ 1-q₊)))))

                     (<ᵣWeaken≤ᵣ _ _ s<ε)
                     (≡ᵣWeaken≤ᵣ _ _
                        (invℝ-rat _ _ (inl (ℚ.0<ℚ₊ 1-q₊)))))
                         (≡ᵣWeaken≤ᵣ _ _ (sym (rat·ᵣrat _  _) ∙
                           cong rat (sym (ℚ.·Assoc _ _ _) ∙
                             cong (ε ℚ.·_)
                              (ℚ.ℚ-y/y (fst 1-q₊) (inl (ℚ.0<ℚ₊ 1-q₊)))
                              ∙ ℚ.·IdR _))))))))


ratioTest₊≤ : ∀ (s : Seq) (sBound : Σ[ b ∈ ℚ₊ ] ∀ n → absᵣ (s n)  ≤ᵣ rat (fst b))
 (q : ℚ₊) → (q<1 : fst q ℚ.< 1)
     → (sPos : ∀ n → rat 0 <ᵣ (s n))

     → (Σ[ N ∈ ℕ ]
       ((n : ℕ) →
          N ℕ.< n →
          absᵣ ((s (suc n) ／ᵣ[ s n , inl (sPos n) ])) <ᵣ
          rat (fst q)))
     → IsConvSeries' s
ratioTest₊≤ s sBound q q<1 sPos N½ =
  ratioTest₊≤' s q q<1 sPos
    ((lim0FromRatioBound _ q q<1 sBound (inl ∘ sPos)
      (fst N½  ) (snd N½)))
    N½

tent : ℝ → ℝ₊ → ℝ → ℝ → ℝ
tent ε δ x₀ x = ε ·ᵣ maxᵣ 0 (1 -ᵣ absᵣ (x -ᵣ x₀) ·ᵣ fst (invℝ₊ δ))

Integral'Const1 : ∀ a b → a ≤ᵣ b →
      on[ a , b ]IntegralOf
      (λ _ → 1) is'
      (b -ᵣ a)
Integral'Const1 a b a≤b ε =
  ∣ 1 , (λ tp _ → isTrans≡<ᵣ _ _ _
    (cong absᵣ (𝐑'.+InvR' _ _ (riemannSum'Const (snd tp) 1 ∙ ·IdL _))
     ∙ absᵣ0) (snd (ℚ₊→ℝ₊ ε))) ∣₁

Integral'Const0 : ∀ a b → a ≤ᵣ b →
      on[ a , b ]IntegralOf
      (λ _ → 0) is' 0
Integral'Const0 a b a≤b ε =
  ∣ 1 , (λ tp _ → isTrans≡<ᵣ _ _ _
    (cong absᵣ (𝐑'.+InvR' _ _ (riemannSum'Const (snd tp) 0 ∙
     𝐑'.0LeftAnnihilates _))
     ∙ absᵣ0) (snd (ℚ₊→ℝ₊ ε))) ∣₁


Integral'Const : ∀ a b → a ≤ᵣ b → ∀ C →
      on[ a , b ]IntegralOf
      (λ _ → C) is'
      (C ·ᵣ (b -ᵣ a))
Integral'Const a b a≤b C ε =
  ∣ 1 , (λ tp _ → isTrans≡<ᵣ _ _ _
    (cong absᵣ (𝐑'.+InvR' _ _ (riemannSum'Const (snd tp) C))
     ∙ absᵣ0) (snd (ℚ₊→ℝ₊ ε))) ∣₁


IntegralConstℙ : ∀ a b → a ≤ᵣ b → ∀ C →
      on[ a , b ]IntegralOf
      (λ _ _ _ → C) is
      (C ·ᵣ (b -ᵣ a))
IntegralConstℙ a b a≤b C ε =
  ∣ 1 , (λ tp _ → isTrans≡<ᵣ _ _ _
    (cong absᵣ (𝐑'.+InvR' _ _ (riemannSum'Const (snd tp) C))
     ∙ absᵣ0) (snd (ℚ₊→ℝ₊ ε))) ∣₁



sin≤1 : ∀ x → sin x ≤ᵣ 1
sin≤1 x = isTrans≤ᵣ _ _ _ (≤absᵣ _) (∣sin∣≤1 x)

-1≤sin : ∀ x → -1 ≤ᵣ sin x
-1≤sin x = subst2 _≤ᵣ_
  (-ᵣ-rat 1)
  (sym (cong -ᵣ_ (sin-odd x)) ∙ -ᵣInvol _)
  (-ᵣ≤ᵣ _ _ (sin≤1 (-ᵣ x)))

open ℚ.HLP

Integral'-< : ∀ a b → a <ᵣ b → ∀ f f' s s'
            → (∀ x → x ∈ intervalℙ a b → f x ≤ᵣ f' x)
            → ∥ IsUContinuousℙ (intervalℙ a b) (λ x _ → f x) ∥₁
            → ∥ IsUContinuousℙ (intervalℙ a b) (λ x _ → f' x) ∥₁
            → on[ a , b ]IntegralOf f is' s
            → on[ a , b ]IntegralOf f' is' s'
            → f a <ᵣ f' a
            → s <ᵣ s'
Integral'-< a b a<b f f' s s' f≤f' fUC₁ fUC'₁ ∫f=s ∫f'=s' fa<fa' =
  fst (propTruncIdempotent≃ (isProp<ᵣ _ _)) $ do
   fUC ← fUC₁
   fUC' ← fUC'₁


   (ε₊@(ε , 0<ε) , ε<πn) ←
     lowerℚBound _ (x<y→0<y-x _ _ fa<fa')
   let (δf , X) = fUC (/2₊ ε₊)
       (δf' , X') = fUC' (/4₊ ε₊)
       δ = (ℚ.min₊ δf δf')
       δ' = minᵣ₊ (ℚ₊→ℝ₊ (/2₊ δ)) (_ , x<y→0<y-x _ _ a<b)
       a' = a +ᵣ fst δ'
       a'≤b : a' ≤ᵣ b
       a'≤b = isTrans≤≡ᵣ _ _ _
                (≤ᵣ-o+ _ _ a (min≤ᵣ' (rat (fst (/2₊ δ))) (b -ᵣ a)))
                L𝐑.lem--05
       a<a' : a <ᵣ a'
       a<a' = isTrans≡<ᵣ _ _ _ (sym (+IdR _))
                 (<ᵣ-o+ _ _ a (snd δ'))
       aa'⊆ab : intervalℙ a a' ⊆ intervalℙ a b
       aa'⊆ab x x∈ = fst x∈ , isTrans≤ᵣ _ _ _ (snd x∈) a'≤b
       a'b⊆ab : intervalℙ a' b ⊆ intervalℙ a b
       a'b⊆ab x x∈ = isTrans≤ᵣ _ _ _  (<ᵣWeaken≤ᵣ _ _ a<a') (fst x∈) , snd x∈
   ∣ subst2 _<ᵣ_
         ((Integral'-additive a a' b (<ᵣWeaken≤ᵣ _ _ a<a') a'≤b
              f _ _ s
                (snd (Integrate-UContinuous∈ a a' (<ᵣWeaken≤ᵣ _ _ a<a') f
                  (IsUContinuousℙ-restr _ _ _ aa'⊆ab fUC)))
                (snd (Integrate-UContinuous∈ a' b a'≤b f
                  (IsUContinuousℙ-restr _ _ _ a'b⊆ab fUC)))
                ∫f=s))
         (Integral'-additive a a' b (<ᵣWeaken≤ᵣ _ _ a<a') a'≤b
              f' _ _ s'
                (snd (Integrate-UContinuous∈ a a' (<ᵣWeaken≤ᵣ _ _ a<a') f'
                  (IsUContinuousℙ-restr _ _ _ aa'⊆ab fUC')))
                (snd (Integrate-UContinuous∈ a' b a'≤b f'
                  (IsUContinuousℙ-restr _ _ _ a'b⊆ab fUC')))
                ∫f'=s')
         (<≤ᵣMonotone+ᵣ _ _ _ _
           (isTrans<≤ᵣ _ _ _
             (isTrans≡<ᵣ _ _ _
                (sym (+IdR _))
                (<ᵣ-o+ _ _ _
                 (snd (ℚ₊→ℝ₊ (/4₊ (ε , 0<ε))
                      ₊·ᵣ (_ , x<y→0<y-x _ _ a<a')))))
             ((Integral'-≤ a a' (<ᵣWeaken≤ᵣ _ _ a<a')
              (λ x → f x +ᵣ rat (fst (/4₊ ε₊)))
              f' _ _
             (λ x x∈ →
                let x∼a = (invEq (∼≃abs<ε _ _ δ)
                                (isTrans≡<ᵣ _ _ _
                                  (abs-max _)
                                   (max<-lem _ _ _
                                    (isTrans≤<ᵣ _ (fst δ') _
                                      (a≤c+b⇒a-c≤b _ _ _
                                        (snd x∈))
                                      (isTrans≤<ᵣ _ _ _
                                        (min≤ᵣ (fst (ℚ₊→ℝ₊ (/2₊ δ))) (b -ᵣ a))
                                         (<ℚ→<ᵣ _ _ (x/2<x δ) )))
                                    (isTrans≡<ᵣ _ _ _
                                     (-[x-y]≡y-x _ _)
                                      (isTrans≤<ᵣ _ _ _
                                        (x≤y→x-y≤0 _ _ (fst x∈ ))
                                         (snd (ℚ₊→ℝ₊ δ)))))))
                    zzz = a-b≤c⇒a-c≤b _ _ _ $ isTrans≤ᵣ _ _ _
                            (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _)
                             (X x a
                              (aa'⊆ab x x∈)
                              (≤ᵣ-refl a , <ᵣWeaken≤ᵣ _ _  a<b)
                               (∼-monotone≤ (ℚ.min≤ _ _) x∼a))))
                    zzz' = a-b≤c⇒a-c≤b _ _ _ $ isTrans≤ᵣ _ _ _
                            (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _)
                            (X' a x ((≤ᵣ-refl a , <ᵣWeaken≤ᵣ _ _  a<b))
                               (aa'⊆ab x x∈)
                               (sym∼ _ _ _
                                (∼-monotone≤ (ℚ.min≤' _ _) x∼a)))))
                in isTrans≤ᵣ _ _ _
                     (isTrans≡≤ᵣ _ _ _
                       (cong₂ _+ᵣ_ refl
                         (cong rat
                    (distℚ! ε ·[
                         (ge[ ℚ.[ 1 / 4 ] ])
                       ≡  ((neg-ge ge[ ℚ.[ 1 / 2 ] ]) +ge ge1)
                         +ge (neg-ge  ge[ ℚ.[ 1 / 4 ] ] ) ]) ∙ sym (+ᵣ-rat _ _)
                           ∙ cong₂ _+ᵣ_ (sym (+ᵣ-rat _ _)
                            ∙ cong₂ _+ᵣ_ (sym (-ᵣ-rat _)) refl)
                             (sym (-ᵣ-rat _))) ∙ +ᵣAssoc _ _ _)
                       (≤ᵣ-+o _ _ _ (isTrans≡≤ᵣ _ _ _
                         (+ᵣAssoc _ _ _ ∙ +ᵣComm _ _) (<ᵣWeaken≤ᵣ _ _
                         ((isTrans≤<ᵣ _ _ _
                           (≤ᵣ-o+ _ _ _ zzz)
                           (a<b-c⇒a+c<b _ _ _ ε<πn)))))))
                     zzz')
             (Integral'-+ a a' (<ᵣWeaken≤ᵣ _ _ a<a') _ _ _ _
                ((snd (Integrate-UContinuous∈ a a' (<ᵣWeaken≤ᵣ _ _ a<a') f
                  (IsUContinuousℙ-restr _ _ _ aa'⊆ab fUC))))
                (Integral'Const a a' (<ᵣWeaken≤ᵣ _ _ a<a')
                 (rat (fst (/4₊ (ε , 0<ε))))))
             (snd (Integrate-UContinuous∈ a a' (<ᵣWeaken≤ᵣ _ _ a<a') f'
                  (IsUContinuousℙ-restr _ _ _ aa'⊆ab fUC'))))))
           (Integral'-≤ a' b a'≤b f f' _ _
             (λ x x∈ → f≤f' x
               (isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a<a') (fst x∈) , snd x∈))
             (snd (Integrate-UContinuous∈ a' b a'≤b f
                  (IsUContinuousℙ-restr _ _ _ a'b⊆ab fUC)))
             (snd (Integrate-UContinuous∈ a' b a'≤b f'
                  (IsUContinuousℙ-restr _ _ _ a'b⊆ab fUC'))))) ∣₁

IsUContinuousℙ-from∀ℚinterval : ∀ (f : ℝ → ℝ) →
                (∀ a b → rat a <ᵣ rat b →
                  IsUContinuousℙ (intervalℙ (rat a) (rat b)) (λ x _ → f x) )
               → ∀ a b → a ≤ᵣ b →
                ∥ IsUContinuousℙ (intervalℙ a b) (λ x _ → f x) ∥₁
IsUContinuousℙ-from∀ℚinterval f X a b a≤b =
  PT.map2
     (λ (a' , _ , a'<a) (b' , b<b' , _) →
       IsUContinuousℙ-restr (intervalℙ (rat a') (rat b'))
         (intervalℙ a b) (λ x _ → f x)
         (λ x x∈ → isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ a'<a) (fst x∈) ,
          isTrans≤ᵣ _ _ _ (snd x∈) (<ᵣWeaken≤ᵣ _ _ b<b'))
           (X a' b' (isTrans<ᵣ _ _ _ a'<a
           (isTrans≤<ᵣ _ _ _ a≤b b<b'))))
   (denseℚinℝ (a +ᵣ (rat -1)) a (isTrans<≡ᵣ _ _ _

        (<ᵣ-o+ _ _ a (decℚ<ᵣ? { -1 } {0}))
        (+IdR a)))
   (denseℚinℝ b (b +ᵣ 1) (isTrans≡<ᵣ _ _ _
        (sym (+IdR b))
        (<ᵣ-o+ _ _ b (decℚ<ᵣ? {0} {1}))) )

π-seq : ℕ → ℝ
π-seq zero = 0
π-seq (suc n) = π-seq n +ᵣ cos (π-seq n)

π-seq≡Σdiffs : ∀ n →
  π-seq n ≡
    seqΣ (λ k → π-seq (suc k) -ᵣ π-seq k) n
π-seq≡Σdiffs (zero) = refl
π-seq≡Σdiffs (suc n) = cong₂ _+ᵣ_ (π-seq≡Σdiffs n)
   (sym L𝐑.lem--063)

∫sin : ∀ a b → a ≤ᵣ b → on[ a , b ]IntegralOf (λ x _ _ → sin x) is
       (cos a -ᵣ cos b)
∫sin a b a≤b =
  PT.rec
   {A = IsUContinuousℙ (intervalℙ a b') (λ x _ → sin x)}
   (isPropΠ λ _ → squash₁)
   (λ iuc →
     let zz = FTOC⇐'' a b' a<b' _ _ iuc
              ((subst2 (uDerivativeOfℙ intervalℙ a b' ,_is_)
                      (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _) )
                      (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _) ∙ -ᵣInvol _ )
                      (C·uDerivativeℙ (intervalℙ a b') -1 _ _
                      (cos'=-sin-uder' a b' a<b')))) b
            (a≤b , <ᵣWeaken≤ᵣ _ _ b<b')
     in subst {x = (-ᵣ cos b -ᵣ -ᵣ cos a)} {cos a -ᵣ cos b}
          (on[ a , b ]IntegralOf (λ x _ _ → sin x) is_)

          (sym (-ᵣDistr (cos b) (-ᵣ cos a))
           ∙ -[x-y]≡y-x (cos b) (cos a)) zz
          )
   (IsUContinuousℙ-from∀ℚinterval _ pre-uContSin a b' (<ᵣWeaken≤ᵣ _ _ a<b'))
 where
 b' = b +ᵣ 1
 b<b' : b <ᵣ b'
 b<b' = isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ _ _ _ (decℚ<ᵣ? {0} {1}))
 a<b' : a <ᵣ b'
 a<b' = isTrans≤<ᵣ _ _ _ a≤b b<b'

absᵣDiff≡max-min : ∀ a b → absᵣ (a -ᵣ b) ≡ maxᵣ a b -ᵣ minᵣ a b
absᵣDiff≡max-min a b = sym (absᵣ-min-max a b) ∙
  absᵣNonNeg _ ((x≤y→0≤y-x _ _
            (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (≤maxᵣ _ _))))


opaque
 unfolding minᵣ
 absᵣdiffCont : ∀ f → IsContinuous f → ∀ a b →
       absᵣ (f (minᵣ a b) -ᵣ f (maxᵣ a b)) ≡
       absᵣ (f a -ᵣ f b)
 absᵣdiffCont f fC =
   ≡Cont₂ (cont∘₂ IsContinuousAbsᵣ
       (IsContinuous-₂∘
         (cont∘₂ fC (contNE₂ minR ))
         (cont∘₂ fC (contNE₂ maxR))))
     (cont∘₂ IsContinuousAbsᵣ
        (IsContinuous-₂∘ ((λ _ → IsContinuousConst _) , λ _ → fC)
         ((λ _ → fC) , λ _ → IsContinuousConst _)))
      (ℚ.elimBy≤ (λ x y →
        cong absᵣ (cong₂ _-ᵣ_ (cong f (minᵣComm (rat y) (rat x)))
         ((cong f (maxᵣComm (rat y) (rat x)))))
          ∙∙_∙∙ minusComm-absᵣ _ _ )
          λ x y x≤y →
           cong absᵣ
            ((cong₂ _-ᵣ_ (cong f (≤→minᵣ (rat x) (rat y) (≤ℚ→≤ᵣ _ _ x≤y)))
         ((cong f (≤→maxᵣ (rat x) (rat y) (≤ℚ→≤ᵣ _ _ x≤y)))))))

cosDiffBound : ∀ a b → absᵣ (cos a -ᵣ cos b) ≤ᵣ absᵣ (a -ᵣ b)
cosDiffBound a b = subst2 _≤ᵣ_
   (absᵣdiffCont cos isContinuousCos a b)
   (sym (absᵣDiff≡max-min a b))
   zz'

 where
  a⊓b≤a⊔b = (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (≤maxᵣ _ _))
  zz' : absᵣ (cos (minᵣ a b) -ᵣ cos (maxᵣ a b)) ≤ᵣ maxᵣ a b -ᵣ minᵣ a b
  zz' = PT.rec (isProp≤ᵣ _ _)
         (λ iuc →
            let intCos = ((Integrate-UContinuousℙ _ _ a⊓b≤a⊔b _
                       (IsUContinuous∘ℙ _
                         IsUContinuousAbsᵣ iuc)))
            in isTrans≤ᵣ _ _ _ (Integral'-abs≤ (minᵣ a b) (maxᵣ a b)
                a⊓b≤a⊔b
                 sin
                 _
                 _
                 (∫sin _ _ ((isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (≤maxᵣ _ _))))
                 (snd intCos))
                    (Integral'-≤ (minᵣ a b) (maxᵣ a b)
                      ((isTrans≤ᵣ _ _ _ (min≤ᵣ _ _)
                     (≤maxᵣ _ _)))
                     (λ x → absᵣ (sin x)) _ _ _
                      (λ x _ → ∣sin∣≤1 x) (snd intCos)
                      (Integral'Const1
                    (minᵣ a b) (maxᵣ a b) a⊓b≤a⊔b)))

                (IsUContinuousℙ-from∀ℚinterval _ pre-uContSin (minᵣ a b) (maxᵣ a b)
                   a⊓b≤a⊔b)




∫cos : ∀ a b → a ≤ᵣ b → on[ a , b ]IntegralOf (λ x _ _ → cos x) is
       (sin b -ᵣ sin a)
∫cos a b a≤b =
  PT.rec
     {A = IsUContinuousℙ (intervalℙ a b') (λ x _ → cos x)}
     (isPropΠ λ _ → squash₁)
     (λ iuc →
         FTOC⇐'' a b' a<b' _ _ iuc
              (sin'=cos-uder' a b' a<b') b
              (a≤b , <ᵣWeaken≤ᵣ _ _ b<b'))
     (IsUContinuousℙ-from∀ℚinterval _ pre-uContCos a b' (<ᵣWeaken≤ᵣ _ _ a<b'))


 where
 b' = b +ᵣ 1
 b<b' : b <ᵣ b'
 b<b' = isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ _ _ _ (decℚ<ᵣ? {0} {1}))
 a<b' : a <ᵣ b'
 a<b' = isTrans≤<ᵣ _ _ _ a≤b b<b'

sinDiffBound : ∀ a b → absᵣ (sin a -ᵣ sin b) ≤ᵣ absᵣ (a -ᵣ b)
sinDiffBound a b =
 subst2 _≤ᵣ_
   (minusComm-absᵣ _ _ ∙ absᵣdiffCont sin isContinuousSin a b)
   (sym (absᵣDiff≡max-min a b))
   zz'

 where
  a⊓b≤a⊔b = (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (≤maxᵣ _ _))
  zz' : absᵣ (sin (maxᵣ a b) -ᵣ sin (minᵣ a b)) ≤ᵣ maxᵣ a b -ᵣ minᵣ a b
  zz' =
    PT.rec (isProp≤ᵣ _ _)
         (λ iuc →
            let intSin = ((Integrate-UContinuousℙ _ _ a⊓b≤a⊔b _
                       (IsUContinuous∘ℙ _
                         IsUContinuousAbsᵣ iuc)))
            in isTrans≤ᵣ _ _ _ (Integral'-abs≤ (minᵣ a b) (maxᵣ a b)
                a⊓b≤a⊔b
                 cos
                 _
                 _
                 ((∫cos _ _ ((isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (≤maxᵣ _ _)))))
                  --
                 (snd intSin))
                    (Integral'-≤ (minᵣ a b) (maxᵣ a b)
                      ((isTrans≤ᵣ _ _ _ (min≤ᵣ _ _)
                     (≤maxᵣ _ _)))
                     (λ x → absᵣ (cos x)) _ _ _
                      (λ x _ → ∣cos∣≤1 x) ((snd intSin))
                      (Integral'Const1
                    (minᵣ a b) (maxᵣ a b) a⊓b≤a⊔b)))

                ((IsUContinuousℙ-from∀ℚinterval _
                 pre-uContCos (minᵣ a b) (maxᵣ a b)
                   a⊓b≤a⊔b))


0＃∣cos∣→∣sin∣<1 : ∀ x → 0 ＃ (cos x)  → absᵣ (sin x) <ᵣ 1
0＃∣cos∣→∣sin∣<1 x 0＃cos =
  x²<1→∣x∣<1 _ (isTrans<≡ᵣ _ _ _
    (isTrans≡<ᵣ _ _ _
      (sym (+IdR _)) (<ᵣ-o+ _ _ _ 0<cos²)) (sin²+cos²=1 x))

 where
 0<cos² : 0 <ᵣ (cos x ^ⁿ 2)
 0<cos² = isTrans<≡ᵣ _ _ _
  (0<x^ⁿ _ 2 (0＃→0<abs _ 0＃cos))
  (sym (absᵣ^ⁿ (cos x) 2) ∙ sym (abs[x^²ⁿ] 1 (cos x)))


t<π-seq→0<cos[t] : ∀ t n →
  0 ≤ᵣ t →  t ≤ᵣ (π-seq (suc n)) → 0 <ᵣ cos t

0<η-seq[n] : ∀ n → 0 <ᵣ π-seq (suc n)

t<π-seq→0<cos[t] t zero 0≤t t≤0+1 =
    isTrans<≡ᵣ _ _ _
    (PT.elim
    (λ ich →
       isProp<ᵣ
        0
        (fromCauchySequence'₁ (seqΣ (λ k → cosSeries k t)) ich)
        )
    (λ ich →
      (isTrans<≤ᵣ _ (rat [ 1 / 2 ]) _
          (decℚ<ᵣ? {0} {[ 1 / 2 ]})
          (isTrans≡≤ᵣ _ _ _
            (sym (fromCauchySequence'-const _ _))

             (isTrans≤≡ᵣ _ _ _
              (fromCauchySequence'≤ (λ _ → rat [ 1 / 2 ])
                (isCauchySequence'-const _) _ _
                 λ n →
                  isTrans≤ᵣ _ _ _
                    (isTrans≤≡ᵣ _ _ _
                      (a≤b-c⇒c≤b-a _ _ _
                       (isTrans≤≡ᵣ _ _ _
                        (isTrans≡≤ᵣ _ _ _
                         (sym (expSeq'≡expSeq _ _))
                         (invEq (z/y≤x₊≃z≤y₊·x _ _ _)
                           (isTrans≤≡ᵣ _ 1 _
                            (^≤1 t 0≤t 2 t≤1)
                            (decℚ≡ᵣ? {1} {[ pos (1 ℕ.· 2 !) / 1 ]
                             ℚ.· ([ pos 1 / 1 ] ℚ.- [ 1 / 2 ])} ∙ rat·ᵣrat _ _))))
                        (sym (-ᵣ-rat₂ _ _))))
                      (sym (+IdL _)))
                    (isTrans≤≡ᵣ _ _ _
                      (seqΣ-truncateNonNeg _ w 1 (suc n)
                       (ℕ.suc-≤-suc (ℕ.zero-≤ {n})))
                      (sym (seqΣ∘·2 _ _)) ))
             ((sym (snd (cauchySequenceFaster (seqΣ (λ k → cosSeries k t))
          (λ n → ((suc n) ℕ.· 2) ,
           subst (ℕ._≤ ((suc n) ℕ.· 2)) (·-identityʳ n)
            (
             ℕ.≤monotone· (ℕ.≤-sucℕ {n}) (ℕ.≤-sucℕ {1})
            )) ich))))))
          ))
    (cos-ch t)) (sym (cosImpl _))

  where
  t≤1 = (isTrans≤≡ᵣ _ _ _ t≤0+1
                                ( (+IdL _) ∙ cos0=1))
  w : (k : ℕ) →
      0 ≤ᵣ cosSeries (k ℕ.· 2) t +ᵣ cosSeries (suc (k ℕ.· 2)) t
  w k = isTrans≤≡ᵣ _ _ _
     (x≤y→0≤y-x _ _
         (invEq (z/y'≤x/y≃y₊·z≤y'₊·x _ _ _ _)
          (≤ᵣ₊Monotone·ᵣ _ _ _ _
           (<ᵣWeaken≤ᵣ _ _
            (snd (ℚ₊→ℝ₊
       ([ pos (suc (k ℕ.· 2) ℕ.· 2 !) / 1 ] ,
        ℚ.<→0< [ pos (suc (k ℕ.· 2) ℕ.· 2 !) / 1 ]
        (ℚ.<ℤ→<ℚ 0 (pos (suc (k ℕ.· 2) ℕ.· 2 !))
         (ℤ.ℕ≤→pos-≤-pos (suc 0) (suc (k ℕ.· 2) ℕ.· 2 !)
          (ℕ.0<! (suc (k ℕ.· 2) ℕ.· 2))))))))
            (0≤x^ⁿ t (suc (k ℕ.· 2) ℕ.· 2) 0≤t)
            ((≤ℚ→≤ᵣ _ _
             (ℚ.≤ℤ→≤ℚ _ _
              (ℤ.ℕ≤→pos-≤-pos _ _
               (ℕ.Monotone! (ℕ.≤SumRight {k = 2}))))))
                (^ⁿ-MonotoneR-inv t 0≤t t≤1 _ _
                  ((ℕ.≤SumRight {k ℕ.· 2 ℕ.· 2} {2}))))))
     (cong₂ _+ᵣ_
       (sym (-1ⁿ·-·2 k _) ∙ cong (-1ⁿ· _) (expSeq'≡expSeq _ _))
       (cong -ᵣ_ (sym (-1ⁿ·-·2 k _))  ∙ sym (-1ⁿ·-suc _ _) ∙ cong (-1ⁿ· _) (expSeq'≡expSeq _ _)))

t<π-seq→0<cos[t] t n@(suc n-1) 0≤t t≤ =
 fst (propTruncIdempotent≃ (isProp<ᵣ _ _)) $ do
   let 0<cos[seq[n]]
          = (t<π-seq→0<cos[t] (π-seq n) n-1
               (<ᵣWeaken≤ᵣ _ _ (0<η-seq[n] n-1)) (≤ᵣ-refl _))
   (ε₊@(ε , 0<ε) , ε<πn) ← lowerℚBound _ 0<cos[seq[n]]

   (δ , X) ← isContinuousCos (π-seq n) ε₊

   z ← Dichotomyℝ' (π-seq n)
          t ((π-seq n) +ᵣ rat (fst δ))
           ((isTrans≡<ᵣ _ _ _
              (sym (+IdR _))
                 (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ δ)))))
   ⊎.rec
     (λ t<πn+1 →
       do zz ← Dichotomyℝ' (π-seq n -ᵣ rat (fst δ))
               t (π-seq n) (isTrans<≡ᵣ _ _ _
                 (<ᵣ-o+ _ _ _
                  (isTrans<≡ᵣ _ _ _
                   (-ᵣ<ᵣ _ _ (snd (ℚ₊→ℝ₊ δ)))
                   (-ᵣ-rat 0))) (+IdR _))
          ⊎.rec
            (∣_∣₁ ∘ t<π-seq→0<cos[t] t n-1 0≤t ∘ <ᵣWeaken≤ᵣ _ _ )
            (λ πn-δ<t →
              let zwz = isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                    (fst (∼≃abs<ε _ _ _)
                     (X t (invEq (∼≃abs<ε _ _ _)
                      (isTrans≡<ᵣ _ _ _
                       (abs-max _)
                       (max<-lem _ _ _
                        (a-b<c⇒a-c<b _ _ _ πn-δ<t)
                        (isTrans≡<ᵣ _ _ _
                         (-[x-y]≡y-x _ _)
                         (a<c+b⇒a-c<b _ _ _ t<πn+1)))))))
              in ∣ isTrans<ᵣ _ _ _ (x<y→0<y-x _ _ ε<πn )
                   (a-b<c⇒a-c<b _ _ _ zwz) ∣₁)
            zz)
       (λ πn<t →
         return $ isTrans≡<ᵣ _ (-ᵣ (π-seq (suc n) -ᵣ π-seq n) +ᵣ cos (π-seq n )) _
            (sym (𝐑'.+InvL' _ _ (sym (+ᵣAssoc _ _ _) ∙ L𝐑.lem--05)))
            (isTrans<≡ᵣ _ _ _ (<ᵣ-+o _ _ _ (-ᵣ<ᵣ _ _
              (isTrans<≤ᵣ _ _ _

                (Integral'-< (π-seq n) t (πn<t)
                  sin (const 1)  (cos (π-seq (suc n-1)) -ᵣ cos t)
                    (t -ᵣ π-seq (suc n-1) )  (λ x _ → sin≤1 x)
                    (IsUContinuousℙ-from∀ℚinterval _ pre-uContSin _ _
                      (<ᵣWeaken≤ᵣ _ _ πn<t))
                    ∣ IsUContinuousℙ-const _ 1 ∣₁
                  (∫sin (π-seq n) t (<ᵣWeaken≤ᵣ _ _ πn<t))
                    (Integral'Const1 (π-seq n) t (<ᵣWeaken≤ᵣ _ _ πn<t))
                   ((isTrans≤<ᵣ _ _ _ (≤absᵣ _) (0＃∣cos∣→∣sin∣<1
                     (π-seq (suc n-1))
                       (inl 0<cos[seq[n]]))))
                   )
                (≤ᵣ-+o _ _ _
                  t≤))))
            (cong₂ _+ᵣ_ (-[x-y]≡y-x _ _) refl
             ∙ 𝐑'.minusPlus (cos t) (cos (π-seq n )) )))
     z

0<η-seq[n] zero =
  isTrans<≡ᵣ _ _ _
   (decℚ<ᵣ? {0} {1})
   (sym cos0=1 ∙ sym (+IdL _))
0<η-seq[n] (suc n) =
 isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat 0 0))
  (<ᵣMonotone+ᵣ _ _ _ _
    (0<η-seq[n] n)
     (t<π-seq→0<cos[t] (π-seq n +ᵣ cos (π-seq n)) n
      (<ᵣWeaken≤ᵣ _ _ (0<η-seq[n] n)) (≤ᵣ-refl _)))

π-seq-incr : ∀ n → π-seq n <ᵣ π-seq (suc n)
π-seq-incr zero = 0<η-seq[n] zero
π-seq-incr (suc n) =
  isTrans≡<ᵣ _ _ _
    (sym (+IdR _))
     (<ᵣ-o+ 0 _ (π-seq (suc n))
      (t<π-seq→0<cos[t] (π-seq n +ᵣ cos (π-seq n)) n
      (<ᵣWeaken≤ᵣ _ _ (0<η-seq[n] n)) (≤ᵣ-refl _)))

π-seq-monotoneStrict : ∀ m n → m ℕ.< n → π-seq m <ᵣ π-seq n
π-seq-monotoneStrict m n (zero , p) =
  isTrans<≡ᵣ _ _ _
   (π-seq-incr m)
   (cong π-seq p)
π-seq-monotoneStrict m zero m<0 = ⊥.rec (ℕ.¬-<-zero m<0)
π-seq-monotoneStrict m (suc n) (suc k , p) =
  isTrans<ᵣ _ _ _
    (π-seq-monotoneStrict m n (k , ℕ.injSuc p))
     (π-seq-incr n)

π-seq-monotone : ∀ m n → m ℕ.≤ n → π-seq m ≤ᵣ π-seq n
π-seq-monotone m n =
    ⊎.rec
      (<ᵣWeaken≤ᵣ _ _ ∘ π-seq-monotoneStrict m n)
      (≡ᵣWeaken≤ᵣ _ _ ∘ cong π-seq)
  ∘ ℕ.≤-split


π-seq1=1 : π-seq 1 ≡ 1
π-seq1=1 = (+IdL _) ∙ cos0=1

sin[1]≤sin[t] : ∀ t n →  1 <ᵣ t → t ≤ᵣ (π-seq (suc n))
       → sin 1 ≤ᵣ sin t
sin[1]≤sin[t] t zero x x₁ = ⊥.rec (≤ᵣ→≯ᵣ _ _ x₁
  (isTrans≡<ᵣ _ _ _ π-seq1=1 x))
sin[1]≤sin[t] t n@(suc n') 1<t t≤π-seq-sn =
  x<y+δ→x≤y _ _ λ ε → fst (propTruncIdempotent≃ (isProp<ᵣ _ _)) $ do
    cosC ← IsUContinuousℙ-from∀ℚinterval cos pre-uContCos 1 t (<ᵣWeaken≤ᵣ _ _ 1<t)
    ((𝒕 , 𝒕∈) , T) ← meanValue 1 t 1<t
            (≤ᵣ-refl 1 , <ᵣWeaken≤ᵣ _ _ 1<t)
            (<ᵣWeaken≤ᵣ _ _ 1<t , ≤ᵣ-refl t)
            (λ x _ → sin x)
            (λ x _ → cos x)
            cosC
            (sin'=cos-uder' 1 t 1<t)
            ε

    ∣ isTrans<≡ᵣ
       (sin 1)
       (rat (fst ε) +ᵣ sin t)
       (sin t +ᵣ rat (fst ε))
       (a-b<c⇒a<c+b
         (sin 1)
         (sin t)
         (rat (fst ε))
         (isTrans≤<ᵣ _ _ _
         (isTrans≤ᵣ _ _ _
          (isTrans≡≤ᵣ _ _ _
            (sym (+IdL _))
            (≤ᵣ-+o _ _ _
              (<ᵣWeaken≤ᵣ _ _
               (snd ((_ ,
                 t<π-seq→0<cos[t] 𝒕 n
                   (isTrans≤ᵣ _ _ _ (decℚ≤ᵣ? {0} {1}) (fst 𝒕∈))
                   (isTrans≤ᵣ _ _ _ (snd 𝒕∈) t≤π-seq-sn) )
                  ₊·ᵣ (_ , (x<y→0<y-x _ _ 1<t)))))))
           (isTrans≤≡ᵣ _ _ _
             (≤absᵣ _)
             (cong absᵣ (+ᵣAssoc _ _ _) ∙ minusComm-absᵣ _ _ ∙ cong absᵣ
               (cong₂ _+ᵣ_ refl (-ᵣDistr _ _ ∙ +ᵣComm _ _)
                 ∙ +ᵣAssoc _ _ _ )))) T))
        (+ᵣComm _ _) ∣₁


π-seq-dist : ∀ n → π-seq (suc (suc (suc (suc n)))) -ᵣ π-seq (suc (suc (suc n)))
                   ≤ᵣ (1 -ᵣ sin 1) ·ᵣ (π-seq (suc (suc (suc n))) -ᵣ π-seq (suc (suc n)))
π-seq-dist n' =
 x<y+δ→x≤y _ _
   λ ε →
     fst (propTruncIdempotent≃ (isProp<ᵣ _ _)) $ do
      sinC ← IsUContinuousℙ-from∀ℚinterval sin pre-uContSin
           (π-seq n) (π-seq (suc n)) (<ᵣWeaken≤ᵣ _ _ (π-seq-incr n))
      ((t , t∈) , T) ← meanValue (π-seq n) (π-seq (suc n)) (π-seq-incr n)
         (≤ᵣ-refl _ , π-seq-monotone n (suc n) ℕ.≤-sucℕ)
         (π-seq-monotone n (suc n) ℕ.≤-sucℕ , ≤ᵣ-refl _)
          (λ x _ → cos x) (λ x _ → -ᵣ sin x)
         (IsUContinuousℙ-ᵣ∘ _ (λ x _ → sin x) sinC)
         (cos'=-sin-uder' (π-seq n) (π-seq (suc n)) (π-seq-incr n)) ε
      let zz =
             isTrans<≡ᵣ _ _ _
               (a-b<c⇒a<c+b _ _ _ (isTrans≤<ᵣ _ _ _ (≤absᵣ _) (isTrans≡<ᵣ _ _ _
             (cong absᵣ
              (cong₂ _-ᵣ_ (L𝐑.lem--041 ∙ +ᵣComm _ _) (
               (·DistR+ _ _ _
                ∙ cong₂ _+ᵣ_  (·IdL _) refl) ∙ +ᵣComm _ _)
                ∙ L𝐑.lem--075))
             T))) (+ᵣComm _ _)
      ∣ isTrans<≤ᵣ _ _ _ zz
        (≤ᵣ-+o _ _ (rat (fst ε))
          (≤ᵣ-·ᵣo
               (rat [ pos 1 / 1+ 0 ] +ᵣ -ᵣ sin t)
               (rat [ pos 1 / 1+ 0 ] -ᵣ sin 1)
              (π-seq (suc n) -ᵣ π-seq n)
               (x≤y→0≤y-x _ _
                 (<ᵣWeaken≤ᵣ _ _ (π-seq-incr n)))
                  (≤ᵣ-o+ _ _ 1
                    (-ᵣ≤ᵣ _ _
                      (sin[1]≤sin[t] t (suc (suc n'))
                        (isTrans<≤ᵣ _ _ _ (
                          isTrans≡<ᵣ _ _ _
                           (sym ((+IdL _) ∙ cos0=1))
                            (π-seq-monotoneStrict 1 n
                             (ℕ.suc-≤-suc (ℕ.zero-<-suc {n'}))))
                            (fst t∈)) (snd t∈))
                       )))
          ) ∣₁

 where
 n = suc (suc n')


0<sin1 : 0 <ᵣ sin 1
0<sin1 = isTrans<≡ᵣ _ _ _
       (Integral'-< 0 1 (decℚ<ᵣ? {0} {1}) (λ _ → 0) cos
         0 (sin 1 -ᵣ sin 0)  (λ x x∈ → <ᵣWeaken≤ᵣ _ _
            (t<π-seq→0<cos[t] x 0 (fst x∈)
               (isTrans≤≡ᵣ _ _ _ (snd x∈) (sym π-seq1=1))))
                 ∣ IsUContinuousℙ-const _ 0 ∣₁
                 (IsUContinuousℙ-from∀ℚinterval cos pre-uContCos 0 1
                  (decℚ≤ᵣ? {0} {1}))
           (Integral'Const0 0 1 (decℚ≤ᵣ? {0} {1}))
           ((invEq (clampᵣ-IntegralOf 0 1 (decℚ≤ᵣ? {0} {1}) cos (sin 1 -ᵣ sin 0))
             (∫cos 0 1 (decℚ≤ᵣ? {0} {1}))))
           (isTrans<≡ᵣ _ _ _ (decℚ<ᵣ? {0} {1})
             (sym cos0=1))) (𝐑'.+IdR' _ _ (cong -ᵣ_ sin0=0 ∙ -ᵣ-rat 0))


π-seq-distⁿ : ∀ n m → π-seq (suc (suc (suc (m ℕ.+ n))))
                      -ᵣ π-seq (suc (suc (m ℕ.+ n)))
                   ≤ᵣ (1 -ᵣ sin 1) ^ⁿ m ·ᵣ
                     (π-seq (suc (suc (suc n))) -ᵣ π-seq (suc (suc n)))
π-seq-distⁿ n zero = ≡ᵣWeaken≤ᵣ _ _ (sym (·IdL _))
π-seq-distⁿ n (suc m) =
  isTrans≤ᵣ _ _ _
   (π-seq-dist (m ℕ.+ n))
   (isTrans≤≡ᵣ _ _ _
     (≤ᵣ-o·ᵣ _ _ (1 -ᵣ sin 1)
     (x≤y→0≤y-x _ _ (sin≤1 _))
     (π-seq-distⁿ n m))
     ( (·ᵣAssoc _ _ _) ∙ cong₂ _·ᵣ_ (·ᵣComm _ _) refl))

isConvSeriesΣπ-seq-diffs : ∥ (IsConvSeries'
  λ n → (π-seq (suc n) -ᵣ π-seq n)) ∥₁
isConvSeriesΣπ-seq-diffs =
 PT.map
  (λ (η , 1-sin1<η , η<1) →
    ratioTest₊≤ (λ n → π-seq (suc n) -ᵣ π-seq n)
       (1 , (λ n → isTrans≡≤ᵣ _ _ _
          (cong absᵣ L𝐑.lem--063)
          (∣cos∣≤1 (π-seq n))))
       (η , ℚ.<→0< _ (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _
        (x≤y→0≤y-x _ _ (sin≤1 _))
        1-sin1<η)
         )) (<ᵣ→<ℚ _ _ η<1)
      (λ n → (x<y→0<y-x _ _ (π-seq-incr n)))

      (1 , λ n 3<n → isTrans≤<ᵣ _ _ _
          (zz n 3<n)
           1-sin1<η))
   (denseℚinℝ (1 -ᵣ sin 1) 1
     (isTrans<≡ᵣ _ _ _
       (<ᵣ-o+ _ _ _ (-ᵣ<ᵣ _ _ 0<sin1))
      (cong₂ _+ᵣ_ refl (-ᵣ-rat 0) ∙ +IdR 1)))
  where
  zz :  (n : ℕ) →
         1 ℕ.< n →
         absᵣ ((π-seq (suc (suc n)) -ᵣ π-seq (suc n)) ／ᵣ[
          π-seq (suc n) -ᵣ π-seq n , inl
            (x<y→0<y-x _ _ (π-seq-incr n)) ])
            ≤ᵣ 1 -ᵣ sin 1
  zz zero x = ⊥.rec (ℕ.¬-<-zero x)
  zz (suc zero) x = ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred x ))
  zz (suc (suc n)) _ =
    isTrans≡≤ᵣ _ _ _
      (cong absᵣ (cong₂ _·ᵣ_ refl
          (sym (invℝ₊≡invℝ (_ ,
           (x<y→0<y-x _ _ (π-seq-incr (suc (suc n))))) _)) )
        ∙ absᵣPos _ (snd
          ((_ , (x<y→0<y-x _ _ (π-seq-incr (suc (suc (suc n))))))
            ₊·ᵣ invℝ₊ (_ , (x<y→0<y-x _ _ (π-seq-incr (suc (suc n))))))))
      (invEq (z/y≤x₊≃z≤y₊·x _ _ _)
        (isTrans≤≡ᵣ _ _ _
         (π-seq-dist n)
         (·ᵣComm _ _)))


π-seq-cauchy : ∥ IsCauchySequence' π-seq ∥₁
π-seq-cauchy = PT.map (λ X → subst IsCauchySequence'
  (sym (funExt π-seq≡Σdiffs))
  (fst (IsConvSeries'≃IsCauchySequence'Sum
    (λ n → π-seq (suc n) -ᵣ π-seq n)) X)) isConvSeriesΣπ-seq-diffs


opaque
 π-number/2 : ℝ
 π-number/2 = fromCauchySequence'₁ π-seq π-seq-cauchy

 π-seq-lim : ∥ lim'ₙ→∞ π-seq is π-number/2  ∥₁
 π-seq-lim = do
  ics ← π-seq-cauchy
  ∣ subst (lim'ₙ→∞ π-seq is_)
    (fromCauchySequence'₁-≡-lem _ ∣ ics ∣₁ π-seq-cauchy)
     (fromCauchySequence'-lim _ ics) ∣₁

π-number : ℝ
π-number = 2 ·ᵣ π-number/2


Lipschitz-cos : Lipschitz-ℝ→ℝ 1 cos
Lipschitz-cos u v ε x =
  invEq (∼≃abs<ε _ _ _)
    ((isTrans≤<ᵣ _ _ _ (cosDiffBound u v)

        (fst (∼≃abs<ε _ _ (1 ℚ₊· ε)) (subst∼ (sym (ℚ.·IdL _)) x))))

Lipschitz-sin : Lipschitz-ℝ→ℝ 1 sin
Lipschitz-sin u v ε x =
  invEq (∼≃abs<ε _ _ _)
    ((isTrans≤<ᵣ _ _ _ (sinDiffBound u v)

        (fst (∼≃abs<ε _ _ (1 ℚ₊· ε)) (subst∼ (sym (ℚ.·IdL _)) x))))


0≤η-seq[n] : ∀ n → 0 ≤ᵣ π-seq n
0≤η-seq[n] zero = ≤ᵣ-refl 0
0≤η-seq[n] (suc n) = <ᵣWeaken≤ᵣ _ _  (0<η-seq[n] n)

opaque
 unfolding π-number/2

 1<π-number/2 : 1 <ᵣ π-number/2
 1<π-number/2 = isTrans<≤ᵣ _ (π-seq 2) _
   (isTrans≡<ᵣ _ _ _ (sym (cos0=1) ∙ sym (+IdL _))
    (π-seq-incr 1))

  (isTrans≤≡ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _ (sym (fromCauchySequence'-const (π-seq 2) _ ) )
    (fromCauchySequence'₁≤ (λ _ → (π-seq 2)) (π-seq ∘ suc ∘ suc)
      ∣ isCauchySequence'-const (π-seq 2) ∣₁
         (PT.map (λ x → fst (cauchySequenceFaster
           π-seq (λ k → suc (suc k) , ℕ.≤-+k {0} {2} {k} (ℕ.≤-solver 0 2)) x))
            π-seq-cauchy)
        λ n → π-seq-monotone 2 (suc (suc n))
         (ℕ.≤-k+ {0} {n} {2} (ℕ.zero-≤ {n}))))
         (sym (fromCauchySequence'₁-∘+ π-seq 2 _ _)))


 0<π-number/2 : 0 <ᵣ π-number/2
 0<π-number/2 = isTrans<ᵣ _ _ _ (decℚ<ᵣ? {0} {1}) 1<π-number/2

π-number/2₊ : ℝ₊
π-number/2₊ = π-number/2 , 0<π-number/2

π-number₊ : ℝ₊
π-number₊ = 2 ₊·ᵣ (_ , 0<π-number/2)

0<cos-π-seq : ∀ n → 0 <ᵣ cos (π-seq n)
0<cos-π-seq n = t<π-seq→0<cos[t] (π-seq n) n (0≤η-seq[n] n)
  (<ᵣWeaken≤ᵣ _ _ (π-seq-incr n))


x²≡0→x≡0 : ∀ x → x ·ᵣ x ≡ 0 → x ≡ 0
x²≡0→x≡0 x x²=0 =
 fst (∼≃≡ _ _)
  (λ ε →
    invEq (∼≃abs<ε _ _ _)
     (isTrans≡<ᵣ _ _ _ (cong absᵣ (cong₂ _+ᵣ_ refl (-ᵣ-rat 0) ∙
         +IdR _ ))
         let uu = isTrans<≡ᵣ _ _ _
                     (isTrans≡<ᵣ _ _ _ (sym (·absᵣ _ _)
                    ∙ cong absᵣ (sym (cong₂ _+ᵣ_ refl (-ᵣ-rat 0) ∙
                   +IdR _ ))) (fst ((∼≃abs<ε _ _ _)) ((invEq (∼≃≡ _ _) x²=0)
                   (ε ℚ₊· ε))))
                   (rat·ᵣrat _ _)
         in PT.rec (isProp<ᵣ _ _)
             (⊎.rec (idfun _)
              λ ε/2<x → ⊥.rec
                let zz = (<ᵣ₊Monotone·ᵣ _ _ _ _
                           (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ (/2₊ ε))))
                           (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ (/2₊ ε))))
                            ε/2<x ε/2<x)
                 in isAsym<ᵣ 0
                     ((rat (fst (/2₊ ε))) ·ᵣ
                       (rat (fst (/2₊ ε))))
                        ((snd (ℚ₊→ℝ₊ (/2₊ ε) ₊·ᵣ ℚ₊→ℝ₊ (/2₊ ε))))
                         (isTrans<≡ᵣ _ _ _ zz
                           (sym (·absᵣ _ _) ∙ cong absᵣ x²=0 ∙
                            absᵣ0)))
             (Dichotomyℝ' (rat (fst (/2₊ ε))) (absᵣ x)
               (rat (fst ε))
               (<ℚ→<ᵣ _ _ (x/2<x ε)))))

opaque
 unfolding π-number/2
 cos[π/2]≡0 : cos π-number/2 ≡ 0
 cos[π/2]≡0 =
   PT.rec (isSetℝ _ _)
   (λ (η , 1-sin1<η , η<1) →
     snd (map-fromCauchySequence'₁ 1
      π-seq π-seq-cauchy cos Lipschitz-cos) ∙
       fromCauchySequence'₁≡ (cos ∘ π-seq)
        _ 0
         λ ε →
           let zwz = lim0FromRatioBound (cos ∘ π-seq)
                      (η , ℚ.<→0< _ (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _
                       (x≤y→0≤y-x _ _ (sin≤1 _))
                       1-sin1<η)
                        ))
                      (<ᵣ→<ℚ _ _ η<1) (1 , (λ _ → ∣cos∣≤1 _))
                      (inl ∘ 0<cos-π-seq) 1
                       (λ n x → isTrans≤<ᵣ _ _ _
                         (isTrans≡≤ᵣ _ _ _ (cong absᵣ
                           (cong₂ _·ᵣ_ (sym L𝐑.lem--063)
                            (cong (uncurry invℝ)
                              (Σ≡Prop (isProp＃ 0)
                               (sym L𝐑.lem--063))))) (zz n x))
                         1-sin1<η)
                       ε
            in ∣ zwz ∣₁)
    (denseℚinℝ (1 -ᵣ sin 1) 1
      (isTrans<≡ᵣ _ _ _
        (<ᵣ-o+ _ _ _ (-ᵣ<ᵣ _ _ 0<sin1))
       (cong₂ _+ᵣ_ refl (-ᵣ-rat 0) ∙ +IdR 1)))


  where


  zz :  (n : ℕ) →
         1 ℕ.< n →
         absᵣ ((π-seq (suc (suc n)) -ᵣ π-seq (suc n)) ／ᵣ[
          π-seq (suc n) -ᵣ π-seq n , inl
            (x<y→0<y-x _ _ (π-seq-incr n)) ])
            ≤ᵣ 1 -ᵣ sin 1
  zz zero x = ⊥.rec (ℕ.¬-<-zero x)
  zz (suc zero) x = ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred x ))
  zz (suc (suc n)) _ =
    isTrans≡≤ᵣ _ _ _
      (cong absᵣ (cong₂ _·ᵣ_ refl
          (sym (invℝ₊≡invℝ (_ ,
           (x<y→0<y-x _ _ (π-seq-incr (suc (suc n))))) _)) )
        ∙ absᵣPos _ (snd
          ((_ , (x<y→0<y-x _ _ (π-seq-incr (suc (suc (suc n))))))
            ₊·ᵣ invℝ₊ (_ , (x<y→0<y-x _ _ (π-seq-incr (suc (suc n))))))))
      (invEq (z/y≤x₊≃z≤y₊·x _ _ _)
        (isTrans≤≡ᵣ _ _ _
         (π-seq-dist n)
         (·ᵣComm _ _)))

π-num : ℝ
π-num = 2 ·ᵣ π-number/2

uContSin : ∀ P → IsUContinuousℙ P (λ x₁ _ → sin x₁)
uContSin = Lipschitz-ℝ→ℝ→IsUContinuousℙ _ _  Lipschitz-sin

uContCos : ∀ P → IsUContinuousℙ P (λ x₁ _ → cos x₁)
uContCos = Lipschitz-ℝ→ℝ→IsUContinuousℙ _ _ Lipschitz-cos


0≤x<π/2→0<cos[x] : ∀ x → 0 ≤ᵣ x → x <ᵣ π-number/2 → 0 <ᵣ cos x
0≤x<π/2→0<cos[x] x 0≤x x<π/2 =
  PT.rec2 (isProp<ᵣ _ _)
    (λ (ε , 0<ε , ε<) ics →
     let NN = ics (ε , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<ε))  -- ics
         z = snd NN (suc (fst NN)) (ℕ.≤-refl {suc (fst NN)})
         zz = <-o+-cancel _ _ _ $ isTrans≤<ᵣ _ _ _
          (isTrans≤≡ᵣ _ _ _
           (≤absᵣ _)
           (minusComm-absᵣ _ _))
          (isTrans<ᵣ _ _ _ z ε<)
     in t<π-seq→0<cos[t] x (fst NN) 0≤x
        (<ᵣWeaken≤ᵣ _ _ (<ᵣ-ᵣ _ _ zz)))
    (denseℚinℝ 0 _ (x<y→0<y-x _ _ x<π/2) )
    π-seq-lim

x≤π/2→0≤cos[x] : ∀ x → x ∈ intervalℙ 0 π-number/2 → 0 ≤ᵣ cos x
x≤π/2→0≤cos[x] x x∈ =
 isTrans≤≡ᵣ _ _ _
   (z (x ·ᵣ fst (invℝ₊ (_ , 0<π-number/2))))
   (cong cos (cong (clampᵣ 0 _) ([x/₊y]·yᵣ _ _) ∙
    sym (∈ℚintervalℙ→clampᵣ≡ 0 π-number/2 x x∈)))


  where
  z : (x : ℝ) →
       0 ≤ᵣ _
  z = ≤Cont (IsContinuousConst 0)
        (IsContinuous∘ _ _
         isContinuousCos
         (IsContinuous∘ _ _
           (IsContinuousClamp 0 (π-number/2))
           (IsContinuous·ᵣR (π-number/2))))

             (ℚ.byTrichotomy 1 w )
    where
    w : ℚ.TrichotomyRec 1
         (λ q → 0 ≤ᵣ cos _)
    w .ℚ.TrichotomyRec.lt-case m m<1 =
     let ww = max<-lem _ _ _  0<π-number/2
             (isTrans<≡ᵣ _ _ _
           (
             (<ᵣ-·ᵣo (rat m) 1 (_ , 0<π-number/2) (<ℚ→<ᵣ _ _ m<1)))
             (·IdL _))

     in <ᵣWeaken≤ᵣ _ _ (0≤x<π/2→0<cos[x]
         (clampᵣ 0 π-number/2 (rat m ·ᵣ π-number/2))
        (≤clampᵣ _ _ _ (<ᵣWeaken≤ᵣ 0 π-number/2 0<π-number/2))
         (isTrans≡<ᵣ _ (maxᵣ 0 ((rat m ·ᵣ π-number/2))) _
         (≤→minᵣ _ _ (<ᵣWeaken≤ᵣ _ _ ww))
         ww))
    w .ℚ.TrichotomyRec.eq-case =
      ≡ᵣWeaken≤ᵣ _ _ (sym cos[π/2]≡0 ∙
       cong cos (∈ℚintervalℙ→clampᵣ≡ 0 π-number/2 π-number/2
         (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _)
         ∙ cong (clampᵣ 0 π-number/2) (sym (·IdL _))))
    w .ℚ.TrichotomyRec.gt-case m 1<m =
      ≡ᵣWeaken≤ᵣ _ _
       ((sym cos[π/2]≡0 ∙
        cong cos (sym ((≤x→clampᵣ≡ 0 π-number/2 (rat m ·ᵣ π-number/2)
         ((<ᵣWeaken≤ᵣ 0 π-number/2 0<π-number/2))
          (isTrans≡≤ᵣ _ _ _ (sym (·IdL _))
           (<ᵣWeaken≤ᵣ _ _
             (<ᵣ-·ᵣo 1 (rat m) (_ , 0<π-number/2) (<ℚ→<ᵣ _ _ 1<m)))))) ) ))



module sin-cos-of-sum where

 module _ (b : ℝ) where
  g h g' h' : ℝ → ℝ
  g a = sin (a  +ᵣ b) -ᵣ (sin a ·ᵣ cos b +ᵣ cos a ·ᵣ sin b)



  h a = cos (a +ᵣ b) -ᵣ (cos a ·ᵣ cos b -ᵣ sin a ·ᵣ sin b)

  g' a = h a
  h' a = -ᵣ (g a)


  module _ (aQ bQ : ℝ) (a<b : aQ <ᵣ bQ) where


   gBd : Bounded (intervalℙ aQ bQ) (λ x _ → g x)
   gBd = (bounded-ᵣ _ _ _ (1 , λ x _ → ∣sin∣≤1 (x +ᵣ b))
                      (bounded-+ _ _ _
                        (bounded-· _ _ _ (bounded-sin _)
                          (1 , λ _ _ → ∣cos∣≤1 b))
                        (bounded-· _ _ _ (bounded-cos _)
                          (1 , λ _ _ → ∣sin∣≤1 b))))

   hBd : Bounded (intervalℙ aQ bQ) (λ x _ → h x)
   hBd = bounded-ᵣ _ _ _
          ((1 , λ x _ → ∣cos∣≤1 (x +ᵣ b)))
          (bounded-ᵣ _ _ _
            (bounded-· _ _ _ (bounded-cos _) (1 , λ _ _ → ∣cos∣≤1 b))
            (bounded-· _ _ _ (bounded-sin _) (1 , λ _ _ → ∣sin∣≤1 b)))


   gC : IsUContinuousℙ (intervalℙ aQ bQ) (λ x _ → g x)
   gC = IsUContinuousℙ+ᵣ₂ _ _ _
         (IsUContinuousℙ-transl _ b _ (uContSin _))
         (IsUContinuousℙ-ᵣ∘ _ _
           (IsUContinuousℙ+ᵣ₂ _ _ _
             (IsUContinuousℙ·ᵣ₂ _ _ _
               (bounded-sin _)
               (1 , λ _ _ → ∣cos∣≤1 b)
               (uContSin _)
               (IsUContinuousℙ-const _ _))
             (IsUContinuousℙ·ᵣ₂ _ _ _
               (bounded-cos _)
               (1 , λ _ _ → ∣sin∣≤1 b)
               (uContCos _)
               (IsUContinuousℙ-const _ _))))

   hC : IsUContinuousℙ (intervalℙ aQ bQ) (λ x _ → h x)
   hC = IsUContinuousℙ+ᵣ₂ _ _ _
           (IsUContinuousℙ-transl _ b _ (uContCos _))
           (IsUContinuousℙ-ᵣ∘ _ _
            (IsUContinuousℙ+ᵣ₂ _ _ _
              ((IsUContinuousℙ·ᵣ₂ _ _ _
               (bounded-cos _)
               (1 , λ _ _ → ∣cos∣≤1 b)
               (uContCos _)
               (IsUContinuousℙ-const _ _)))
              (IsUContinuousℙ-ᵣ∘ _ _(IsUContinuousℙ·ᵣ₂ _ _ _
               (bounded-sin _)
               (1 , λ _ _ → ∣sin∣≤1 b)
               (uContSin _)
               (IsUContinuousℙ-const _ _)))))


   P = (intervalℙ (aQ) (bQ))
   gD : uDerivativeOfℙ P ,
          (λ x _ → g x) is (λ x _ → g' x)
   gD = -uDerivativeℙ _ _ _ _ _
         (uDerivativeOfℙ-restr _ P
           _ _ (λ x (≤x , x≤) → ≤ᵣ-+o _ _ _ ≤x , ≤ᵣ-+o _ _ _ x≤)
           ((uDerivativeOfℙ-transl
              (intervalℙ (aQ +ᵣ b) (bQ +ᵣ b)) _ _ b
               (sin'=cos-uder' _ _ (<ᵣ-+o _ _ _ a<b))))
           )
          (+uDerivativeℙ _ _ _ _ _
            (·CuDerivativeℙ _ _ _ _ (sin'=cos-uder' _ _ a<b))
              ((subst
               (uDerivativeOfℙ intervalℙ (aQ) (bQ) ,
                 (λ r _ → cos r ·ᵣ sin b) is_)
            (funExt₂ λ _ _ → -ᵣ· _ _)
             (·CuDerivativeℙ _ _ _ _ (cos'=-sin-uder' _ _ a<b)))))

   hD : uDerivativeOfℙ (intervalℙ (aQ) (bQ)) ,
          (λ x _ → h x) is (λ x _ → h' x)
   hD = subst (uDerivativeOfℙ (intervalℙ (aQ) (bQ)) ,
          (λ x _ → h x) is_)
           (funExt₂ λ _ _ → sym (-ᵣDistr _ _))
           (-uDerivativeℙ _ _ _ _ _
            ((uDerivativeOfℙ-restr _ P
           _ _ (λ x (≤x , x≤) → ≤ᵣ-+o _ _ _ ≤x , ≤ᵣ-+o _ _ _ x≤)
           ((uDerivativeOfℙ-transl
              (intervalℙ (aQ +ᵣ b) (bQ +ᵣ b)) _ _ b
               (cos'=-sin-uder' _ _ (<ᵣ-+o _ _ _ a<b))))
           ))

             (subst (uDerivativeOfℙ intervalℙ (aQ) (bQ) ,
           (λ r _ → cos r ·ᵣ cos b -ᵣ sin r ·ᵣ sin b) is_)
           (funExt₂ λ _ _ → sym (-ᵣDistr _ _))
           (-uDerivativeℙ _ _ _ _ _
             (subst
               (uDerivativeOfℙ intervalℙ (aQ) (bQ) ,
                 (λ r _ → cos r ·ᵣ cos b) is_)
            (funExt₂ λ _ _ → -ᵣ· _ _)
             (·CuDerivativeℙ _ _ _ _ (cos'=-sin-uder' _ _ a<b)))
             ((·CuDerivativeℙ _ _ _ _ (sin'=cos-uder' _ _ a<b))))) )

   D[g²+f²] : uDerivativeOfℙ (intervalℙ (aQ) (bQ)) ,
          (λ x _ → g x ·ᵣ g x +ᵣ h x ·ᵣ h x) is (λ _ _ → 0)
   D[g²+f²] = subst (uDerivativeOfℙ (intervalℙ (aQ) (bQ)) ,
          (λ x _ → g x ·ᵣ g x +ᵣ h x ·ᵣ h x) is_)
           (funExt₂ λ _ _ →
              sym (·DistL+ _ _ _) ∙ cong (2 ·ᵣ_)
               (cong₂ _+ᵣ_ refl (-ᵣ· _ _) ∙
                𝐑'.+InvR' _ _ (·ᵣComm _ _))
                ∙ sym (rat·ᵣrat _ 0))
      (+uDerivativeℙ _ _ _ _ _
              (uDerivativeOfℙ² (aQ) (bQ) a<b
                _ _ gBd
                    gC
                    hBd
                    gD)
              (uDerivativeOfℙ² (aQ) (bQ) a<b
                _ _ hBd
                    hC
                    (-ᵣbounded _ _ gBd)
                    hD))

  [g²+f²]0 : g 0 ·ᵣ g 0 +ᵣ h 0 ·ᵣ h 0 ≡ 0
  [g²+f²]0 = cong₂ _+ᵣ_
            (cong₂ _·ᵣ_ g0 g0 ∙ sym (rat·ᵣrat 0 0))
            (cong₂ _·ᵣ_ h0 h0 ∙ sym (rat·ᵣrat 0 0))
              ∙ +ᵣ-rat 0 0
   where
   g0 : g 0 ≡ 0
   g0 = cong₂ _-ᵣ_ (cong sin (+IdL _))
         (cong₂ _+ᵣ_
          (𝐑'.0LeftAnnihilates' _ _ sin0=0)
          (𝐑'.·IdL' _ _ cos0=1)) ∙
           𝐑'.+InvR' _ _ (sym (+IdL _))

   h0 : h 0 ≡ 0
   h0 = cong₂ _-ᵣ_ (cong cos (+IdL _))
        ((cong₂ _-ᵣ_
          (𝐑'.·IdL' _ _ cos0=1)
          (𝐑'.0LeftAnnihilates' _ _ sin0=0)))
      ∙ 𝐑'.+InvR' _ _ (sym (+IdR _) ∙ cong₂ _+ᵣ_ refl (sym (-ᵣ-rat 0)))

  [g²+f²]=0-a<0 : ∀ a → a <ᵣ 0 → g a ·ᵣ g a +ᵣ h a ·ᵣ h a ≡ 0
  [g²+f²]=0-a<0 a a<0 =
    let z = nullDerivative→const a 0
          (≤ᵣ-refl a , <ᵣWeaken≤ᵣ _ _ a<0)
          (<ᵣWeaken≤ᵣ _ _ a<0 , ≤ᵣ-refl 0)
           a<0 _
           (D[g²+f²] a 0 a<0)
    in z ∙ [g²+f²]0

  [g²+f²]=0-0<a : ∀ a → 0 <ᵣ a → g a ·ᵣ g a +ᵣ h a ·ᵣ h a ≡ 0
  [g²+f²]=0-0<a a 0<a =
    let z = nullDerivative→const 0 a
          (≤ᵣ-refl 0 , <ᵣWeaken≤ᵣ _ _ 0<a)
          (<ᵣWeaken≤ᵣ _ _ 0<a , ≤ᵣ-refl a) 0<a _
           (D[g²+f²] 0 a 0<a)
    in sym z ∙ [g²+f²]0

  cG : IsContinuous g
  cG = IsUContinuousℙ→IsContinuous g λ _ _ → gC _ _

  cH : IsContinuous h
  cH = IsUContinuousℙ→IsContinuous h λ _ _ → hC _ _


  [g²+f²]=0 : ∀ a → g a ·ᵣ g a +ᵣ h a ·ᵣ h a ≡ 0
  [g²+f²]=0 = ≡Continuous _ _
    (cont₂+ᵣ _ _
      (cont₂·ᵣ _ _ cG cG)
      (cont₂·ᵣ _ _ cH cH))
    (IsContinuousConst _)
    (ℚ.byTrichotomy 0 td)
    where
    td : ℚ.TrichotomyRec 0
          (λ z → g (rat z) ·ᵣ g (rat z) +ᵣ h (rat z) ·ᵣ h (rat z) ≡ 0)
    td .ℚ.TrichotomyRec.lt-case a = [g²+f²]=0-a<0 (rat a) ∘ <ℚ→<ᵣ _ _
    td .ℚ.TrichotomyRec.eq-case = [g²+f²]0
    td .ℚ.TrichotomyRec.gt-case a = [g²+f²]=0-0<a (rat a) ∘ <ℚ→<ᵣ _ _

  g=0 : ∀ a → g a ≡ 0
  g=0 a =
   let z = isAntisym≤ᵣ (g a ·ᵣ g a) 0
            (subst2 _≤ᵣ_
              (+IdR _)
              ([g²+f²]=0 a)
              (≤ᵣ-o+ _ _ (g a ·ᵣ g a) (isTrans≤≡ᵣ _ _ _
             (0≤ᵣx² (h a))
             (cong₂ _·ᵣ_  (·IdL _) refl))))
            (isTrans≤≡ᵣ _ _ _ (0≤ᵣx² (g a)) (cong₂ _·ᵣ_  (·IdL _) refl))
   in x²≡0→x≡0 (g a) z

  h=0 : ∀ a → h a ≡ 0
  h=0 a = x²≡0→x≡0 (h a)
    (sym (𝐑'.+IdL' _ _ (cong₂ _·ᵣ_ (g=0 a) (g=0 a) ∙ sym (rat·ᵣrat 0 0)))
     ∙ [g²+f²]=0 a)

 sinOfSum : ∀ a b → sin (a  +ᵣ b) ≡ sin a ·ᵣ cos b +ᵣ cos a ·ᵣ sin b
 sinOfSum a b = 𝐑'.equalByDifference _ _ (g=0 b a)

 cosOfSum : ∀ a b → cos (a +ᵣ b) ≡ cos a ·ᵣ cos b -ᵣ sin a ·ᵣ sin b
 cosOfSum a b = 𝐑'.equalByDifference _ _ (h=0 b a)

open sin-cos-of-sum public using (sinOfSum; cosOfSum)
