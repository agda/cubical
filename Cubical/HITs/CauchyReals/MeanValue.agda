{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.MeanValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset
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
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

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
open import Cubical.HITs.CauchyReals.Summation
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer

open import Cubical.Tactics.CommRingSolver






≡-byContracdition : ∀ x y → ((ε : ℚ₊) → rat (fst ε) <ᵣ absᵣ (x -ᵣ y) → ⊥ )
                      → x ≡ y
≡-byContracdition x y X =
  eqℝ _ _ λ ε →
    PT.rec (isProp∼ _ _ _)
        (⊎.rec (invEq (∼≃abs<ε _ _ ε))
         (⊥.rec ∘ X (/2₊ ε)) )
      (Dichotomyℝ' (fst (ℚ₊→ℝ₊ (/2₊ ε))) (absᵣ (x -ᵣ y)) (fst (ℚ₊→ℝ₊ ε))
       (<ℚ→<ᵣ _ _ (x/2<x ε)))


stichFns : (a b : ℝ) → a <ᵣ b
           → (f : ∀ x → x <ᵣ b → ℝ)
           → (g : ∀ x → a <ᵣ x → ℝ)
           → (∀ x x< <x → f x x< ≡ g x <x)
           → ℝ → ℝ
stichFns a b a<b f g f=g x =
  PT.rec→Set isSetℝ
    (⊎.rec (f x) (g x))
    w
   (Dichotomyℝ' a x b a<b)
 where
 w : 2-Constant (⊎.rec (f x) (g x))
 w (inl u) (inl v) = cong (f x) (isProp<ᵣ _ _ u v)
 w (inl u) (inr v) = f=g x u v
 w (inr u) (inl v) = sym (f=g x v u)
 w (inr u) (inr v) = cong (g x) (isProp<ᵣ _ _ u v)
 

Bishop-Proposition7 : ∀ n (f : Fin n → ℝ)
 → 0 <ᵣ foldlFin {n = n} (λ a k → a +ᵣ f k) 0 (idfun _)
 → ∃[ k ∈ Fin n ] 0 <ᵣ f k
Bishop-Proposition7 zero f x = ⊥.rec (isIrrefl<ᵣ 0 x)
Bishop-Proposition7 (suc n) f x =
  PT.rec squash₁
  (λ (ε , 0<ε , ε<∑) →
    let ε₊ = (ε , ℚ.<→0< ε (<ᵣ→<ℚ 0 ε 0<ε))
    in PT.rec squash₁
          (⊎.rec
            (λ f0<ε/2 →
              let zz = isTrans<≡ᵣ _ _ _ (isTrans<ᵣ _ _ _
                       (snd (ℚ₊→ℝ₊ (/2₊ ε₊))) (isTrans≡<ᵣ _ _ _
                        (sym L𝐑.lem--04 ∙
                          cong₂ _+ᵣ_ refl (+ᵣ-rat _ _
                           ∙ cong rat (ℚ.ε/2+ε/2≡ε ε)))
                        (<ᵣMonotone+ᵣ _ _ _ _
                         (-ᵣ<ᵣ _ _ f0<ε/2)
                         (isTrans<≡ᵣ _ _ _ ε<∑
                           (foldFin+0ᵣ n (fsuc) (f) _
                            ∙ cong₂ _+ᵣ_ (+IdL _) refl)))))
                          (L𝐑.lem--04 ∙ foldFin+map n 0 f fsuc (idfun _))
                  z = Bishop-Proposition7 n (f ∘ fsuc) zz
              in PT.map ((_ ,_) ∘ snd) z)
            (∣_∣₁ ∘ (_ ,_)))
         ((Dichotomyℝ' 0 (f fzero) (rat (fst (/2₊ ε₊))) (snd (ℚ₊→ℝ₊ (/2₊ ε₊))) )))
  (denseℚinℝ 0 _ x)




-- uDerivativeOfℙ→at : ∀ P f f' x x∈
--    → uDerivativeOfℙ P , f is f'
--    → derivativeOfℙ P , f at (x , x∈) is (f' x x∈)
-- uDerivativeOfℙ→at P f f' x x∈ X ε =
--   PT.map (λ  λ X' h h∈ 0＃h ∣h∣<ε
--     → X' x x∈ h h∈ 0＃h
--       (isTrans≡<ᵣ _ _ _
--         (-absᵣ h ∙ cong absᵣ (sym (+IdL _)))
--         ∣h∣<ε)) {!X ?!}


Fin-∀A⊎∃B : ∀ n → (A B : Fin n → Type₀)
           → (∀ k → ∥ A k ⊎ B k ∥₁)
           → ∥ (∀ k → A k) ⊎ Σ _ B ∥₁

Fin-∀A⊎∃B zero A B ab? = ∣ inl (⊥.rec ∘ ¬Fin0) ∣₁
Fin-∀A⊎∃B (suc n) A B ab? =
  PT.map2
     (⊎.rec (λ a0 →
       ⊎.map (λ ∀kA →
              λ { (zero , _) → subst A (toℕ-injective refl) a0
                ; (suc k , l , p) →
                  subst A (toℕ-injective refl) (∀kA (k , l ,
                    injSuc (sym (+-suc _ _) ∙ p)))
                })
        λ (k , bk) → _ , bk) (λ b0 _ → inr (_ , b0)))
    (ab? fzero)
    (Fin-∀A⊎∃B n (A ∘ fsuc) (B ∘ fsuc) (ab? ∘ fsuc))

ε<abs→ε<⊎<-ε : ∀ (ε : ℝ₊) x → fst ε <ᵣ absᵣ x →
                        (x <ᵣ -ᵣ (fst ε)) ⊎ (fst ε <ᵣ x)
ε<abs→ε<⊎<-ε ε x ε<∣x∣ =

   ⊎.map (λ x<0 → isTrans≡<ᵣ _ _ _
        (sym (-ᵣInvol _) ∙
         cong -ᵣ_ (sym (absᵣNeg _ x<0))) (-ᵣ<ᵣ _ _ ε<∣x∣))
      (λ 0<x → isTrans<≡ᵣ _ _ _ ε<∣x∣ (absᵣPos _ 0<x))
   (invEq (＃≃0<dist x 0)
      (isTrans<≡ᵣ _ _ _
        (isTrans<ᵣ _ _ _ (snd ε) ε<∣x∣)
        (cong absᵣ (sym (𝐑'.+IdR' _ _ (-ᵣ-rat 0))))))
 where
 -ε<ε = isTrans<ᵣ _ _ _
    (isTrans<≡ᵣ _ _ _
      (-ᵣ<ᵣ _ _ (snd ε))
      (-ᵣ-rat 0))
    (snd ε)

equalPartitionStrict∃ : ∀ a b → a <ᵣ b → (ε : ℚ₊) →
 ∃[ pa ∈ Partition[ a , b ] ] (isStrictPartition pa × mesh≤ᵣ pa (rat (fst ε)))
equalPartitionStrict∃ a b a<b ε =
  PT.map2 w
    (denseℚinℝ a (a +ᵣ fst η)
      (isTrans≡<ᵣ _ _ _
        (sym (+IdR a)) (<ᵣ-o+ _ _ _ (snd η))))
    (denseℚinℝ (b -ᵣ fst η) b
     ((isTrans<≡ᵣ _ _ _
         (<ᵣ-o+ _ _ _
           (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (snd η)) (-ᵣ-rat 0)))
         (+IdR b))))

  where
  Δ₊ : ℝ₊
  Δ₊ = _ , x<y→0<y-x _ _ a<b
  η : ℝ₊
  η = minᵣ₊ (Δ₊ ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _))) (ℚ₊→ℝ₊ ε)

  w : _
  w (a' , a<a' , a'<a+η) (b' , b-η<b' , b'<b) =
    w' , ww' , www'
   where
   h = min≤ᵣ (fst (Δ₊ ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)))) (fst (ℚ₊→ℝ₊ ε))
   a'<b' = <ᵣ→<ℚ _ _
     (isTrans<ᵣ _ _ _
       a'<a+η
       (isTrans≤<ᵣ _ _ _
         (a+b≤c⇒b≤c-b _ _ _
           (isTrans≡≤ᵣ _ _ _
             (+ᵣComm _ _
              ∙ sym (+ᵣAssoc _ _ _))
              (b≤c-b⇒a+b≤c _ _ _
               (isTrans≤≡ᵣ _ _ _
                   (≤ᵣMonotone+ᵣ _ _ _ _ h h)
                   (sym
                    (·DistL+ (fst Δ₊) (rat [ 1 / 2 ]) (rat [ 1 / 2 ]))
                    ∙ 𝐑'.·IdR' _ _ (+ᵣ-rat _ _ ∙
                     decℚ≡ᵣ?))))))
         b-η<b'))
   rtp = RefinableTaggedPartition[_,_].tpTP
     (rtp-1/n a' b' (ℚ.<Weaken≤ a' b' a'<b')) ε

   module eqp = Partition[_,_] (fst (fst rtp))
   w' : Partition[ a , b ]
   w' .len = suc (suc eqp.len)
   w' .pts = eqp.pts'
   w' .a≤pts k = isTrans≤ᵣ _ _ _
       (<ᵣWeaken≤ᵣ _ _ a<a') (eqp.a≤pts' k)
   w' .pts≤b k = isTrans≤ᵣ _ _ _ (eqp.pts'≤b k)
         (<ᵣWeaken≤ᵣ _ _ b'<b)
   w' .pts≤pts = eqp.pts'≤pts'

   hlpr : ∀ k k< k<' → pts' w' (suc k , k<) ≡ eqp.pts' (k , k<')
   hlpr k (zero , p) (l , p') =
     ⊥.rec (znots (inj-m+
         (+-zero k ∙ injSuc (injSuc p) ∙ sym p' ∙ +-comm l (suc k)
       ∙ sym (+-suc k l))))
   hlpr k k<@(suc l , snd₁) k<' =
    cong {x = k , _} {(k , k<')}
      eqp.pts' (toℕ-injective refl)

   ww' : isStrictPartition w'
   ww' (zero , zero , p) = ⊥.rec (znots (injSuc p))
   ww' (zero , suc l , p) = a<a'
   ww' (suc zero , zero , p) = ⊥.rec (znots (injSuc (injSuc p)))
   ww' (suc (suc k) , zero , p) = b'<b
   ww' (suc k , suc l , p) =
     subst2 _<ᵣ_
       (sym (hlpr k (snd (finj (suc k , suc l , p))) _))
       (sym (hlpr (suc k) (snd (fsuc (suc k , suc l , p)))
           (snd (fsuc (k , l , _)))))
       (Integration.isStrictEqualPartition (rat a') (rat b')
        _ (<ℚ→<ᵣ _ _ a'<b')
        _
         (k , l , injSuc (sym (+-suc _ _) ∙ injSuc p)))

   www' : mesh≤ᵣ w' (rat (fst ε))
   www' (zero , zero , p) = ⊥.rec (znots (injSuc p))
   www' (zero , suc l , p) =
     isTrans≤ᵣ _ _ _
       (<ᵣWeaken≤ᵣ _ _ (a<c+b⇒a-c<b _ _ _ a'<a+η))
       (min≤ᵣ' (fst (Δ₊ ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)))) (fst (ℚ₊→ℝ₊ ε)))
   www' (suc zero , zero , p) = ⊥.rec (znots (injSuc (injSuc p)))
   www' (suc (suc k) , zero , p) =
     isTrans≤ᵣ _ _ _
       (<ᵣWeaken≤ᵣ _ _ (a-b<c⇒a-c<b _ _ _ b-η<b'))
       (min≤ᵣ' (fst (Δ₊ ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)))) (fst (ℚ₊→ℝ₊ ε)))
   www' (suc k , suc l , p) =
     isTrans≡≤ᵣ _ _ _
       (cong₂ _-ᵣ_
         (hlpr (suc k) (snd (fsuc (suc k , suc l , p)))
           (snd (fsuc (k , l , _))))
         (hlpr k (snd (finj (suc k , suc l , p))) _))
       (snd rtp (k , l , injSuc (sym (+-suc _ _) ∙ injSuc p)))


allOnOneSideLemma : ∀ n (ε : ℝ₊) (f : Fin (suc n) → ℝ)
            → (∀ k → absᵣ (f (fsuc k) -ᵣ f (finj k)) <ᵣ fst ε )
            → (∀ k → (f k <ᵣ -ᵣ (fst ε  ·ᵣ rat [ 1 / 2 ]))
                ⊎ (fst ε ·ᵣ rat [ 1 / 2 ] <ᵣ f k))

            → (∀ k → f k <ᵣ -ᵣ (fst ε  ·ᵣ rat [ 1 / 2 ])) ⊎
              (∀ k → fst ε  ·ᵣ rat [ 1 / 2 ] <ᵣ f k)
allOnOneSideLemma zero ε f fΔ f⊎ =
  ⊎.map
    (λ f0 k → isTrans≡<ᵣ _ _ _ (cong f (sym (snd (isContrFin1) k) )) f0)
    (λ f0 k → isTrans<≡ᵣ _ _ _ f0 (cong f (snd (isContrFin1) k)))
    (f⊎ fzero)
allOnOneSideLemma (suc n) ε f fΔ f⊎ =
  ⊎.map
    (λ fs → ⊎.rec
           (λ f0< →
             λ { (zero , p) →
                   isTrans≡<ᵣ _ _ _ (cong f (toℕ-injective refl)) f0<
               ; (suc k , p) →
                  isTrans≡<ᵣ _ _ _ (cong f (toℕ-injective refl))
                   (fs (k , ℕ.pred-≤-pred p))})
           (λ <f0 _ →
              ⊥.rec
                 (isAsym<ᵣ (fst ε)
                           (absᵣ (f (fsuc fzero) -ᵣ f (finj fzero)))
                   (isTrans<≤ᵣ _ _ _
                     (isTrans≡<ᵣ _ _ _
                     ((sym (𝐑'.·IdR' _ _ (+ᵣ-rat _ _ ∙
                       decℚ≡ᵣ?))
                      ∙ ·DistL+ _ _ _ )
                      ∙ cong₂ _+ᵣ_
                        (sym (-ᵣInvol _))
                        refl)
                      (<ᵣMonotone+ᵣ _ _ _ _ (-ᵣ<ᵣ _ _ (fs fzero)) (<f0)))
                      (isTrans≤≡ᵣ _ _ _
                        (≤absᵣ _)
                        (cong absᵣ (+ᵣComm _ _)
                          ∙ minusComm-absᵣ _ _)))
                     (fΔ fzero)
                     ))
       (f⊎ (finj fzero)))
    (λ fs → ⊎.rec
           (λ f0< → ⊥.rec
                 ((isAsym<ᵣ (fst ε)
                           (absᵣ (f (fsuc fzero) -ᵣ f (finj fzero)))
                  ((isTrans<≤ᵣ _ _ _
                     (isTrans≡<ᵣ _ _ _
                     ((sym (𝐑'.·IdR' _ _ (+ᵣ-rat _ _ ∙
                       decℚ≡ᵣ?))
                      ∙ ·DistL+ _ _ _ )
                      ∙ cong₂ _+ᵣ_ refl
                              (sym (-ᵣInvol _))
                        )
                          (isTrans<≡ᵣ _ _ _
                           (<ᵣMonotone+ᵣ _ _ _ _
                           (fs fzero) (-ᵣ<ᵣ _ _  (f0<)))
                           (+ᵣComm _ _ ∙
                             cong₂ _+ᵣ_
                              (cong (-ᵣ_ ∘ f) (toℕ-injective refl))
                               refl)))
                      (isTrans≤≡ᵣ _ _ _
                        (≤absᵣ _)
                        (cong absᵣ (+ᵣComm _ _))))))
                           (fΔ fzero)))
           (λ <f0 →
               λ { (zero , p) →
                     isTrans<≡ᵣ _ _ _ <f0 (cong f (toℕ-injective refl))
                 ; (suc k , p) →
                   isTrans<≡ᵣ _ _ _ (fs (k , ℕ.pred-≤-pred p))
                      (cong f (toℕ-injective refl))})
       (f⊎ fzero))
    (allOnOneSideLemma n ε (f ∘ fsuc)
      ((λ {a} → isTrans≡<ᵣ _ _ _
       (cong (λ ffa → absᵣ (f (fsuc (fsuc a)) -ᵣ f ffa))
         (toℕ-injective refl) ))
       ∘ (fΔ ∘ fsuc))
       (f⊎ ∘ fsuc))


Rolle'sTheorem : ∀ a b → a <ᵣ b → ∀ a∈ b∈ f f'
  → IsUContinuousℙ (intervalℙ a b) f'
  → uDerivativeOfℙ (intervalℙ a b) , f is f'
  → f a a∈ ≡ f b b∈
  → ∀ (ε : ℚ₊) → ∃[ (x₀ , x∈) ∈ Σ _ (_∈ intervalℙ a b) ]
            absᵣ (f' x₀ x∈) <ᵣ rat (fst ε)
Rolle'sTheorem a b a<b a∈ b∈ f f' ucf udf fa≡fb ε =
  PT.rec squash₁ (w (ucf ε)) (udf (/2₊ ε))

 where
 w : _ → _ → _
 w (δ , X) (δ' , X') = PT.rec squash₁ ww
   (equalPartitionStrict∃ a b a<b δ⊓δ')
  where
  δ⊓δ' = ℚ.min₊ (/2₊ δ) (/2₊ δ')


  ww : _
  ww (pa , str-pa , mesh-pa) =
    PT.rec squash₁
      (⊎.rec (∀case ∘ (ε<abs→ε<⊎<-ε (ℚ₊→ℝ₊ (/2₊ ε)) _ ∘_))
             (∣_∣₁ ∘ (_ ,_) ∘ snd))
     (Fin-∀A⊎∃B (suc (suc Pa.len)) 
       _ _
        λ k → PT.map (Iso.fun ⊎-swap-Iso) (Dichotomyℝ'
                        (rat (fst (/2₊ ε)))
                   (absᵣ (f' (Pa.pts' (finj k))
                     (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))))
                   ((rat (fst ε)))
                   (<ℚ→<ᵣ _ _ (ℚ.x/2<x ε))))
   where
   module Pa = Partition[_,_] pa



   z : ∀ f f' → f a a∈ ≡ f b b∈ →
          ((x : ℝ) (x∈ : x ∈ intervalℙ a b) (h : ℝ)
           (h∈ : x +ᵣ h ∈ intervalℙ a b) (0＃h : rat [ pos 0 / 1+ 0 ] ＃ h) →
           absᵣ h <ᵣ rat (fst δ') →
           absᵣ (f' x x∈ -ᵣ differenceAtℙ (intervalℙ a b) f x h 0＃h x∈ h∈) <ᵣ
           rat (fst (/2₊ ε)))
        → ∃-syntax (Fin (suc (suc Pa.len)))
        (λ k → (-ᵣ rat (fst ε))
          <ᵣ f' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k)))
   z f f' fa≡fb X' = PT.map
          (map-snd
           λ {l} X → 0<y-x→x<y _ _
             (isTrans<≡ᵣ _ _ _
              (isTrans≡<ᵣ _ _ _ (sym (𝐑'.0LeftAnnihilates _))
              (invEq (z/y<x₊≃z<y₊·x _ _ (_ , x<y→0<y-x _ _ (str-pa l)))
                (isTrans<≡ᵣ _ _ _ X
                (·ᵣComm _ _))))
                (cong₂ _+ᵣ_ refl
                 (sym (-ᵣInvol _)))))
        (Bishop-Proposition7 (suc (suc Pa.len))
        (λ k → (f' (Pa.pts' (finj k))
                     (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
                    +ᵣ rat (fst ε))
             ·ᵣ (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k)))
        (isTrans≡<ᵣ _ _ _
           (sym (𝐑'.+InvR' _ _ (sym fa≡fb))
             ∙ cong₂ _-ᵣ_
                (cong (f b) (∈-isProp (intervalℙ a b) _ _ _))
                (cong (f a) (∈-isProp (intervalℙ a b) _ _ _))
             ∙ sym (deltas-sum (suc (suc Pa.len))
               λ k → f (Pa.pts' k) (Pa.a≤pts' k , Pa.pts'≤b k)))
           (foldFin+< (suc Pa.len) 0 0
             _ _ (idfun _) (idfun _) (≤ᵣ-refl 0)
             <f)))

    where
    <f : (k : Fin (suc (suc Pa.len))) →
          f (Pa.pts' (fsuc k)) _ -ᵣ f (Pa.pts' (finj k)) _
          <ᵣ
          (f' (Pa.pts' (finj k)) _ +ᵣ rat (fst ε))
          ·ᵣ
          (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))
    <f k = isTrans<ᵣ _ _ _ (isTrans<≡ᵣ _ _ _
      (fst (z/y<x₊≃z<y₊·x _ _ _) fromX') (·ᵣComm _ _))
           (<ᵣ-·ᵣo _ _
             (_ , x<y→0<y-x _ _ (str-pa k))
             (<ᵣ-o+ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.x/2<x ε))))
     where
     fromX' : _ <ᵣ f' (Pa.pts' (finj k)) _ +ᵣ rat (fst (/2₊ ε))
     fromX' = (isTrans≡<ᵣ _ _ _
       (cong₂ _·ᵣ_
         (cong₂ _-ᵣ_
           (cong (uncurry f)
             (Σ≡Prop (∈-isProp (intervalℙ a b)) (sym L𝐑.lem--05)) )
           refl)
        (invℝ₊≡invℝ (_ , x<y→0<y-x _ _ (str-pa k)) _))
       (isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _
        (isTrans≤<ᵣ _ _ _
         (≤absᵣ _)
         (isTrans≡<ᵣ _ _ _
          (minusComm-absᵣ _ _)
            (X' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
        (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))
        (subst-∈ (intervalℙ a b)
          (sym L𝐑.lem--05)
           (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k)))
        (invEq (＃Δ _ _) (inl (str-pa k)))
        (isTrans≡<ᵣ _ _ _
          (absᵣNonNeg _ (x≤y→0≤y-x _ _ (Pa.pts'≤pts' k)))
          (isTrans≤<ᵣ _ _ _
            (isTrans≤ᵣ _ _ _
              (mesh-pa k)
              (≤ℚ→≤ᵣ (fst δ⊓δ')  (fst (/2₊ δ'))
                (ℚ.min≤' (fst (/2₊ δ)) (fst (/2₊ δ')))))
            (<ℚ→<ᵣ _ _ (ℚ.x/2<x δ'))))))))
            (+ᵣComm _ _)))


   z' : ∃-syntax (Fin (suc (suc Pa.len)))
        (λ k → f' (Pa.pts' (finj k)) _ <ᵣ rat (fst ε))
   z' = PT.map (map-snd (<ᵣ-ᵣ _ _))
          (z (λ x x∈ → -ᵣ (f x x∈))
               (λ x x∈ → -ᵣ (f' x x∈))
                (cong -ᵣ_ fa≡fb)
                 λ x x∈ h h∈ 0＃h h<δ' →
                  isTrans≡<ᵣ _ _ _
                     (cong absᵣ (sym (-ᵣDistr _ _)) ∙
                      sym (-absᵣ _)
                        ∙ cong (absᵣ ∘ (f' x x∈ +ᵣ_))
                          (cong (_·ᵣ invℝ h 0＃h)
                            (sym (-ᵣDistr _ _))
                            ∙ -ᵣ· _ _) )
                     (X' x x∈ h h∈ 0＃h h<δ'))


   ∀case : ((a₁ : Fin (suc (suc Pa.len))) →
            (f' (Pa.pts' (finj a₁)) _ <ᵣ -ᵣ fst (ℚ₊→ℝ₊ (/2₊ ε)))
            ⊎
            (fst (ℚ₊→ℝ₊ (/2₊ ε)) <ᵣ f' (Pa.pts' (finj a₁)) _)) →
            ∃ (Σ ℝ (_∈ intervalℙ a b))
            (λ v → absᵣ (f' (v .fst) (v .snd)) <ᵣ rat (fst ε))
   ∀case =
        ⊎.rec
          (λ ∀f< → PT.map
              (λ (k , U) →
                _ ,
                 isTrans≡<ᵣ _ _ _
                   (abs-max _)
                    (max<-lem _ _ _
                      (isTrans<ᵣ _ _ _ (∀f< k)
                        (isTrans<ᵣ _ 0 _
                          (isTrans<≡ᵣ _ _ _
                            (-ᵣ<ᵣ _ _
                              (snd ((ℚ₊→ℝ₊ ε) ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ] , _))))
                           (-ᵣ-rat 0)) (snd (ℚ₊→ℝ₊ ε))))
                      (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ U) (-ᵣInvol _))))
              (z f f' fa≡fb X'))
          (λ ∀<f → PT.map
             (λ (k , U) →
                _ ,
                 isTrans≡<ᵣ _ _ _
                   (abs-max _)
                    (max<-lem _ _ _ U
                      (isTrans<ᵣ _ _ _
                        (-ᵣ<ᵣ _ _ (∀<f k))
                        ((isTrans<ᵣ _ 0 _
                          (isTrans<≡ᵣ _ _ _
                            (-ᵣ<ᵣ _ _
                              (snd ((ℚ₊→ℝ₊ ε) ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ] , _))))
                           (-ᵣ-rat 0)) (snd (ℚ₊→ℝ₊ ε)))))))
             z')
     ∘  allOnOneSideLemma (suc Pa.len) (ℚ₊→ℝ₊ ε) _
             (fst (∼≃abs<ε _ _ ε) ∘
               λ k → (X _ _ _ _
                (invEq (∼≃abs<ε _ _ δ)
                  (isTrans≤<ᵣ _ _ _
                    (isTrans≡≤ᵣ _ _ _
                      (cong {x = finj (fsuc k)} {(fsuc (finj k))}
                       (λ aa → absᵣ (Pa.pts' aa
                         +ᵣ -ᵣ Pa.pts' (finj (finj k))))
                         (toℕ-injective refl)
                        ∙ absᵣPos _ (x<y→0<y-x _ _
                        (str-pa (finj k))))
                      (mesh-pa (finj k)))
                    (<ℚ→<ᵣ _ _
                     (ℚ.isTrans≤< (fst δ⊓δ') _ _
                       (ℚ.min≤ (fst (/2₊ δ)) (fst (/2₊ δ')))
                       (ℚ.x/2<x δ))
                     )))))
     ∘ (⊎.map (flip (isTrans<≡ᵣ _ _ _) (cong -ᵣ_ (rat·ᵣrat (fst ε) _)))
              (isTrans≡<ᵣ _ _ _ (sym (rat·ᵣrat (fst ε) _)))
         ∘_)

meanValue : ∀ a b → a <ᵣ b → ∀ a∈ b∈ f f'
       →  IsUContinuousℙ (intervalℙ a b) f'
       →  uDerivativeOfℙ (intervalℙ a b) , f is f'
       → (ε : ℚ₊) →
          ∃[ (x₀ , x∈) ∈ Σ _ (_∈ intervalℙ a b) ]
           absᵣ ((f b b∈ -ᵣ f a a∈)  -ᵣ f' x₀ x∈ ·ᵣ (b -ᵣ a)) <ᵣ rat (fst ε)
meanValue a b a<b a∈ b∈ f f' ucf udf =
  PT.rec (isPropΠ λ _ → squash₁) (λ uch' → Rolle'sTheorem a b a<b a∈ b∈
     h h' uch' udh ha≡hb)
      uch


 where
  h h' : (x : ℝ) → x ∈ intervalℙ a b → ℝ
  h x x∈ = ((x -ᵣ a) ·ᵣ (f b b∈ -ᵣ f a a∈))
                -ᵣ f x x∈ ·ᵣ (b -ᵣ a)

  h' x x∈ = (f b b∈ -ᵣ f a a∈) -ᵣ f' x x∈ ·ᵣ (b -ᵣ a)

  uch : ∥ IsUContinuousℙ (intervalℙ a b) h' ∥₁
  uch = PT.map (λ z → IsUContinuous∘ℙ (intervalℙ a b)
       (IsUContinuous∘ (IsUContinuous+ᵣL (f b b∈ -ᵣ f a a∈))
          (subst IsUContinuous (funExt λ x → ·-ᵣ _ _)
            z))
       ucf) (IsUContinuous·ᵣR (-ᵣ (b -ᵣ a)))

  udh0 : _
  udh0 = +uDerivativeℙ (intervalℙ a b)
    (λ x _ → ((x -ᵣ a) ·ᵣ (f b b∈ -ᵣ f a a∈)))
     (λ _ _ → (f b b∈ -ᵣ f a a∈))
    _ _
    (subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
      (funExt₂ λ x x∈ → ·ᵣComm _ _)
      (funExt₂ λ x x∈ → 𝐑'.·IdR' _ _ (+IdR 1))
      (C·uDerivativeℙ (intervalℙ a b)
       _ _ _ (+uDerivativeℙ (intervalℙ a b)
        _ _ _ _
        (uDerivativeℙ-id (intervalℙ a b))
        (uDerivativeℙ-const (intervalℙ a b) (-ᵣ a))) ))
    (C·uDerivativeℙ (intervalℙ a b) (-ᵣ (b -ᵣ a))
     _ _
     udf)

  udh : uDerivativeOfℙ intervalℙ a b , h is h'
  udh = subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
           (funExt₂ λ x x∈ →
            cong₂ _+ᵣ_ refl (-ᵣ· _ _ ∙ cong -ᵣ_ (·ᵣComm _ _)))
           (funExt₂ λ x x∈ →
            cong₂ _+ᵣ_ refl (-ᵣ· _ _ ∙ cong -ᵣ_ (·ᵣComm _ _)))
           udh0


  ha≡hb : h a a∈ ≡ h b b∈
  ha≡hb = 𝐑'.+IdL' _ _ (𝐑'.0LeftAnnihilates' _ _ (+-ᵣ a))
    ∙ sym (-ᵣ· _ _)
    ∙ cong (_·ᵣ (b -ᵣ a)) (sym L𝐑.lem--063)
    ∙ 𝐑'.·DistL- (f b b∈ -ᵣ f a a∈) (f b b∈) (b -ᵣ a)
    ∙ cong₂ _-ᵣ_ (·ᵣComm _ _) refl

nullDerivative→const : ∀ a b a∈ b∈ → a <ᵣ b → ∀ f
       → uDerivativeOfℙ (intervalℙ a b) , f is (λ _ _ → 0)
       → f a a∈ ≡ f b b∈
nullDerivative→const a b a∈ b∈ a<b f udf  =
  eqℝ _ _ λ ε →
    PT.rec (isProp∼ _ _ _)
      (λ (_ , X) →
        sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
          (isTrans≡<ᵣ _ _ _
            (cong absᵣ
              (sym (𝐑'.+IdR' _ _
                (cong -ᵣ_ (𝐑'.0LeftAnnihilates (b -ᵣ a))
                 ∙ -ᵣ-rat 0))))
            X)))
      (meanValue a b a<b a∈ b∈ f
        (λ _ _ → 0) (λ ε₁ → 1 , λ _ _ _ _ _ → refl∼ _ _) udf ε)




-- Dichotomyℝ' : ∀ x y z → x <ᵣ z →
--               ∥ (y <ᵣ z) ⊎ (x <ᵣ y) ∥₁
-- Dichotomyℝ' x y z x<z =
--   PT.map2
--    (λ (q  , x<q  , q<x+Δ)
--       (q' , y-Δ<q' , q'<y)
--      → ⊎.map
--          (λ q'≤q →
--            isTrans<ᵣ _ _ _
--              (a-b<c⇒a<c+b _ _ _ y-Δ<q')
--              (isTrans<≡ᵣ _ _ _
--                (<ᵣ-+o _ _ _
--                  ((isTrans≤<ᵣ _ _ _ (≤ℚ→≤ᵣ q' _ q'≤q)
--                   q<x+Δ )))
--                ((sym (+ᵣAssoc _ _ _)  ∙
--                 cong (x +ᵣ_) (sym (·DistL+ _ _ _) ∙
--                  𝐑'.·IdR' _ _ (+ᵣ-rat _ _ ∙ decℚ≡ᵣ?) ))
--                 ∙ L𝐑.lem--05 {x} {z})))
--          (λ q<q' →
--            isTrans<ᵣ _ _ _ (isTrans<ᵣ _ _ _
--                x<q
--                (<ℚ→<ᵣ q _ q<q'))
--              q'<y)
--          (ℚ.Dichotomyℚ q' q))
--     (denseℚinℝ x (x +ᵣ (fst Δ₊))
--       (isTrans≡<ᵣ _ _ _
--         (sym (+IdR x)) (<ᵣ-o+ _ _ _ (snd Δ₊))))
--     (denseℚinℝ (y -ᵣ (fst Δ₊)) y
--       (isTrans<≡ᵣ _ _ _
--          (<ᵣ-o+ _ _ _
--            (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (snd Δ₊)) (-ᵣ-rat 0)))
--          (+IdR y)))

--  where
--  Δ₊ : ℝ₊
--  Δ₊ = (z -ᵣ x , x<y→0<y-x _ _ x<z) ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ] , _)

-- Bishop-Proposition7 : ∀ n (f : Fin n → ℝ)
--  → 0 <ᵣ foldlFin {n = n} (λ a k → a +ᵣ f k) 0 (idfun _)
--  → ∃[ k ∈ Fin n ] 0 <ᵣ f k
-- Bishop-Proposition7 zero f x = ⊥.rec (isIrrefl<ᵣ 0 x)
-- Bishop-Proposition7 (suc n) f x =
--   PT.rec squash₁
--   (λ (ε , 0<ε , ε<∑) →
--     let ε₊ = (ε , ℚ.<→0< ε (<ᵣ→<ℚ 0 ε 0<ε))
--     in PT.rec squash₁
--           (⊎.rec
--             (λ f0<ε/2 →
--               let zz = isTrans<≡ᵣ _ _ _ (isTrans<ᵣ _ _ _
--                        (snd (ℚ₊→ℝ₊ (/2₊ ε₊))) (isTrans≡<ᵣ _ _ _
--                         (sym L𝐑.lem--04 ∙
--                           cong₂ _+ᵣ_ refl (+ᵣ-rat _ _
--                            ∙ cong rat (ℚ.ε/2+ε/2≡ε ε)))
--                         (<ᵣMonotone+ᵣ _ _ _ _
--                          (-ᵣ<ᵣ _ _ f0<ε/2)
--                          (isTrans<≡ᵣ _ _ _ ε<∑
--                            (foldFin+0ᵣ n (fsuc) (f) _
--                             ∙ cong₂ _+ᵣ_ (+IdL _) refl)))))
--                           (L𝐑.lem--04 ∙ foldFin+map n 0 f fsuc (idfun _))
--                   z = Bishop-Proposition7 n (f ∘ fsuc) zz
--               in PT.map ((_ ,_) ∘ snd) z)
--             (∣_∣₁ ∘ (_ ,_)))
--          ((Dichotomyℝ' 0 (f fzero) (rat (fst (/2₊ ε₊))) (snd (ℚ₊→ℝ₊ (/2₊ ε₊))) )))
--   (denseℚinℝ 0 _ x)




-- -- uDerivativeOfℙ→at : ∀ P f f' x x∈
-- --    → uDerivativeOfℙ P , f is f'
-- --    → derivativeOfℙ P , f at (x , x∈) is (f' x x∈)
-- -- uDerivativeOfℙ→at P f f' x x∈ X ε =
-- --   PT.map (λ  λ X' h h∈ 0＃h ∣h∣<ε
-- --     → X' x x∈ h h∈ 0＃h
-- --       (isTrans≡<ᵣ _ _ _
-- --         (-absᵣ h ∙ cong absᵣ (sym (+IdL _)))
-- --         ∣h∣<ε)) {!X ?!}


-- Fin-∀A⊎∃B : ∀ n → (A B : Fin n → Type₀)
--            → (∀ k → ∥ A k ⊎ B k ∥₁)
--            → ∥ (∀ k → A k) ⊎ Σ _ B ∥₁

-- Fin-∀A⊎∃B zero A B ab? = ∣ inl (⊥.rec ∘ ¬Fin0) ∣₁
-- Fin-∀A⊎∃B (suc n) A B ab? =
--   PT.map2
--      (⊎.rec (λ a0 →
--        ⊎.map (λ ∀kA →
--               λ { (zero , _) → subst A (toℕ-injective refl) a0
--                 ; (suc k , l , p) →
--                   subst A (toℕ-injective refl) (∀kA (k , l ,
--                     injSuc (sym (+-suc _ _) ∙ p)))
--                 })
--         λ (k , bk) → _ , bk) (λ b0 _ → inr (_ , b0)))
--     (ab? fzero)
--     (Fin-∀A⊎∃B n (A ∘ fsuc) (B ∘ fsuc) (ab? ∘ fsuc))

-- ε<abs→ε<⊎<-ε : ∀ (ε : ℝ₊) x → fst ε <ᵣ absᵣ x →
--                         (x <ᵣ -ᵣ (fst ε)) ⊎ (fst ε <ᵣ x)
-- ε<abs→ε<⊎<-ε ε x ε<∣x∣ =

--    ⊎.map (λ x<0 → isTrans≡<ᵣ _ _ _
--         (sym (-ᵣInvol _) ∙
--          cong -ᵣ_ (sym (absᵣNeg _ x<0))) (-ᵣ<ᵣ _ _ ε<∣x∣))
--       (λ 0<x → isTrans<≡ᵣ _ _ _ ε<∣x∣ (absᵣPos _ 0<x))
--    (invEq (＃≃0<dist x 0)
--       (isTrans<≡ᵣ _ _ _
--         (isTrans<ᵣ _ _ _ (snd ε) ε<∣x∣)
--         (cong absᵣ (sym (𝐑'.+IdR' _ _ (-ᵣ-rat 0))))))
--  where
--  -ε<ε = isTrans<ᵣ _ _ _
--     (isTrans<≡ᵣ _ _ _
--       (-ᵣ<ᵣ _ _ (snd ε))
--       (-ᵣ-rat 0))
--     (snd ε)

-- record Partition*[_,_] (a b : ℝ) : Type₀ where
--  field
--   a≤b : a ≤ᵣ b
--   len : ℕ
--   pts : Fin (len) → ℝ
--   a≤pts : ∀ k → a ≤ᵣ pts k
--   pts≤b : ∀ k → pts k ≤ᵣ b
--   pts≤pts : ∀ (k : ℕ) k< sk< → pts (k , k<) ≤ᵣ pts (suc k , sk<)


--  pts'Σ-R : ElimFinSS (Σ-syntax ℝ (λ p → (a ≤ᵣ p) × (p ≤ᵣ b))) len
--  pts'Σ-R .ElimFinSS.a₀ = a , ≤ᵣ-refl a , a≤b
--  pts'Σ-R .ElimFinSS.f k = pts k , a≤pts _ , pts≤b _
--  pts'Σ-R .ElimFinSS.aₙ = b , a≤b , ≤ᵣ-refl b

--  pts'Σ : Fin (2 ℕ.+ len) → Σ[ p ∈ ℝ ] (a ≤ᵣ p) × (p ≤ᵣ b)
--  pts'Σ = ElimFinSS.go pts'Σ-R


--  pts' : Fin (2 ℕ.+ len) → ℝ
--  pts' = fst ∘ pts'Σ

--  a≤pts' : ∀ k → a ≤ᵣ pts' k
--  a≤pts' = fst ∘ snd ∘ pts'Σ

--  pts'≤b : ∀ k → pts' k ≤ᵣ b
--  pts'≤b = snd ∘ snd ∘ pts'Σ


--  isStrictPartition : Type
--  isStrictPartition = ∀ k → pts' (finj k) <ᵣ pts' (fsuc k)

--  mesh≤ᵣ : ℝ → Type
--  mesh≤ᵣ δ = ∀ k →  pts' (fsuc k) -ᵣ pts' (finj k)  ≤ᵣ δ

--  pts'≤pts' : ∀ k → pts' (finj k) ≤ᵣ pts' (fsuc k)
--  pts'≤pts' (zero , l , p) = a≤pts' (1 , l , +-suc _ _ ∙ cong suc p)
--  pts'≤pts' k'@(suc k , zero , p) =
--   let z = pts'≤b (suc k , 1 , cong suc p)
--   in isTrans≡≤ᵣ (pts' (finj k'))
--         (pts' (suc k , 1 , (λ i → suc (p i))))
--         _ (cong {x = finj k'}
--                 {(suc k , 1 , cong suc p)} pts'
--                  (toℕ-injective refl)) z
--  pts'≤pts' (suc k , suc l , p) = 
   
--      subst2 _≤ᵣ_
--          (cong (λ u → pts (k , l ℕ.+ (suc zero) , u))
--            (isSetℕ _ _ _ _))
--          (cong (λ u → pts (suc k , l , u))
--            (isSetℕ _ _ _ _))
--          (pts≤pts k (_ , (sym (ℕ.+-assoc l _ _)) ∙ injSuc p) (_ , injSuc p))


-- open  Partition*[_,_]

-- equalPartitionStrict∃ : ∀ a b → a ≤ᵣ b → (ε : ℚ₊) →
--  ∃[ pa ∈ Partition*[ a , b ] ] (isStrictPartition pa × mesh≤ᵣ pa (rat (fst ε)))
-- equalPartitionStrict∃ a b a≤b ε = {!!}
--   -- PT.map2 w
--   --   (denseℚinℝ a (a +ᵣ fst η)
--   --     (isTrans≡<ᵣ _ _ _
--   --       (sym (+IdR a)) (<ᵣ-o+ _ _ _ (snd η))))
--   --   (denseℚinℝ (b -ᵣ fst η) b
--   --    ((isTrans<≡ᵣ _ _ _
--   --        (<ᵣ-o+ _ _ _
--   --          (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (snd η)) (-ᵣ-rat 0)))
--   --        (+IdR b))))

--   -- where
--   -- Δ₊ : ℝ₊
--   -- Δ₊ = _ , x<y→0<y-x _ _ ?
--   -- η : ℝ₊
--   -- η = minᵣ₊ (Δ₊ ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _))) (ℚ₊→ℝ₊ ε)

--   -- w : _
--   -- w (a' , a<a' , a'<a+η) (b' , b-η<b' , b'<b) =
--   --   w' , ww' , www'
--   --  where
--   --  h = min≤ᵣ (fst (Δ₊ ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)))) (fst (ℚ₊→ℝ₊ ε))
--   --  a'<b' = <ᵣ→<ℚ _ _
--   --    (isTrans<ᵣ _ _ _
--   --      a'<a+η
--   --      (isTrans≤<ᵣ _ _ _
--   --        (a+b≤c⇒b≤c-b _ _ _
--   --          (isTrans≡≤ᵣ _ _ _
--   --            (+ᵣComm _ _
--   --             ∙ sym (+ᵣAssoc _ _ _))
--   --             (b≤c-b⇒a+b≤c _ _ _
--   --              (isTrans≤≡ᵣ _ _ _
--   --                  (≤ᵣMonotone+ᵣ _ _ _ _ h h)
--   --                  (sym
--   --                   (·DistL+ (fst Δ₊) (rat [ 1 / 2 ]) (rat [ 1 / 2 ]))
--   --                   ∙ 𝐑'.·IdR' _ _ (+ᵣ-rat _ _ ∙
--   --                    decℚ≡ᵣ?))))))
--   --        b-η<b'))
--   --  rtp = RefinableTaggedPartition[_,_].tpTP
--   --    (rtp-1/n a' b' (ℚ.<Weaken≤ a' b' a'<b')) ε

--   --  module eqp = Partition[_,_] (fst (fst rtp))
--   --  w' : Partition[ a , b ]
--   --  w' .len = suc (suc eqp.len)
--   --  w' .pts = eqp.pts'
--   --  w' .a≤pts k = isTrans≤ᵣ _ _ _
--   --      (<ᵣWeaken≤ᵣ _ _ a<a') (eqp.a≤pts' k)
--   --  w' .pts≤b k = isTrans≤ᵣ _ _ _ (eqp.pts'≤b k)
--   --        (<ᵣWeaken≤ᵣ _ _ b'<b)
--   --  w' .pts≤pts = eqp.pts'≤pts'

--   --  hlpr : ∀ k k< k<' → pts' w' (suc k , k<) ≡ eqp.pts' (k , k<')
--   --  hlpr k (zero , p) (l , p') =
--   --    ⊥.rec (znots (inj-m+
--   --        (+-zero k ∙ injSuc (injSuc p) ∙ sym p' ∙ +-comm l (suc k)
--   --      ∙ sym (+-suc k l))))
--   --  hlpr k k<@(suc l , snd₁) k<' =
--   --   cong {x = k , _} {(k , k<')}
--   --     eqp.pts' (toℕ-injective refl)

--   --  ww' : isStrictPartition w'
--   --  ww' (zero , zero , p) = ⊥.rec (znots (injSuc p))
--   --  ww' (zero , suc l , p) = a<a'
--   --  ww' (suc zero , zero , p) = ⊥.rec (znots (injSuc (injSuc p)))
--   --  ww' (suc (suc k) , zero , p) = b'<b
--   --  ww' (suc k , suc l , p) =
--   --    subst2 _<ᵣ_
--   --      (sym (hlpr k (snd (finj (suc k , suc l , p))) _))
--   --      (sym (hlpr (suc k) (snd (fsuc (suc k , suc l , p)))
--   --          (snd (fsuc (k , l , _)))))
--   --      (Integration.isStrictEqualPartition (rat a') (rat b')
--   --       _ (<ℚ→<ᵣ _ _ a'<b')
--   --       _
--   --        (k , l , injSuc (sym (+-suc _ _) ∙ injSuc p)))

--   --  www' : mesh≤ᵣ w' (rat (fst ε))
--   --  www' (zero , zero , p) = ⊥.rec (znots (injSuc p))
--   --  www' (zero , suc l , p) =
--   --    isTrans≤ᵣ _ _ _
--   --      (<ᵣWeaken≤ᵣ _ _ (a<c+b⇒a-c<b _ _ _ a'<a+η))
--   --      (min≤ᵣ' (fst (Δ₊ ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)))) (fst (ℚ₊→ℝ₊ ε)))
--   --  www' (suc zero , zero , p) = ⊥.rec (znots (injSuc (injSuc p)))
--   --  www' (suc (suc k) , zero , p) =
--   --    isTrans≤ᵣ _ _ _
--   --      (<ᵣWeaken≤ᵣ _ _ (a-b<c⇒a-c<b _ _ _ b-η<b'))
--   --      (min≤ᵣ' (fst (Δ₊ ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _)))) (fst (ℚ₊→ℝ₊ ε)))
--   --  www' (suc k , suc l , p) =
--   --    isTrans≡≤ᵣ _ _ _
--   --      (cong₂ _-ᵣ_
--   --        (hlpr (suc k) (snd (fsuc (suc k , suc l , p)))
--   --          (snd (fsuc (k , l , _))))
--   --        (hlpr k (snd (finj (suc k , suc l , p))) _))
--   --      (snd rtp (k , l , injSuc (sym (+-suc _ _) ∙ injSuc p)))


-- allOnOneSideLemma : ∀ n (ε : ℝ₊) (f : Fin (suc n) → ℝ)
--             → (∀ k → absᵣ (f (fsuc k) -ᵣ f (finj k)) <ᵣ fst ε )
--             → (∀ k → (f k <ᵣ -ᵣ (fst ε  ·ᵣ rat [ 1 / 2 ]))
--                 ⊎ (fst ε ·ᵣ rat [ 1 / 2 ] <ᵣ f k))

--             → (∀ k → f k <ᵣ -ᵣ (fst ε  ·ᵣ rat [ 1 / 2 ])) ⊎
--               (∀ k → fst ε  ·ᵣ rat [ 1 / 2 ] <ᵣ f k)
-- allOnOneSideLemma zero ε f fΔ f⊎ =
--   ⊎.map
--     (λ f0 k → isTrans≡<ᵣ _ _ _ (cong f (sym (snd (isContrFin1) k) )) f0)
--     (λ f0 k → isTrans<≡ᵣ _ _ _ f0 (cong f (snd (isContrFin1) k)))
--     (f⊎ fzero)
-- allOnOneSideLemma (suc n) ε f fΔ f⊎ =
--   ⊎.map
--     (λ fs → ⊎.rec
--            (λ f0< →
--              λ { (zero , p) →
--                    isTrans≡<ᵣ _ _ _ (cong f (toℕ-injective refl)) f0<
--                ; (suc k , p) →
--                   isTrans≡<ᵣ _ _ _ (cong f (toℕ-injective refl))
--                    (fs (k , ℕ.pred-≤-pred p))})
--            (λ <f0 _ →
--               ⊥.rec
--                  (isAsym<ᵣ (fst ε)
--                            (absᵣ (f (fsuc fzero) -ᵣ f (finj fzero)))
--                    (isTrans<≤ᵣ _ _ _
--                      (isTrans≡<ᵣ _ _ _
--                      ((sym (𝐑'.·IdR' _ _ (+ᵣ-rat _ _ ∙
--                        decℚ≡ᵣ?))
--                       ∙ ·DistL+ _ _ _ )
--                       ∙ cong₂ _+ᵣ_
--                         (sym (-ᵣInvol _))
--                         refl)
--                       (<ᵣMonotone+ᵣ _ _ _ _ (-ᵣ<ᵣ _ _ (fs fzero)) (<f0)))
--                       (isTrans≤≡ᵣ _ _ _
--                         (≤absᵣ _)
--                         (cong absᵣ (+ᵣComm _ _)
--                           ∙ minusComm-absᵣ _ _)))
--                      (fΔ fzero)
--                      ))
--        (f⊎ (finj fzero)))
--     (λ fs → ⊎.rec
--            (λ f0< → ⊥.rec
--                  ((isAsym<ᵣ (fst ε)
--                            (absᵣ (f (fsuc fzero) -ᵣ f (finj fzero)))
--                   ((isTrans<≤ᵣ _ _ _
--                      (isTrans≡<ᵣ _ _ _
--                      ((sym (𝐑'.·IdR' _ _ (+ᵣ-rat _ _ ∙
--                        decℚ≡ᵣ?))
--                       ∙ ·DistL+ _ _ _ )
--                       ∙ cong₂ _+ᵣ_ refl
--                               (sym (-ᵣInvol _))
--                         )
--                           (isTrans<≡ᵣ _ _ _
--                            (<ᵣMonotone+ᵣ _ _ _ _
--                            (fs fzero) (-ᵣ<ᵣ _ _  (f0<)))
--                            (+ᵣComm _ _ ∙
--                              cong₂ _+ᵣ_
--                               (cong (-ᵣ_ ∘ f) (toℕ-injective refl))
--                                refl)))
--                       (isTrans≤≡ᵣ _ _ _
--                         (≤absᵣ _)
--                         (cong absᵣ (+ᵣComm _ _))))))
--                            (fΔ fzero)))
--            (λ <f0 →
--                λ { (zero , p) →
--                      isTrans<≡ᵣ _ _ _ <f0 (cong f (toℕ-injective refl))
--                  ; (suc k , p) →
--                    isTrans<≡ᵣ _ _ _ (fs (k , ℕ.pred-≤-pred p))
--                       (cong f (toℕ-injective refl))})
--        (f⊎ fzero))
--     (allOnOneSideLemma n ε (f ∘ fsuc)
--       ((λ {a} → isTrans≡<ᵣ _ _ _
--        (cong (λ ffa → absᵣ (f (fsuc (fsuc a)) -ᵣ f ffa))
--          (toℕ-injective refl) ))
--        ∘ (fΔ ∘ fsuc))
--        (f⊎ ∘ fsuc))


-- Rolle'sTheorem : ∀ a b → a ≤ᵣ b → ∀ a∈ b∈ f f'
--   → IsUContinuousℙ (intervalℙ a b) f'
--   → uDerivativeOfℙ (intervalℙ a b) , f is f'
--   → f a a∈ ≡ f b b∈
--   → ∀ (ε : ℚ₊) → ∃[ (x₀ , x∈) ∈ Σ _ (_∈ intervalℙ a b) ]
--             absᵣ (f' x₀ x∈) <ᵣ rat (fst ε)
-- Rolle'sTheorem a b a≤b a∈ b∈ f f' ucf udf fa≡fb ε = 
--   PT.rec squash₁ (w (ucf ε)) (udf (/2₊ ε))

--  where
--  w : _ → _ → _
--  w (δ , X) (δ' , X') = PT.rec squash₁ ww
--    (equalPartitionStrict∃ a b a≤b δ⊓δ')
--   where
--   δ⊓δ' = ℚ.min₊ (/2₊ δ) (/2₊ δ')


--   ww : _
--   ww (pa , str-pa , mesh-pa) =
--     PT.rec squash₁
--       (⊎.rec (∀case ∘ (ε<abs→ε<⊎<-ε (ℚ₊→ℝ₊ (/2₊ ε)) _ ∘_))
--              (∣_∣₁ ∘ (_ ,_) ∘ snd))
--      (Fin-∀A⊎∃B (suc Pa.len)
--        _ _
--         λ k → PT.map (Iso.fun ⊎-swap-Iso) (Dichotomyℝ'
--                         (rat (fst (/2₊ ε)))
--                    (absᵣ (f' (Pa.pts' (finj k))
--                      (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))))
--                    ((rat (fst ε)))
--                    (<ℚ→<ᵣ _ _ (ℚ.x/2<x ε))))
--    where
--    module Pa = Partition*[_,_] pa



--    z : ∀ f f' → f a a∈ ≡ f b b∈ →
--           ((x : ℝ) (x∈ : x ∈ intervalℙ a b) (h : ℝ)
--            (h∈ : x +ᵣ h ∈ intervalℙ a b) (0＃h : rat [ pos 0 / 1+ 0 ] ＃ h) →
--            absᵣ h <ᵣ rat (fst δ') →
--            absᵣ (f' x x∈ -ᵣ differenceAtℙ (intervalℙ a b) f x h 0＃h x∈ h∈) <ᵣ
--            rat (fst (/2₊ ε)))
--         → ∃-syntax (Fin (suc Pa.len))
--         (λ k → (-ᵣ rat (fst ε))
--           <ᵣ f' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k)))
--    z f f' fa≡fb X' = 
--     PT.map
--           (map-snd
--            λ {l} X → 0<y-x→x<y _ _
--              (isTrans<≡ᵣ _ _ _
--               (isTrans≡<ᵣ _ _ _ (sym (𝐑'.0LeftAnnihilates _))
--               (invEq (z/y<x₊≃z<y₊·x _ _ (_ , x<y→0<y-x _ _ (str-pa l)))
--                 (isTrans<≡ᵣ _ _ _ X
--                 (·ᵣComm _ _))))
--                 (cong₂ _+ᵣ_ refl
--                  (sym (-ᵣInvol _)))))
                 
--         (Bishop-Proposition7 (suc (Pa.len))
         
--         (λ k → (f' (Pa.pts' (finj k))
--                      (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
--                     +ᵣ rat (fst ε))
--              ·ᵣ (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k)))
        
--         (isTrans≡<ᵣ _ _ _
--            (sym (𝐑'.+InvR' _ _ (sym fa≡fb))
--              ∙ cong₂ _-ᵣ_
--                 (cong (f b) (∈-isProp (intervalℙ a b) _ _ _))
--                 (cong (f a) (∈-isProp (intervalℙ a b) _ _ _))
--              ∙ sym ((deltas-sum (suc Pa.len)
--                λ k → f (Pa.pts' k) (Pa.a≤pts' k , Pa.pts'≤b k))))
--                (foldFin+< (Pa.len) 0 0
--                  _ _ (idfun _) (idfun _) (≤ᵣ-refl 0) <f)))

--     where
--     <f : (k : Fin (suc (Pa.len))) →
--           f (Pa.pts' (fsuc k)) ((Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k)))
--            -ᵣ f (Pa.pts' (finj k)) _
--           <ᵣ
--           (f' (Pa.pts' (finj k)) _ +ᵣ rat (fst ε))
--           ·ᵣ
--           (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))
--     <f k = isTrans<ᵣ _ _ _ (isTrans<≡ᵣ _ _ _
--       (fst (z/y<x₊≃z<y₊·x _ _ _) fromX') (·ᵣComm _ _))
--            (<ᵣ-·ᵣo _ _
--              (_ , x<y→0<y-x _ _ (str-pa k))
--              (<ᵣ-o+ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.x/2<x ε))))
--      where
--      fromX' : _ <ᵣ f' (Pa.pts' (finj k)) _ +ᵣ rat (fst (/2₊ ε))
--      fromX' = (isTrans≡<ᵣ _ _ _
--        (cong₂ _·ᵣ_
--          (cong₂ _-ᵣ_
--            (cong (uncurry f)
--              (Σ≡Prop (∈-isProp (intervalℙ a b)) (sym L𝐑.lem--05)) )
--            refl)
--         (invℝ₊≡invℝ (_ , x<y→0<y-x _ _ (str-pa k)) _))
--        (isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ _ _
--         (isTrans≤<ᵣ _ _ _
--          (≤absᵣ _)
--          (isTrans≡<ᵣ _ _ _
--           (minusComm-absᵣ _ _)
--             (X' (Pa.pts' (finj k)) (Pa.a≤pts' (finj k) , Pa.pts'≤b (finj k))
--         (Pa.pts' (fsuc k) -ᵣ Pa.pts' (finj k))
--         (subst-∈ (intervalℙ a b)
--           (sym L𝐑.lem--05)
--            (Pa.a≤pts' (fsuc k) , Pa.pts'≤b (fsuc k)))
--         (invEq (＃Δ _ _) (inl (str-pa k)))
--         (isTrans≡<ᵣ _ _ _
--           (absᵣNonNeg _ (x≤y→0≤y-x _ _ (Pa.pts'≤pts' k )))
--           (isTrans≤<ᵣ _ _ _
--             (isTrans≤ᵣ _ _ _
--               (mesh-pa k)
--               (≤ℚ→≤ᵣ (fst δ⊓δ')  (fst (/2₊ δ'))
--                 (ℚ.min≤' (fst (/2₊ δ)) (fst (/2₊ δ')))))
--             (<ℚ→<ᵣ _ _ (ℚ.x/2<x δ'))))))))
--             (+ᵣComm _ _)))


--    z' : ∃-syntax (Fin (suc (Pa.len)))
--         (λ k → f' (Pa.pts' (finj k)) _ <ᵣ rat (fst ε))
--    z' = 
--      PT.map (map-snd (<ᵣ-ᵣ _ _))
--           (z (λ x x∈ → -ᵣ (f x x∈))
--                (λ x x∈ → -ᵣ (f' x x∈))
--                 (cong -ᵣ_ fa≡fb)
--                  λ x x∈ h h∈ 0＃h h<δ' →
--                   isTrans≡<ᵣ _ _ _
--                      (cong absᵣ (sym (-ᵣDistr _ _)) ∙
--                       sym (-absᵣ _)
--                         ∙ cong (absᵣ ∘ (f' x x∈ +ᵣ_))
--                           (cong (_·ᵣ invℝ h 0＃h)
--                             (sym (-ᵣDistr _ _))
--                             ∙ -ᵣ· _ _) )
--                      (X' x x∈ h h∈ 0＃h h<δ'))


--    ∀case : ((a₁ : Fin (suc (Pa.len))) →
--             (f' (Pa.pts' (finj a₁)) _ <ᵣ -ᵣ fst (ℚ₊→ℝ₊ (/2₊ ε)))
--             ⊎
--             (fst (ℚ₊→ℝ₊ (/2₊ ε)) <ᵣ f' (Pa.pts' (finj a₁)) _)) →
--             ∃ (Σ ℝ (_∈ intervalℙ a b))
--             (λ v → absᵣ (f' (v .fst) (v .snd)) <ᵣ rat (fst ε))
--    ∀case =
--         ⊎.rec
--           (λ ∀f< → PT.map
--               (λ (k , U) →
--                 _ ,
--                  isTrans≡<ᵣ _ _ _
--                    (abs-max _)
--                     (max<-lem _ _ _
--                       (isTrans<ᵣ _ _ _ (∀f< k)
--                         (isTrans<ᵣ _ 0 _
--                           (isTrans<≡ᵣ _ _ _
--                             (-ᵣ<ᵣ _ _
--                               (snd ((ℚ₊→ℝ₊ ε) ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ] , _))))
--                            (-ᵣ-rat 0)) (snd (ℚ₊→ℝ₊ ε))))
--                       (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ U) (-ᵣInvol _))))
--               (z f f' fa≡fb X'))
              
--           (λ ∀<f → PT.map
--              (λ (k , U) →
--                 _ ,
--                  isTrans≡<ᵣ _ _ _
--                    (abs-max _)
--                     (max<-lem _ _ _ U
--                       (isTrans<ᵣ _ _ _
--                         (-ᵣ<ᵣ _ _ (∀<f k))
--                         ((isTrans<ᵣ _ 0 _
--                           (isTrans<≡ᵣ _ _ _
--                             (-ᵣ<ᵣ _ _
--                               (snd ((ℚ₊→ℝ₊ ε) ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ] , _))))
--                            (-ᵣ-rat 0)) (snd (ℚ₊→ℝ₊ ε)))))))
--              z')
--      ∘  allOnOneSideLemma (Pa.len) (ℚ₊→ℝ₊ ε) _
--                           (fst (∼≃abs<ε _ _ ε) ∘
--                λ k → (X _ _ _ _
--                 (invEq (∼≃abs<ε _ _ δ)
--                   (isTrans≤<ᵣ _ _ _
--                     (isTrans≡≤ᵣ _ _ _
--                       (cong {x = finj (fsuc k)} {(fsuc (finj k))}
--                        (λ aa → absᵣ (Pa.pts' aa
--                          +ᵣ -ᵣ Pa.pts' (finj (finj k))))
--                          (toℕ-injective refl)
--                         ∙ absᵣPos _ (x<y→0<y-x _ _
--                         (str-pa (finj k))))
--                       (mesh-pa (finj k)))
--                     (<ℚ→<ᵣ _ _
--                      (ℚ.isTrans≤< (fst δ⊓δ') _ _
--                        (ℚ.min≤ (fst (/2₊ δ)) (fst (/2₊ δ')))
--                        (ℚ.x/2<x δ))
--                      )))))
--      ∘ (⊎.map (flip (isTrans<≡ᵣ _ _ _) (cong -ᵣ_ (rat·ᵣrat (fst ε) _)))
--               (isTrans≡<ᵣ _ _ _ (sym (rat·ᵣrat (fst ε) _)))
--          ∘_)

-- meanValue : ∀ a b → a ≤ᵣ b → ∀ a∈ b∈ f f'
--        →  IsUContinuousℙ (intervalℙ a b) f'
--        →  uDerivativeOfℙ (intervalℙ a b) , f is f'
--        → (ε : ℚ₊) →
--           ∃[ (x₀ , x∈) ∈ Σ _ (_∈ intervalℙ a b) ]
--            absᵣ ((f b b∈ -ᵣ f a a∈)  -ᵣ f' x₀ x∈ ·ᵣ (b -ᵣ a)) <ᵣ rat (fst ε)
-- meanValue a b a≤b a∈ b∈ f f' ucf udf =
--   PT.rec (isPropΠ λ _ → squash₁) (λ uch' → Rolle'sTheorem a b a≤b a∈ b∈
--      h h' uch' udh ha≡hb)
--       uch


--  where
--   h h' : (x : ℝ) → x ∈ intervalℙ a b → ℝ
--   h x x∈ = ((x -ᵣ a) ·ᵣ (f b b∈ -ᵣ f a a∈))
--                 -ᵣ f x x∈ ·ᵣ (b -ᵣ a)

--   h' x x∈ = (f b b∈ -ᵣ f a a∈) -ᵣ f' x x∈ ·ᵣ (b -ᵣ a)

--   uch : ∥ IsUContinuousℙ (intervalℙ a b) h' ∥₁
--   uch = PT.map (λ z → IsUContinuous∘ℙ (intervalℙ a b)
--        (IsUContinuous∘ (IsUContinuous+ᵣL (f b b∈ -ᵣ f a a∈))
--           (subst IsUContinuous (funExt λ x → ·-ᵣ _ _)
--             z))
--        ucf) (IsUContinuous·ᵣR (-ᵣ (b -ᵣ a)))

--   udh0 : _
--   udh0 = +uDerivativeℙ (intervalℙ a b)
--     (λ x _ → ((x -ᵣ a) ·ᵣ (f b b∈ -ᵣ f a a∈)))
--      (λ _ _ → (f b b∈ -ᵣ f a a∈))
--     _ _
--     (subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
--       (funExt₂ λ x x∈ → ·ᵣComm _ _)
--       (funExt₂ λ x x∈ → 𝐑'.·IdR' _ _ (+IdR 1))
--       (C·uDerivativeℙ (intervalℙ a b)
--        _ _ _ (+uDerivativeℙ (intervalℙ a b)
--         _ _ _ _
--         (uDerivativeℙ-id (intervalℙ a b))
--         (uDerivativeℙ-const (intervalℙ a b) (-ᵣ a))) ))
--     (C·uDerivativeℙ (intervalℙ a b) (-ᵣ (b -ᵣ a))
--      _ _
--      udf)

--   udh : uDerivativeOfℙ intervalℙ a b , h is h'
--   udh = subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
--            (funExt₂ λ x x∈ →
--             cong₂ _+ᵣ_ refl (-ᵣ· _ _ ∙ cong -ᵣ_ (·ᵣComm _ _)))
--            (funExt₂ λ x x∈ →
--             cong₂ _+ᵣ_ refl (-ᵣ· _ _ ∙ cong -ᵣ_ (·ᵣComm _ _)))
--            udh0


--   ha≡hb : h a a∈ ≡ h b b∈
--   ha≡hb = 𝐑'.+IdL' _ _ (𝐑'.0LeftAnnihilates' _ _ (+-ᵣ a))
--     ∙ sym (-ᵣ· _ _)
--     ∙ cong (_·ᵣ (b -ᵣ a)) (sym L𝐑.lem--063)
--     ∙ 𝐑'.·DistL- (f b b∈ -ᵣ f a a∈) (f b b∈) (b -ᵣ a)
--     ∙ cong₂ _-ᵣ_ (·ᵣComm _ _) refl

-- nullDerivative→const : ∀ a b a∈ b∈ → a ≤ᵣ b → ∀ f
--        → uDerivativeOfℙ (intervalℙ a b) , f is (λ _ _ → 0)
--        → f a a∈ ≡ f b b∈
-- nullDerivative→const a b a∈ b∈ a≤b f udf  =
--   eqℝ _ _ λ ε →
--     PT.rec (isProp∼ _ _ _)
--       (λ (_ , X) →
--         sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
--           (isTrans≡<ᵣ _ _ _
--             (cong absᵣ
--               (sym (𝐑'.+IdR' _ _
--                 (cong -ᵣ_ (𝐑'.0LeftAnnihilates (b -ᵣ a))
--                  ∙ -ᵣ-rat 0))))
--             X)))
--       (meanValue a b a≤b a∈ b∈ f
--         (λ _ _ → 0) (λ ε₁ → 1 , λ _ _ _ _ _ → refl∼ _ _) udf ε)

