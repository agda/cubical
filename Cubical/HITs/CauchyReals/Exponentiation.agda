{-# OPTIONS --safe  --lossy-unification #-} --

module Cubical.HITs.CauchyReals.Exponentiation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos; ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

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
open import Cubical.HITs.CauchyReals.NthRoot



ointervalℙ⊆-max : ∀ n m →
           ointervalℙ
           (rat (ℚ.- fromNat (suc n)))
           (rat (fromNat (suc n))) ⊆
           ointervalℙ
           (rat (ℚ.- fromNat (suc (max n m))))
           (rat (fromNat (suc (max n m))))
ointervalℙ⊆-max n m x (≤x , x≤) =
    (isTrans≤<ᵣ _ _ _
    (≤ℚ→≤ᵣ _ _ (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≥→negsuc-≤-negsuc _ _ ℕ.left-≤-max)))
    ≤x)
  , isTrans<≤ᵣ _ _ _ x≤
       (≤ℚ→≤ᵣ _ _ (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
         (ℕ.left-≤-max {suc n} {suc m}))))


ointervalℙ⊆-max' : ∀ n m →
           ointervalℙ
           (rat (ℚ.- fromNat (suc m)))
           (rat (fromNat (suc m))) ⊆
           ointervalℙ
           (rat (ℚ.- fromNat (suc (max n m))))
           (rat (fromNat (suc (max n m))))
ointervalℙ⊆-max' n m x (≤x , x≤) =
  (isTrans≤<ᵣ _ _ _
    (≤ℚ→≤ᵣ _ _ (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≥→negsuc-≤-negsuc _ _ ℕ.right-≤-max)))
    ≤x)
  , isTrans<≤ᵣ _ _ _ x≤
       (≤ℚ→≤ᵣ _ _ (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
         (ℕ.right-≤-max {suc m} {suc n}))))


module RestrℝIso (a b fa fb : ℝ)
      (isom :
          Iso (Σ ℝ (_∈ ointervalℙ a b))
              (Σ ℝ (_∈ ointervalℙ fa fb))) where

 open Iso isom

 module _ (monotoneFun : ∀ x y → fst x ≤ᵣ fst y → fst (fun x) ≤ᵣ fst (fun y))
          (monotoneInv : ∀ x y → fst x ≤ᵣ fst y → fst (inv x) ≤ᵣ fst (inv y))
          (a' b' : ℝ) (a'<b' : a' <ᵣ b')
          (a'∈ : a' ∈ ointervalℙ a b)
          (b'∈ : b' ∈ ointervalℙ a b) where

  fa' = fun (a' , a'∈)
  fb' = fun (b' , b'∈)

  restrIso : Iso (Σ ℝ (_∈ intervalℙ a' b'))
                 (Σ ℝ (_∈ intervalℙ (fst fa') (fst fb')))
  restrIso .Iso.fun (x , ≤x , x≤) =
    let X = (x ,
             (isTrans<≤ᵣ _ _ _ (fst a'∈) ≤x)
               , isTrans≤<ᵣ _ _ _ x≤ (snd b'∈))
        (fx , fx∈) = fun X
    in fx , monotoneFun (a' , a'∈) X ≤x
          , monotoneFun X (b' , b'∈) x≤
  restrIso .Iso.inv (x , ≤x , x≤) =
    let X = (x ,
             (isTrans<≤ᵣ _ _ _ (fst (snd fa')) ≤x)
               , isTrans≤<ᵣ _ _ _ x≤ (snd (snd fb')))
        (fx , fx∈) = inv X
    in fx , isTrans≡≤ᵣ _ _ _ (sym (cong fst (leftInv (a' , a'∈))))
            (monotoneInv fa' X ≤x)
          , isTrans≤≡ᵣ _ _ _ (monotoneInv X fb' x≤)
            (cong fst (leftInv (b' , b'∈)))
  restrIso .Iso.rightInv _ =
   Σ≡Prop (∈-isProp (intervalℙ _ _))
     (cong fst
        ((cong fun (Σ≡Prop (∈-isProp (ointervalℙ _ _))
          (refl))) ∙ rightInv _))

  restrIso .Iso.leftInv _ =
   Σ≡Prop (∈-isProp (intervalℙ _ _))
     (cong fst
        ((cong inv (Σ≡Prop (∈-isProp (ointervalℙ _ _))
          (refl))) ∙ leftInv _))


module EquivFromRestr
     (f : ℝ → ℝ)

     (f∈ₙ : ∀ n x → (x ∈ (ointervalℙ
                      (rat (ℚ.- fromNat (suc n)))
                      (rat (fromNat (suc n))))) →
                       f x ∈ (ointervalℙ
                      (f (rat (ℚ.- fromNat (suc n))))
                      (f (rat (fromNat (suc n))))))
     (equiv-restr : ∀ n →
       isEquiv {A = Σ ℝ (_∈ (ointervalℙ
                      (rat (ℚ.- fromNat (suc n)))
                      (rat (fromNat (suc n)))))}
               {B = Σ ℝ (_∈ (ointervalℙ
                      (f (rat (ℚ.- fromNat (suc n))))
                      (f (rat (fromNat (suc n))))))}
                λ (x , x∈) → f x , f∈ₙ n x x∈) where

 clamp' : ∀ x → ∃[ n ∈ ℕ ] (x ∈ (ointervalℙ
                  ((rat (ℚ.- fromNat (suc n))))
                  ((rat (fromNat (suc n))))))
 clamp' x =
   PT.map (λ (1+ n , X) →
        n
     , isTrans<≡ᵣ _ _ _
           (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat  _)) (-ᵣ<ᵣ _ _ (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
           (isTrans≡<ᵣ _ _ _ (sym (-absᵣ _)) X))))

            (-ᵣInvol x)
     , isTrans≤<ᵣ _ _ _ (≤absᵣ _) X)
     (getClamps x)

 Bℙ : ℙ ℝ
 Bℙ x = (∃[ n ∈ ℕ ] (x ∈ (ointervalℙ
                      (f (rat (ℚ.- fromNat (suc n))))
                      (f (rat (fromNat (suc n))))))) , squash₁

 f' : ℝ → Σ ℝ (_∈ Bℙ)
 f' x = f x , PT.map (map-snd (λ {n} → f∈ₙ n x)) (clamp' x)

 f-inj : ∀ w x → f w ≡ f x → w ≡ x
 f-inj w x =
   PT.rec2 (isProp→ (isSetℝ _ _))
     (λ (n , N) (m , M) →
      λ fw=fx →
         cong fst (invEq (congEquiv
       {x = w , ointervalℙ⊆-max n m w N}
       {y = x , ointervalℙ⊆-max' n m x M} (_ , equiv-restr (ℕ.max n m)))
         (Σ≡Prop (∈-isProp _) fw=fx)))
    (clamp' w) (clamp' x)

 isEmbedding-f' : isEmbedding f'
 isEmbedding-f' w x =
  snd (propBiimpl→Equiv (isSetℝ _ _)
      ((isSetΣ isSetℝ (isProp→isSet ∘ ∈-isProp Bℙ)) _ _)
    (cong f')
    (f-inj w x ∘ cong fst))

 isSurjection-f' : isSurjection f'
 isSurjection-f' = λ (x , x∈) →
   PT.map (λ (n , N) →
    let (y , y∈) = invEq (_ , equiv-restr n) (_ , N)
    in y , Σ≡Prop (∈-isProp _) (cong fst (secEq (_ , equiv-restr n) (_ , N))))
    x∈

 equiv-fromRestr : isEquiv f'
 equiv-fromRestr = isEmbedding×isSurjection→isEquiv
  (isEmbedding-f' , isSurjection-f')


ℚApproxℙ''→ℚApproxℙ' : ∀ (P Q : ℙ ℝ) f  →
  (ℚApproxℙ'' P Q f) → (ℚApproxℙ' P Q f)
ℚApproxℙ''→ℚApproxℙ' P Q f X q q∈P =
  fst ∘ X q q∈P ∘ /2₊
  , fst ∘ snd ∘ X q q∈P ∘ /2₊ , zz ,

    eqℝ _ _ λ ε →
       let z = triangle∼ {ε = (/2₊ ε ℚ₊+ /2₊ (/2₊ ε)) ℚ₊+ (/2₊ (/2₊ (/2₊ ε)))}
                    (lim-rat (rat ∘ fst ∘ X q q∈P ∘ /2₊) _ _
                      (/2₊ (/2₊ ε))
                      _ (subst 0<_
                         (sym (𝐐'.plusMinus _ _)
                            ∙ cong (ℚ._- fst (/2₊ (/2₊ ε))) (
                               sym (ℚ.+Assoc _ _ _)
                              ∙∙ cong (fst (/2₊ ε) ℚ.+_) (ℚ.+Comm _ _)
                               ∙∙ ℚ.+Assoc _ _ _) )
                         (snd ((/2₊ ε) ℚ₊+ (/2₊ (/2₊ (/2₊ ε))))  )) (refl∼ _ _))

                  (snd (snd (X q q∈P (/2₊ (/2₊ (/2₊ ε))))))
       in subst∼ (sym (ℚ.+Assoc _ _ _)
               ∙∙ cong ((fst (/2₊ ε) ℚ.+ fst (/2₊ (/2₊ ε))) ℚ.+_)
                     (ℚ.ε/2+ε/2≡ε _)
               ∙∙ (sym (ℚ.+Assoc _ _ _)
                ∙∙ cong (fst (/2₊ ε) ℚ.+_) (ℚ.ε/2+ε/2≡ε _)
                ∙∙ ℚ.ε/2+ε/2≡ε (fst ε))) z
 where
 zz : (δ ε : ℚ₊) →
      rat (fst (X q q∈P (/2₊ δ))) ∼[ δ ℚ₊+ ε ]
      rat (fst (X q q∈P (/2₊ ε)))
 zz δ ε = ∼-monotone< (
       subst (ℚ._< fst (δ ℚ₊+ ε)) (ℚ.·DistR+ _ _ _) (x/2<x (δ ℚ₊+ ε)))
   (triangle∼ (snd (snd ((X q q∈P) (/2₊ δ)))) --((snd ((X q q∈P) (/2₊ δ))))
     (sym∼ _ _ _ (snd ((snd ((X q q∈P) (/2₊ ε))))) --((snd ((X q q∈P) (/2₊ ε))))
     ))




clamp-abs : ∀ L L' x → L ℚ.≤ L' →
     ℚ.abs (ℚ.clamp L L' x) ℚ.≤ ℚ.max (ℚ.abs L) (ℚ.abs L')
clamp-abs L L' x L≤L' = ⊎.rec
  (λ 0≤ → subst (ℚ._≤ ℚ.max (ℚ.abs L) (ℚ.abs L'))
     (sym (ℚ.absNonNeg _ 0≤))
       (ℚ.isTrans≤ _ _ _ (ℚ.clamp≤ L L' x)
        (ℚ.isTrans≤ _ _ _
          (ℚ.≤abs _) (ℚ.≤max' _ _))))
  (λ <0 →
     subst (ℚ._≤ ℚ.max (ℚ.abs L) (ℚ.abs L'))
       (sym (ℚ.absNeg _ <0))
       (ℚ.isTrans≤ _ _ _
         (ℚ.isTrans≤ _ _ _
          (ℚ.minus-≤ _ _ (ℚ.≤clamp L L' x L≤L'))
          (subst (ℚ.- L ℚ.≤_) (sym (ℚ.abs'≡abs L)) (ℚ.-≤abs' L)))
         (ℚ.≤max _ _)))
  (ℚ.Dichotomyℚ 0 (ℚ.clamp L L' x))

module _ (f : ℚ → ℝ) (B : ℕ → ℚ₊)  where

 boundedLipschitz : Type
 boundedLipschitz =
   ∀ n x y
       → ℚ.abs x ℚ.≤ fromNat (suc n)
       → ℚ.abs y ℚ.≤ fromNat (suc n)
     →  absᵣ (f y -ᵣ f x) ≤ᵣ rat (fst (B n) ℚ.· ℚ.abs (y ℚ.- x))

 module BoundedLipsch (bl : boundedLipschitz) where


  flₙ : ∀ n → Σ (Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (B n))) (IsContinuous ∘ fst)
  flₙ n = fl , uncurry (Lipschitz→IsContinuous _) fl
   where
   fl = fromLipschitz (B n)
     (f ∘ ℚ.clamp (fromNeg (suc n)) (fromNat (suc n)) ,
         Lipschitz-ℚ→ℝ'→Lipschitz-ℚ→ℝ _ _
           λ q r → isTrans≤ᵣ _ _ _ (bl n
             (ℚ.clamp (fromNeg (suc n)) (fromNat (suc n)) r)
             (ℚ.clamp (fromNeg (suc n)) (fromNat (suc n)) q)
              (ℚ.isTrans≤ _ _ _ (clamp-abs _ _ _
                (ℚ.≤ℤ→≤ℚ _ _ ℤ.negsuc<pos))
                ((ℚ.≡Weaken≤ _ _ (((ℚ.≤→max (ℚ.abs (fromNeg (suc n)))
                    (ℚ.abs (fromNat (suc n))
                     ) (ℚ.≡Weaken≤ _ _
                        ((ℚ.absNeg _
                         (ℚ.<ℤ→<ℚ _ _ ℤ.negsuc<-zero)
                          ) ∙ sym (ℚ.absPos _ (ℚ.0<sucN _))))))
                      ∙ ℚ.absPos _ (ℚ.0<sucN _)))) )
              (ℚ.isTrans≤ _ _ _ (clamp-abs _ _ _
                (ℚ.≤ℤ→≤ℚ _ _ ℤ.negsuc<pos))
                ((ℚ.≡Weaken≤ _ _ (((ℚ.≤→max (ℚ.abs (fromNeg (suc n)))
                    (ℚ.abs (fromNat (suc n))
                     ) (ℚ.≡Weaken≤ _ _
                        ((ℚ.absNeg _
                         (ℚ.<ℤ→<ℚ _ _ ℤ.negsuc<-zero)
                          ) ∙ sym (ℚ.absPos _ (ℚ.0<sucN _))))))
                      ∙ ℚ.absPos _ (ℚ.0<sucN _)))) ))
              (≤ℚ→≤ᵣ _ _ (ℚ.≤-o· _ _ _ (ℚ.0≤ℚ₊ (B n))
                (ℚ.clampDist _ _ _ _))))


  Seq⊆→Power : Seq⊆→ ℝ Seq⊆-abs<N
  Seq⊆→Power .Seq⊆→.fun x n _ = fst (fst (flₙ n)) x
  Seq⊆→Power .Seq⊆→.fun⊆ x n m x∈@(<x , x<) x'∈@(<x' , x'<) n<m =
    (cong (fst (fst (flₙ n))) (∈ℚintervalℙ→clampᵣ≡ _ _ _
      (<ᵣWeaken≤ᵣ _ _ <x , <ᵣWeaken≤ᵣ _ _ x<)) ∙∙
    ≡Continuous _ _
       (IsContinuous∘ _ _ (snd (flₙ n))
         (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n)) ))
       (IsContinuous∘ _ _ (snd (flₙ m))
         (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n)) ))
        (λ x →
         cong f
          (sym (clamp-contained-agree _ _ _ _ _
          (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≥→negsuc-≤-negsuc _ _ (ℕ.<-weaken n<m)))
           (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc n<m)))
           (clam∈ℚintervalℙ _ _ (ℚ.≤ℤ→≤ℚ _ _ ℤ.negsuc<pos) _))))
             x
    ∙∙ cong (fst (fst (flₙ m))) (
       sym (∈ℚintervalℙ→clampᵣ≡ _ _ _
      (<ᵣWeaken≤ᵣ _ _ <x , <ᵣWeaken≤ᵣ _ _ x<))))


  open Seq⊆→.FromIntersection Seq⊆→Power
    isSetℝ (λ _ → Unit , isPropUnit) Seq⊆-abs<N-s⊇-⊤Pred public

  𝒇 : ℝ → ℝ
  𝒇 x = ∩$ x _



  𝒇-rat : ∀ q → 𝒇 (rat q) ≡ f q
  𝒇-rat q = PT.rec (isSetℝ _ _) (λ y → snd (snd y) ∙ cong f
        (sym (∈ℚintervalℙ→clam≡ _ _ _
          (∈intervalℙ→∈ℚintervalℙ _ _ _
             (<ᵣWeaken≤ᵣ _ _ (fst (fst (snd y))) ,
              <ᵣWeaken≤ᵣ _ _ (snd (fst (snd y))))))))
    (∩$-lem (rat q) _)

  𝒇-cont : IsContinuous 𝒇
  𝒇-cont = contDropPred 𝒇 (∩$-cont _ _ (λ _ → openIintervalℙ _ _)
     _ _ λ n → AsContinuousWithPred (λ _ → _ ,
         isProp× _ _)
                 (fst (fst (flₙ n)))
                  (snd (flₙ n)))
  module Equiv𝒇₊ (f∈ : ∀ n x x∈ → fst (fst (flₙ n)) x ∈
                   ointervalℙ (𝒇 (fromNeg (suc n)))
                             (𝒇 (fromNat (suc n))))
           (isEquivFₙ : ∀ n →
           isEquiv
              {A = Σ _ (_∈ ointervalℙ (fromNeg (suc n)) (fromNat (suc n)))}
              {B = Σ _ (_∈ ointervalℙ (𝒇 (fromNeg (suc n)))
                                      (𝒇 (fromNat (suc n))))}
             λ (x , x∈) →
                ((fst (fst (flₙ n))) x) ,
                  f∈ n x x∈)
           (exN' : ∀ b → 0 <ᵣ b → ∃[ n ∈ ℕ ]
                  b ∈
                   ointervalℙ (𝒇 (fromNeg (suc n)))
                             (𝒇 (fromNat (suc n))))
           (𝒇-pos : ∀ x → 0 <ᵣ 𝒇 x)
      where

   𝒇₊ : ℝ → ℝ₊
   𝒇₊ x = 𝒇 x , 𝒇-pos x

   isEmbedding-𝒇 : isEmbedding {A = ℝ} {B = ℝ₊} 𝒇₊
   isEmbedding-𝒇 w x =
    snd
     (propBiimpl→Equiv (isSetℝ _ _) (isSetℝ₊ _ _)
      (cong 𝒇₊)
      ((∩$-elimProp2 w _ x _ {λ u v → u ≡ v → w ≡ x}
       (λ _ _ → isProp→ (isSetℝ _ _))
        λ n w∈ x∈ p → cong fst
          (invEq (congEquiv {x = _ , w∈} {y = _ , x∈}
            (_ , isEquivFₙ n))
            (Σ≡Prop (∈-isProp
             (ointervalℙ
               (𝒇 (fromNeg (suc n)))
               (𝒇 (fromNat (suc n))))) p)) ) ∘ cong fst)
               )

   isSurjection-𝒇 : isSurjection 𝒇₊
   isSurjection-𝒇 (b , b∈') =
     PT.map (λ (n , b∈) →
       let (y , y∈) = invEq (_ , isEquivFₙ n) (b , b∈)
       in y , ℝ₊≡
            (∩$-∈ₙ _ _ n y∈
           ∙ cong fst (secEq (_ , isEquivFₙ n) (b , b∈))))
       (exN' b b∈')

   𝒇₊-equiv : isEquiv 𝒇₊
   𝒇₊-equiv = isEmbedding×isSurjection→isEquiv
     (isEmbedding-𝒇 , isSurjection-𝒇)

  lipFₙ : ∀ n → Lipschitz-ℝ→ℝℙ (B n)
       (intervalℙ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n))))
       (λ x _ → fst (fst (flₙ n)) x)
  lipFₙ n u _ v _ = snd (fst (flₙ n)) u v

  module _ (K : ℕ → ℚ₊) where
   boundedInvLipschitz : Type
   boundedInvLipschitz =
     ∀ n x y
         → ℚ.abs x ℚ.≤ fromNat (suc n)
         → ℚ.abs y ℚ.≤ fromNat (suc n)
       →  rat (ℚ.abs (y ℚ.- x)) ≤ᵣ rat (fst (K n)) ·ᵣ absᵣ (f y -ᵣ f x)

   module BoundedInvLipsch (ibl : boundedInvLipschitz)
              -- (𝒇-pos : ∀ x → 0 <ᵣ 𝒇 x)
              -- (aprox : ℚApproxℙ' ⊤Pred (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , squash₁)
              --     λ x _ → 𝒇 x , 𝒇-pos x)
              where
    invLipFₙ : ∀ n → Invlipschitz-ℝ→ℝℙ (K n)
      (intervalℙ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n))))
      (λ x _ → fst (fst (flₙ n)) x)
    invLipFₙ n u u∈ v v∈ ε X =
     let X' = fst (∼≃abs<ε _ _ _) X


     in invEq (∼≃abs<ε _ _ _)
          (isTrans≤<ᵣ _ _ _
            bil-clamp
            (isTrans<≡ᵣ _ _ _
              (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ (K n)) X')
              (sym (rat·ᵣrat _ _))))

        where

         u' = clampᵣ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
                (rat [ pos (suc n) / 1+ 0 ]) u
         v' = clampᵣ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
                (rat [ pos (suc n) / 1+ 0 ]) v

         opaque
          unfolding _+ᵣ_
          bil-clamp : absᵣ (u +ᵣ -ᵣ v) ≤ᵣ
                       fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
                       absᵣ (fst (fst (flₙ n)) u +ᵣ -ᵣ fst (fst (flₙ n)) v)
          bil-clamp =
            subst2 {x = u'} {z = v'} (λ u v → absᵣ (u +ᵣ -ᵣ v) ≤ᵣ
               fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
               absᵣ (fst (fst (flₙ n)) u +ᵣ -ᵣ fst (fst (flₙ n)) v))
               (sym (∈ℚintervalℙ→clampᵣ≡ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n)))
                   u ((fst u∈) , snd u∈)))
               (sym (∈ℚintervalℙ→clampᵣ≡ (rat (ℚ.- fromNat (suc n))) (rat (fromNat (suc n)))
                   v (fst v∈ , snd v∈)))
               (≤Cont₂ {λ u v →
                         absᵣ (clampᵣ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
                 (rat [ pos (suc n) / 1+ 0 ]) u -ᵣ
                           clampᵣ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
                 (rat [ pos (suc n) / 1+ 0 ]) v)}
                       {λ u v →
                         fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
                       absᵣ (fst (fst (flₙ n)) (clampᵣ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
                 (rat [ pos (suc n) / 1+ 0 ]) u)
                          -ᵣ fst (fst (flₙ n)) (clampᵣ (rat (ℚ.- [ pos (suc n) / 1+ 0 ]))
                 (rat [ pos (suc n) / 1+ 0 ]) v))}
                  (cont∘₂ IsContinuousAbsᵣ
                      (cont₂∘ (contNE₂ sumR)
                        (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n)) )
                        (IsContinuous∘ _ _ IsContinuous-ᵣ
                           (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))))
                  (cont∘₂ (IsContinuous·ᵣL _)
                     (cont∘₂ IsContinuousAbsᵣ
                        (cont₂∘ (contNE₂ sumR)
                            (IsContinuous∘ _ _
                              (snd (flₙ n))
                             (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))
                            (IsContinuous∘ _ _ IsContinuous-ᵣ
                              (IsContinuous∘ _ _
                              (snd (flₙ n))
                             (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))))))
                    (λ u v →
                        subst2 _≤ᵣ_
                            (sym (absᵣ-rat _) ∙ cong absᵣ (sym (-ᵣ-rat₂ _ _)))
                            (cong₂ (λ fu fv → rat (fst (K n)) ·ᵣ
                              absᵣ (fu -ᵣ fv))
                               (cong f (∈ℚintervalℙ→clam≡ _ _ _
                                (clam∈ℚintervalℙ _ _ (ℚ.neg≤pos _ _) _))
                                ∙ cong {x =
                                rat (ℚ.clamp ((ℚ.- [ pos (suc n) / 1+ 0 ]))
                                     ([ pos (suc n) / 1+ 0 ]) u) }
                                       (fst (fst (flₙ n))) refl)
                               (cong f (∈ℚintervalℙ→clam≡ _ _ _
                                (clam∈ℚintervalℙ _ _ (ℚ.neg≤pos _ _) _))
                                 ∙ cong {x =
                                rat (ℚ.clamp ((ℚ.- [ pos (suc n) / 1+ 0 ]))
                                     ([ pos (suc n) / 1+ 0 ]) v) }
                                       (fst (fst (flₙ n))) refl))
                           (ibl n
                           (ℚ.clamp ((ℚ.- [ pos (suc n) / 1+ 0 ]))
                               ([ pos (suc n) / 1+ 0 ]) (v))
                           (ℚ.clamp ((ℚ.- [ pos (suc n) / 1+ 0 ]))
                               ([ pos (suc n) / 1+ 0 ]) (u))
                               (ℚ.absFrom≤×≤ _ _ (ℚ.≤clamp _ _ _ (ℚ.neg≤pos _ _))
                                  (ℚ.clamp≤ (ℚ.- [ pos (suc n) / 1+ 0 ]) _ _))
                               (ℚ.absFrom≤×≤ _ _ (ℚ.≤clamp _ _ _ (ℚ.neg≤pos _ _))
                                  (ℚ.clamp≤ (ℚ.- [ pos (suc n) / 1+ 0 ]) _ _))) )
                    u v)


boundedLipsch-coh : (f : ℚ → ℝ) (B B' : ℕ → ℚ₊)
    (bl : boundedLipschitz f B)
    (bl' : boundedLipschitz f B')
    → ∀ x →  BoundedLipsch.𝒇 f B bl x
           ≡ BoundedLipsch.𝒇 f B' bl' x
boundedLipsch-coh f B B' bl bl' =
                  ≡Continuous _ _
                   (BoundedLipsch.𝒇-cont f B bl)
                   (BoundedLipsch.𝒇-cont f B' bl')
                    λ r →
                      BoundedLipsch.𝒇-rat f B bl r ∙
                        sym (BoundedLipsch.𝒇-rat f B' bl' r)


_₊^ⁿ_ : ℝ₊ → ℕ → ℝ₊
(x , 0<x) ₊^ⁿ n  = (x ^ⁿ n) , 0<x^ⁿ x n 0<x


IsContinuous₊^ⁿ : ∀ n → IsContinuousWithPred
         (λ x → _ , isProp<ᵣ _ _)
         λ x 0<x →  fst ((x , 0<x) ₊^ⁿ n)
IsContinuous₊^ⁿ zero = AsContinuousWithPred _ _
 (IsContinuousConst 1)
IsContinuous₊^ⁿ (suc n) =
 cont₂·ᵣWP _ _ _
   (IsContinuous₊^ⁿ n) (AsContinuousWithPred _ _
  (IsContinuousId))


^ℕ-+ : ∀ x a b → ((x ₊^ⁿ a) ₊·ᵣ (x ₊^ⁿ b)) ≡ (x ₊^ⁿ (a ℕ.+ b))
^ℕ-+ x zero b = ℝ₊≡ (·IdL _)
^ℕ-+ x (suc a) b =
   ℝ₊≡ ((sym $ ·ᵣAssoc _ _ _)
        ∙∙ cong (fst (x ₊^ⁿ a) ·ᵣ_) (·ᵣComm _ _)
        ∙∙ ·ᵣAssoc _ _ _)
  ∙ cong (_₊·ᵣ x) (^ℕ-+ x a b)

_^ℤ_ : ℝ₊ → ℤ → ℝ₊
x ^ℤ pos n = x ₊^ⁿ n
x ^ℤ ℤ.negsuc n = invℝ₊ (x ₊^ⁿ (suc n))


_ℚ^ℤ_ : ℚ₊ → ℤ → ℚ₊
x ℚ^ℤ pos n = _ , ℚ.0<ℚ^ⁿ (fst x) (snd x) n
x ℚ^ℤ ℤ.negsuc n = invℚ₊ (_ , ℚ.0<ℚ^ⁿ (fst x) (snd x) (suc n))




^ℤ-rat : ∀ q n → ((ℚ₊→ℝ₊ q) ^ℤ n) ≡ ℚ₊→ℝ₊ (q ℚ^ℤ n)
^ℤ-rat q (pos n) = ℝ₊≡ (^ⁿ-ℚ^ⁿ _ _)
^ℤ-rat q (ℤ.negsuc n) =
  ℝ₊≡ (  fst (ℚ₊→ℝ₊ q ^ℤ ℤ.negsuc n)
      ≡⟨ cong (fst ∘ invℝ₊) (ℝ₊≡ (^ⁿ-ℚ^ⁿ _ _)) ⟩
         fst (invℝ₊ (ℚ₊→ℝ₊ (_ , ℚ.0<ℚ^ⁿ (fst q) (snd q) (suc n))))
      ≡⟨ invℝ'-rat _ _
        (snd ((ℚ₊→ℝ₊ ((q .fst ℚ^ⁿ suc n) ,
          ℚ.0<ℚ^ⁿ (fst q) (snd q) (suc n))))) ⟩ _
      ∎)

^ℤ-ℚApproxℙ'' : ∀ n → ℚApproxℙ''
      (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , isProp<ᵣ _ _)
      (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , isProp<ᵣ _ _)
      (curry (λ p → ((p .fst , p .snd) ^ℤ n)))
^ℤ-ℚApproxℙ'' n x x∈P ε =
  fst (q₊ ℚ^ℤ n) , snd (ℚ₊→ℝ₊ (q₊ ℚ^ℤ n)) ,
    ≡→∼ (cong fst (sym (^ℤ-rat q₊ n)) ∙
         cong (curry (λ p → (p ^ℤ n) .fst) (rat x))
             (isProp<ᵣ _ _ _ _))

 where
  q₊ = (x , ℚ.<→0< _ (<ᵣ→<ℚ _ _ x∈P))

IsContinuous^ℤ : ∀ n → IsContinuousWithPred
         (λ x → _ , isProp<ᵣ _ _)
         λ x 0<x →  fst ((x , 0<x) ^ℤ n)
IsContinuous^ℤ (pos n) = IsContinuous₊^ⁿ n
IsContinuous^ℤ (ℤ.negsuc n) =
 IsContinuousWP∘ _ _ _ _
   _ (snd invℝ') (IsContinuous₊^ⁿ (suc n))


-- TODO : more direct!! (invℝ₊ is more basic than invℝ)

₊^ⁿ-invℝ₊ : ∀ n x  →
            ((invℝ₊ x) ₊^ⁿ n) ≡ (invℝ₊ (x ₊^ⁿ n))
₊^ⁿ-invℝ₊ n x =
    ℝ₊≡ (cong (_^ⁿ n) (invℝ₊≡invℝ _ (inl (snd x))) ∙∙
       ^ⁿ-invℝ _ _ _ _
       ∙∙ sym (invℝ₊≡invℝ _ (inl (snd (x ₊^ⁿ n)))) )

1₊^ⁿ≡1 : ∀ k → 1 ₊^ⁿ k ≡ 1
1₊^ⁿ≡1 zero = refl
1₊^ⁿ≡1 (suc k) = ℝ₊≡ (·IdR _) ∙ 1₊^ⁿ≡1 k

1^ℤ≡1 : ∀ k → 1 ^ℤ k ≡ 1
1^ℤ≡1 (pos n) = 1₊^ⁿ≡1 n
1^ℤ≡1 (ℤ.negsuc n) =
     cong invℝ₊ (1₊^ⁿ≡1 (suc n))
   ∙ invℝ₊1


pos+negsuc : ∀ a b → pos a ℤ.+ ℤ.negsuc b ≡ pos (suc a) ℤ.+ ℤ.negsuc (suc b)
pos+negsuc a b = ℤ.+Comm _ _ ∙∙
   cong (ℤ.negsuc b ℤ.+_) (ℤ.+Comm _ _)
     ∙ ℤ.+Assoc (ℤ.negsuc b) (ℤ.negsuc 0) _ ∙∙ ℤ.+Comm _ _

^ℤ-minus : ∀ x a b → ((x ^ℤ (pos a)) ₊·ᵣ (x ^ℤ (ℤ.negsuc b)))
                   ≡ (x ^ℤ ((pos a) ℤ.+ (ℤ.negsuc b)))
^ℤ-minus x zero b =
    ℝ₊≡ (·IdL _)
  ∙ cong (x ^ℤ_) (ℤ.pos0+ _)
^ℤ-minus x (suc a) zero =
  ℝ₊≡ (sym (·ᵣAssoc _ _ _) ∙
    cong (fst (x ₊^ⁿ a) ·ᵣ_) (
       cong (fst x ·ᵣ_) (cong (fst ∘ invℝ₊) (ℝ₊≡ (·IdL _)))
      ∙ x·invℝ₊[x] x)  ∙ ·IdR _ )
^ℤ-minus x (suc a) (suc b) =
  let z = ^ℤ-minus x a b
  in ℝ₊≡ (sym (·ᵣAssoc _ _ _) ∙
       cong ((x .fst ^ⁿ a) ·ᵣ_)
         (  ·ᵣComm _ _
        ∙∙  cong (_·ᵣ x .fst) (cong fst (invℝ₊· (x ₊^ⁿ (suc b)) x))
            ∙ sym (·ᵣAssoc _ _ _)
            ∙ cong (invℝ₊ (x ₊^ⁿ suc b) .fst ·ᵣ_)
                (·ᵣComm _ _ ∙ x·invℝ₊[x] x )
        ∙∙ ·IdR _))
       ∙∙ z ∙∙
     cong (x ^ℤ_) (pos+negsuc a b)

^ℤ-+ : ∀ x a b → ((x ^ℤ a) ₊·ᵣ (x ^ℤ b)) ≡ (x ^ℤ (a ℤ.+ b))
^ℤ-+ x (pos n) (pos n₁) = ^ℕ-+ x n n₁ ∙ cong (x ^ℤ_) (ℤ.pos+ _ _)
^ℤ-+ x (pos n) (ℤ.negsuc n₁) = ^ℤ-minus x n n₁
^ℤ-+ x (ℤ.negsuc n) (pos n₁) =
  ℝ₊≡ (·ᵣComm _ _)
  ∙∙ ^ℤ-minus x n₁ n ∙∙
  cong (x ^ℤ_) (ℤ.+Comm _ _)
^ℤ-+ x (ℤ.negsuc n) (ℤ.negsuc n₁) =
      sym (invℝ₊· _ _)
   ∙∙ cong invℝ₊ (^ℕ-+ x (suc n) (suc n₁))
   ∙∙ cong (x ^ℤ_) (ℤ.negsuc+ n (suc n₁))


^ℕ-· : ∀ x a b → ((x ₊^ⁿ a) ₊^ⁿ b) ≡ (x ₊^ⁿ (a ℕ.· b))
^ℕ-· x a zero = cong (x ₊^ⁿ_) (ℕ.0≡m·0 a)
^ℕ-· x a (suc b) = cong (_₊·ᵣ (x ₊^ⁿ a)) (^ℕ-· x a b)
  ∙ ^ℤ-+ x (pos (a ℕ.· b)) (pos a) ∙
   cong {y = pos ((a ℕ.· suc b))} (x ^ℤ_)
    (sym (ℤ.pos+ _ _) ∙ cong pos
      ((cong (ℕ._+ a) (ℕ.·-comm _ _) ∙ ℕ.+-comm _ _) ∙ ℕ.·-comm (suc b) a))


pow-root-+ℕ₊₁ : ∀ (m n : ℕ₊₁) →
         nth-pow-root-iso (m ·₊₁ n)
             ≡ compIso (nth-pow-root-iso m) (nth-pow-root-iso n)
pow-root-+ℕ₊₁ (1+ m) (1+ n) = SetsIso≡fun isSetℝ₊ isSetℝ₊
  (funExt (λ x → sym (^ℕ-· x (suc m) (suc n))))


ₙ√1 : ∀ b → root b 1 ≡ 1
ₙ√1 b = cong (root b) (sym (1₊^ⁿ≡1 _)) ∙ Iso.leftInv (nth-pow-root-iso b) 1



ₙ√-StrictMonotone : ∀ {x y : ℝ₊} (b : ℕ₊₁)
      → fst x <ᵣ fst y → fst (root b x) <ᵣ fst (root b y)
ₙ√-StrictMonotone x@{_ , 0<x} y@{_ , 0<y} (1+ b) x<y =
  ^ⁿStrictMonotone⁻¹  (suc b) (ℕ.suc-≤-suc  ℕ.zero-≤)
    (snd (root (1+ b) (_ , 0<x)))
    (snd (root (1+ b) (_ , 0<y)))
    (subst2 _<ᵣ_
      (cong fst $ sym (Iso.rightInv (nth-pow-root-iso (1+ b)) x))
      (cong fst $ sym (Iso.rightInv (nth-pow-root-iso (1+ b)) y))
      x<y)


ₙ√-Monotone : ∀ {x y : ℝ₊} (b : ℕ₊₁)
      → fst x ≤ᵣ fst y → fst (root b x) ≤ᵣ fst (root b y)
ₙ√-Monotone x@{_ , 0<x} y@{_ , 0<y} (1+ b) x≤y =
  ^ⁿMonotone⁻¹  (suc b) (ℕ.suc-≤-suc  ℕ.zero-≤)
    (snd (root (1+ b) (_ , 0<x)))
    (snd (root (1+ b) (_ , 0<y)))
    (subst2 _≤ᵣ_
      (cong fst $ sym (Iso.rightInv (nth-pow-root-iso (1+ b)) x))
      (cong fst $ sym (Iso.rightInv (nth-pow-root-iso (1+ b)) y))
      x≤y)



uContRoot0 : ∀ n → ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ (u : ℝ₊) → fst u <ᵣ rat (fst δ)
         → (fst (root n u)) <ᵣ rat (fst ε))
uContRoot0 (1+ n) ε =
    (ε ℚ₊^ⁿ (suc n))
  , λ u u<εⁿ →
    isTrans<≡ᵣ _ _ _ (ₙ√-StrictMonotone
          {y = ℚ₊→ℝ₊ (ε ℚ₊^ⁿ (suc n))} (1+ n) u<εⁿ)
         (cong (fst ∘ root (1+ n)) (
            ℝ₊≡ (sym (^ⁿ-ℚ^ⁿ _ _)))
          ∙ cong fst (Iso.leftInv (nth-pow-root-iso (1+ n)) (ℚ₊→ℝ₊ ε)))


·DistRoot : ∀ x y b → root b x ₊·ᵣ root b y ≡ root b (x ₊·ᵣ y)
·DistRoot x y b =
   sym (Iso.leftInv (nth-pow-root-iso b) _) ∙ cong (root b)
     (ℝ₊≡ (^ⁿDist·ᵣ _ _ _)
      ∙ cong₂ _₊·ᵣ_
       (Iso.rightInv (nth-pow-root-iso b) x)
       (Iso.rightInv (nth-pow-root-iso b) y))

invCommRoot : ∀ x b → invℝ₊ (root b x) ≡ root b (invℝ₊ x)
invCommRoot x b =
  isoFunInjective (nth-pow-root-iso b) _ _
   (₊^ⁿ-invℝ₊ _ _
     ∙ cong invℝ₊ (Iso.rightInv (nth-pow-root-iso b) _)
     ∙ sym (Iso.rightInv (nth-pow-root-iso b) _))

pow-root-comm₊ : ∀ x a b → (root b x) ₊^ⁿ a ≡ root b (x ₊^ⁿ a)
pow-root-comm₊ x zero b = sym (ₙ√1 b)
pow-root-comm₊ x (suc a) b =
    cong (_₊·ᵣ (root b x)) (pow-root-comm₊ x a b)
  ∙ ·DistRoot _ _ _


pow-root-comm : ∀ x a b → (root b x) ^ℤ a ≡ root b (x ^ℤ a)
pow-root-comm x (pos n) b = pow-root-comm₊ x n b
pow-root-comm x (ℤ.negsuc n) b =
   cong invℝ₊ (pow-root-comm₊ x (suc n) b) ∙
     invCommRoot _ _



ℝ₊→ℝ₀₊ : ℝ₊ → ℝ₀₊
ℝ₊→ℝ₀₊ (x , y) = x , <ᵣWeaken≤ᵣ _ _ y



a/[a+c]<b/[b+c] : ∀ (a b c : ℝ₊) → fst a <ᵣ fst b →
    fst (a ₊·ᵣ invℝ₊ (a ₊+ᵣ c)) <ᵣ fst (b ₊·ᵣ invℝ₊ (b ₊+ᵣ c))
a/[a+c]<b/[b+c] a b c a<b =
  invEq (z/y'<x/y≃y₊·z<y'₊·x _ _ _ _)
   (subst2 _<ᵣ_
     (cong (_+ᵣ fst c ·ᵣ fst a) (·ᵣComm _ _) ∙ sym (·DistR+ _ _ _))
      (sym (·DistR+ _ _ _))
     (<ᵣ-o+ _ _ _ (<ᵣ-o·ᵣ _ _ c a<b) ))



_₀₊+ᵣ_ : ℝ₊ → ℝ₀₊ → ℝ₊
(x , 0<x) ₀₊+ᵣ (y , 0≤y) = x +ᵣ y ,
 (isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) $ <≤ᵣMonotone+ᵣ _ _ _ _ 0<x 0≤y)



opaque
 unfolding _<ᵣ_
 x<δ→x≤0 : ∀ x → ((ε : ℚ₊) → x <ᵣ (rat (fst ε))) → x ≤ᵣ 0
 x<δ→x≤0 x p = eqℝ _ _
   λ ε → invEq (∼≃abs<ε _ _ _)
     (isTrans≡<ᵣ _ _ _
         (cong absᵣ (+IdR _ ∙ maxᵣComm _ _)
           ∙ (absᵣNonNeg _ (≤maxᵣ 0 x)) ∙ maxᵣComm _ _) (p' ε))
   where
   p' : (ε : ℚ₊) → maxᵣ x 0 <ᵣ (rat (fst ε))
   p' ε = max<-lem _ _ _  (p ε) (snd (ℚ₊→ℝ₊ ε))

opaque
 unfolding _<ᵣ_
 x<y+δ→x≤y : ∀ x y → ((ε : ℚ₊) → x <ᵣ y +ᵣ (rat (fst ε))) → x ≤ᵣ y
 x<y+δ→x≤y x y p = invEq (x≤y≃0≤y-x _ _)
  ( isTrans≤≡ᵣ _ _ _
    (-ᵣ≤ᵣ _ 0 (x<δ→x≤0 _ (a<c+b⇒a-c<b _ _ _ ∘ p)))
    (-[x-y]≡y-x _ _))

-- lim√→₀ : ∀ n → (ε : ℚ₊) →
--            ∃[ δ ∈ ℚ₊ ] (∀ x →
--                fst x <ᵣ rat (fst δ) → fst (root n x) <ᵣ rat (fst ε))
-- lim√→₀ = {!!}


module slope-incr-root (n : ℕ) where


 help-fn : (a c : ℝ₊) → ℝ
 help-fn a c =
   fst (root (1+ (suc n)) (a ₊+ᵣ c)) -ᵣ fst (root (1+ (suc n)) a)

 help-fn-decr : ∀ c a b → fst a <ᵣ fst b
                 →  help-fn b c <ᵣ help-fn a c
 help-fn-decr c a b a<b =
      subst2 _<ᵣ_
        (cong (fst c ·ᵣ_) (invℝ₊≡invℝ _ _) ∙ sym (H.h b))
         (cong (fst c ·ᵣ_) (invℝ₊≡invℝ _ _) ∙ sym (H.h a))
        (invEq (z/y'<x/y≃y₊·z<y'₊·x (fst c) (fst c)
           (H.fac.S₊ a) (H.fac.S₊ b ))
          (<ᵣ-·ᵣo _ _ c (Seq<→Σ<
            (geometricProgression _ (H.fac.r a))
            (geometricProgression _ (H.fac.r b))
            (suc n) (λ m m≤n →
              subst2 _<ᵣ_
                (sym (geometricProgressionClosed _ _ _))
                (sym (geometricProgressionClosed _ _ _))
                (<≤ᵣ₊Monotone·ᵣ
                  (ℝ₊→ℝ₀₊ ((root (2+ n) (a ₊+ᵣ c) ₊^ⁿ n)
                    ₊·ᵣ root (2+ n) (a ₊+ᵣ c) ))
                  _ ((H.fac.r a , H.fac.0<r a) ₊^ⁿ m) _

                     (^ⁿ-StrictMonotone (suc n)
                      (ℕ.suc-≤-suc ℕ.zero-≤)
                      ((<ᵣWeaken≤ᵣ _ _
                      $ snd (root (1+ (suc n)) (a ₊+ᵣ c))))
                       ((<ᵣWeaken≤ᵣ _ _
                      $ snd (root (1+ (suc n)) (b ₊+ᵣ c))))
                       (ₙ√-StrictMonotone _
                         (<ᵣ-+o _ _ (fst c) a<b)))
                     (^ⁿ-Monotone m
                      (<ᵣWeaken≤ᵣ _ _ (H.fac.0<r a))
                       (subst2 _≤ᵣ_
                         (sym (cong fst (·DistRoot _ _ _))
                            ∙ (cong (fst (root (1+ (suc n)) a) ·ᵣ_)
                              (cong fst (sym (invCommRoot _ _))
                               ∙ invℝ₊≡invℝ _ _ )))
                         (sym (cong fst (·DistRoot _ _ _))
                            ∙ (cong (fst (root (1+ (suc n)) b) ·ᵣ_)
                              (cong fst (sym (invCommRoot _ _))
                               ∙ invℝ₊≡invℝ _ _ )))
                         (ₙ√-Monotone _
                           (<ᵣWeaken≤ᵣ _ _
                             (a/[a+c]<b/[b+c] _ _ _ a<b))))))))))

  where
  open bⁿ-aⁿ n hiding (n)

  module H (a : ℝ₊) where
   module fac = factor
     (fst (root (1+ (suc n)) a)) (fst (root (1+ (suc n)) (a ₊+ᵣ c)))
     (snd (root (1+ (suc n)) a)) (snd (root (1+ (suc n)) (a ₊+ᵣ c)))

   h : fst (root (2+ n) (a ₊+ᵣ c)) -ᵣ fst (root (2+ n) a) ≡ (c .fst ／ᵣ[
                Sₙ (fst (root (2+ n) (a ₊+ᵣ c)) ^ⁿ suc n)
                (r (fst (root (2+ n) a)) (fst (root (2+ n) (a ₊+ᵣ c)))
                 (snd (root (2+ n) a)) (snd (root (2+ n) (a ₊+ᵣ c))))
                (bⁿ-aⁿ.n n)
                , _ ])
   h = x·y≡z→x≡z/y _ _ _ (inl fac.0<S) ((fac.[b-a]·S≡bⁿ-aⁿ

         ∙ cong₂ _-ᵣ_
         (cong fst
          (Iso.rightInv (nth-pow-root-iso (1+ (suc n))) (a ₊+ᵣ c)))
         (cong fst
          (Iso.rightInv (nth-pow-root-iso (1+ (suc n))) a))
           ∙ L𝐑.lem--063))


opaque
 unfolding -ᵣ_
 -ᵣWeaken<ᵣ : ∀ a b c → 0 ≤ᵣ b → a <ᵣ c  → a -ᵣ b <ᵣ c
 -ᵣWeaken<ᵣ a b c 0≤b a<c =
   isTrans<≡ᵣ _ _ _
     (<≤ᵣMonotone+ᵣ _ _ _ _ a<c (-ᵣ≤ᵣ _ _ 0≤b))
     (+IdR _)

opaque
 unfolding _+ᵣ_
 nth-root-slope-incr : ∀ n (x : ℚ₊) (Δ : ℚ₊)
    → fst (root (1+ n) ((ℚ₊→ℝ₊ x) ₊+ᵣ (ℚ₊→ℝ₊ Δ)))
       -ᵣ fst (root (1+ n) (ℚ₊→ℝ₊ x))
       ≤ᵣ fst (root (1+ n) (ℚ₊→ℝ₊ Δ))
 nth-root-slope-incr zero x Δ  = ≡ᵣWeaken≤ᵣ _ _ (-ᵣ-rat₂ _ _ ∙ cong rat lem--063)
 nth-root-slope-incr (suc n) x Δ =
    x<y+δ→x≤y _ _ h

  where

   h : ∀ (ε : ℚ₊) →
             fst (root (1+ (suc n)) ((ℚ₊→ℝ₊ x) ₊+ᵣ (ℚ₊→ℝ₊ Δ)))
       -ᵣ fst (root (1+ (suc n)) (ℚ₊→ℝ₊ x))
          <ᵣ (fst (NthRoot.nth-root n (ℚ₊→ℝ₊ Δ))) +ᵣ rat (fst ε)

   h ε = PT.rec
     (isProp<ᵣ _ _)
     (λ (δ , X)
        --(δ' , X')
       → let δ⊓x = (ℚ.min₊
                     x δ)
             ineq1 = (slope-incr-root.help-fn-decr
                 n (ℚ₊→ℝ₊ Δ) (ℚ₊→ℝ₊ (/2₊ δ⊓x)) _
                       (isTrans<≤ᵣ _ _ _
                         (<ℚ→<ᵣ _ _ (x/2<x δ⊓x))
                         (min≤ᵣ _ (rat (fst δ)))))

             ineq2 :
                fst (root (1+ (suc n)) ((ℚ₊→ℝ₊ (/2₊ δ⊓x)) ₊+ᵣ (ℚ₊→ℝ₊ Δ)))
                 -ᵣ fst (root (1+ (suc n)) (ℚ₊→ℝ₊ (/2₊ δ⊓x)))
                    <ᵣ
                 fst (root (1+ (suc n)) (ℚ₊→ℝ₊ Δ)) +ᵣ (rat (fst ε))
             ineq2 =
                -- isTrans<ᵣ _ _ _
                  -ᵣWeaken<ᵣ _ _ _
                     (<ᵣWeaken≤ᵣ _ _
                      (snd (root (1+ (suc n)) (ℚ₊→ℝ₊ (/2₊ δ⊓x)))))
                     (isTrans<≡ᵣ _ _ _
                       (a-b<c⇒a<c+b _ _ _
                         (isTrans≤<ᵣ _ _ _
                          (≤absᵣ _)
                          (fst (∼≃abs<ε _ _ _)
                            (sym∼ _ _ _
                              (X _ _
                                (subst (_∼[ δ ]
                                   (ℚ₊→ℝ₊ (/2₊ δ⊓x) .fst +ᵣ rat (fst Δ)))
                                 (+IdL _)
                                 (+ᵣ-∼ 0 (ℚ₊→ℝ₊ (/2₊ δ⊓x) .fst)
                                 (rat (fst Δ)) δ
                                    (invEq (∼≃abs<ε _ _ _)
                                      (isTrans≡<ᵣ _ _ _
                                        (minusComm-absᵣ _ _ ∙
                                         cong (absᵣ ∘ (ℚ₊→ℝ₊ (/2₊ δ⊓x) .fst +ᵣ_))
                                           (-ᵣ-rat 0) ∙ cong absᵣ (+IdR _)
                                         ∙ absᵣPos _ ((ℚ₊→ℝ₊ (/2₊ δ⊓x) .snd)))
                                        ((isTrans<≤ᵣ _ _ _
                         (<ℚ→<ᵣ _ _ (x/2<x δ⊓x))
                         (min≤ᵣ' (rat (fst x)) _)))))))))) ))
                       (+ᵣComm _ _))

         in isTrans<ᵣ _ _ _
              ineq1
                 ineq2
       )
      (IsContinuousRoot (2+ n) (rat (fst Δ))
        ε (snd (ℚ₊→ℝ₊ Δ)))




 uContRootℚ : ∀ n → IsUContinuousℚℙ (λ x → (0 <ᵣ x) , isProp<ᵣ _ _ )
                    (curry (fst ∘ root n) ∘ rat)
 uContRootℚ (1+ n) ε =
   (ε ℚ₊^ⁿ (suc n)) ,
     ℚ.elimBy≡⊎<'
      (λ x y X u∈ v∈ →
        sym∼ _ _ _ ∘ X v∈ u∈ ∘ (subst (ℚ._< fst (ε ℚ₊^ⁿ suc n))
           (ℚ.absComm- _ _)))
      (λ x u∈ v∈ _ → subst (_ ∼[ _ ]_)
         (cong (fst ∘ (root (1+ n))) (ℝ₊≡ refl)) (refl∼ _ _))
      λ x Δ u∈ v∈ X →
        sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
         (isTrans≡<ᵣ _ _ _ (absᵣPos _
           (fst (x<y≃0<y-x _ _)
             (ₙ√-StrictMonotone (1+ n)
               (isTrans≡<ᵣ _ _ _
                 (sym (+IdR _)) (<ᵣ-o+ _ _ (rat x) (snd (ℚ₊→ℝ₊ Δ)))))))
          let X' = isTrans<≡ᵣ _ _ _
               (ₙ√-StrictMonotone {ℚ₊→ℝ₊ Δ} {ℚ₊→ℝ₊ (ε ℚ₊^ⁿ suc n)} (1+ n)
               ((<ℚ→<ᵣ _ _ (subst (ℚ._< fst (ε ℚ₊^ⁿ suc n))
                   (ℚ.absComm- _ _ ∙ cong ℚ.abs
                     lem--063 ∙ (ℚ.absPos _ (ℚ.0<ℚ₊ Δ))) X))))
                     (cong (fst ∘ (root (1+ n)))
                        (ℝ₊≡
                          (sym (^ⁿ-ℚ^ⁿ _ _)))
                       ∙ cong fst (Iso.leftInv (nth-pow-root-iso (1+ n))
                         (ℚ₊→ℝ₊ ε)))
          in isTrans≤<ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                 (cong₂ (λ v∈ u∈ →
                    fst (root (1+ n) (rat (x ℚ.+ Δ .fst) , v∈)) -ᵣ
                     fst (root (1+ n) (rat x , u∈)))
                      (isProp<ᵣ _ _ _ _) (isProp<ᵣ _ _ _ _))
                  (nth-root-slope-incr _
                    (x , (ℚ.<→0< _ (<ᵣ→<ℚ _ _ u∈))) _) )
              X'))

uContRoot : ∀ n → IsUContinuousℙ (λ x → (0 <ᵣ x) , isProp<ᵣ _ _ )
                   (curry (fst ∘ root n))
uContRoot n = IsUContinuousℚℙ→IsUContinuousℙ _
  (λ _ _ _ _ → ₙ√-Monotone n)
  (uContRootℚ n)


^ℤ-· : ∀ x a b → ((x ^ℤ a) ^ℤ b) ≡  (x ^ℤ (a ℤ.· b))
^ℤ-· x (pos n) (pos n₁) = ^ℕ-· x n n₁ ∙ cong (x ^ℤ_) (ℤ.pos·pos _ _)
^ℤ-· x (pos zero) (ℤ.negsuc n₁) = 1^ℤ≡1 _
^ℤ-· x (pos (suc n)) (ℤ.negsuc n₁) =
     cong invℝ₊ (^ℕ-· x (suc n) (suc n₁))
   ∙ cong (x ^ℤ_) (cong ℤ.-_ (ℤ.pos·pos _ _ ) ∙ sym (ℤ.pos·negsuc _ _))
^ℤ-· x (ℤ.negsuc n) (pos zero) =
  cong {x = 0} (x ^ℤ_) (sym (ℤ.·AnnihilR _))
^ℤ-· x (ℤ.negsuc n) (pos (suc n₁)) =
      ₊^ⁿ-invℝ₊ _ _
   ∙∙ cong invℝ₊ (^ℕ-· x (suc n) (suc n₁))
   ∙∙ cong (x ^ℤ_)
     ( cong ℤ.-_ ((ℤ.pos·pos (suc n) (suc n₁) )) ∙ sym (ℤ.negsuc·pos n (suc n₁)) )

^ℤ-· x (ℤ.negsuc n) (ℤ.negsuc n₁) =
        (sym (₊^ⁿ-invℝ₊ _ _)
       ∙ cong (_₊^ⁿ (suc n₁)) (invℝ₊Invol _))
   ∙∙ ^ℕ-· x (suc n) (suc n₁)
   ∙∙ cong (x ^ℤ_) (ℤ.pos·pos _ _ ∙ (sym $ ℤ.negsuc·negsuc n n₁))



pre^ℚ-aprox : ∀ a b → ℚApproxℙ'' (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                                 (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
                    λ x 0<x → (root b ((x , 0<x) ^ℤ a))
pre^ℚ-aprox a b =
  ℚApproxℙ∘ (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
            (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
            (λ x → (0 <ᵣ x) , isProp<ᵣ _ _)
     (curry (root b))
      (curry ((_^ℤ a)))
       (uContRoot _)
      (ℚApproxℙ'→ℚApproxℙ'' _ _ (curry (root b)) (ℚApproxℙ-root b))
      (^ℤ-ℚApproxℙ'' a)

module _ (x : ℝ) (0<x : 0 <ᵣ x) where
 ^ℚ-coh' : ∀ a a' b b' → pos a ℤ.· pos (suc b') ≡ pos a' ℤ.· pos (suc b) →
   (root (1+ b) (x , 0<x)  ^ℤ (pos a)) ≡ (root (1+ b') (x , 0<x) ^ℤ (pos a'))
 ^ℚ-coh' n n' b b' p  =
     let z = cong₂ (_^ℤ_)
               (sym ((cong Iso.inv (pow-root-+ℕ₊₁ (1+ b') (1+ b))) ≡$ (x , 0<x))
               ∙∙ cong (flip root (x , 0<x) )
                 (·₊₁-comm _ _ )
               ∙∙ (((cong Iso.inv (pow-root-+ℕ₊₁ (1+ b) (1+ b'))) ≡$ (x , 0<x))))
                (ℤ.·Comm _ _ ∙∙ p ∙∙ ℤ.·Comm _ _)
    in (sym (cong (_₊^ⁿ n)
            (Iso.rightInv (nth-pow-root-iso (1+ b')) (root (1+ b) (x , 0<x))))
        ∙ (^ℤ-· _ (pos (suc b')) (pos n)) )
      ∙∙ z ∙∙
       ( sym (^ℤ-· _ (pos (suc b)) (pos n'))
         ∙ cong (_₊^ⁿ n')
            (Iso.rightInv (nth-pow-root-iso (1+ b)) (root (1+ b') (x , 0<x))))

 ^ℚ-coh : ∀ a a' b b' → a ℤ.· pos (suc b') ≡ a' ℤ.· pos (suc b) →
   (root (1+ b) (x , 0<x)  ^ℤ a) ≡ (root (1+ b') (x , 0<x) ^ℤ a')
 ^ℚ-coh (pos n) (pos n₁) b b' p = ^ℚ-coh' n n₁ b b' p

 ^ℚ-coh (pos n) (ℤ.negsuc n₁) b b' p =
   ⊥.rec (ℤ.posNotnegsuc _ _
    (ℤ.pos·pos _ _ ∙∙ p ∙∙ (ℤ.negsuc·pos n₁ (suc b) ∙
      cong (ℤ.-_) (sym (ℤ.pos·pos _ _)) )))
 ^ℚ-coh (ℤ.negsuc n) (pos n₁) b b' p =
   ⊥.rec (ℤ.negsucNotpos _ _
    ((cong (ℤ.-_) (ℤ.pos·pos _ _) ∙
       sym (ℤ.negsuc·pos n (suc b'))) ∙∙ p ∙∙ ((sym (ℤ.pos·pos _ _)) )))
 ^ℚ-coh (ℤ.negsuc n) (ℤ.negsuc n₁) b b' p =
   cong invℝ₊ (^ℚ-coh' (suc n) (suc n₁) b b' (
     sym (ℤ.-DistL· (ℤ.negsuc n) (pos (suc b')))
      ∙∙ cong ℤ.-_ p ∙∙
      ℤ.-DistL· (ℤ.negsuc n₁) (pos (suc b))))

 _^ℚc_ : ℚ → ℝ₊
 _^ℚc_ = SQ.Elim.go w
  where
  w : Elim (λ _ → ℝ₊)
  w .Elim.isSetB _ = isSetℝ₊
  w .Elim.f (a , b) = (root b (x , 0<x)) ^ℤ a
  w .Elim.f∼ (a , (1+ b)) (a' , (1+ b')) r =
    ^ℚ-coh a a' b b' r

_^ℚ_ : ℝ₊ → ℚ →  ℝ₊
_^ℚ_ = uncurry _^ℚc_

IsContinuous^ℚ : ∀ q → IsContinuousWithPred (λ _ → _ , isProp<ᵣ _ _)
                          (curry (fst ∘ (_^ℚ q)))
IsContinuous^ℚ = SQ.ElimProp.go w
  where
  P = _
  w : ElimProp _
  w .ElimProp.isPropB _ = isPropΠ3 λ _ _ _ → squash₁
  w .ElimProp.f (a , b) =
    IsContinuousWP∘ P P (curry (fst ∘ _^ℤ a)) (curry (fst ∘ root b))
      (curry (snd ∘ root b))
      (IsContinuous^ℤ a)
      (IsContinuousRoot b)

^ℚ-+ : ∀ x a b → ((x ^ℚ a) ₊·ᵣ (x ^ℚ b)) ≡ (x ^ℚ (a ℚ.+ b))
^ℚ-+ x₊@(x , 0<x) = SQ.ElimProp2.go w
 where
 w : ElimProp2 (λ z z₁ → ((x₊ ^ℚ z) ₊·ᵣ (x₊ ^ℚ z₁)) ≡ (x₊ ^ℚ (z ℚ.+ z₁)))
 w .ElimProp2.isPropB _ _ = isSetℝ₊ _ _
 w .ElimProp2.f (a , 1+ b) (a' , 1+ b') =
  ((root (1+ b) (x , 0<x) ^ℤ a) ₊·ᵣ (root (1+ b') (x , 0<x) ^ℤ a'))
   ≡⟨ cong₂ _₊·ᵣ_
        (cong (_^ℤ a) b√x≡ ∙ ^ℤ-· bb'√x _ _)
        (cong (_^ℤ a') b'√x≡ ∙ ^ℤ-· bb'√x _ _) ⟩
            ((bb'√x ^ℤ (ℚ.ℕ₊₁→ℤ (1+ b') ℤ.· a))
         ₊·ᵣ (bb'√x ^ℤ (ℚ.ℕ₊₁→ℤ (1+ b) ℤ.· a')))
   ≡⟨ (λ i → ^ℤ-+ bb'√x
       (ℤ.·Comm (pos (suc b')) a i)
       (ℤ.·Comm (pos (suc b)) a' i)
       i) ⟩
   ((bb'√x ^ℤ
      (a ℤ.· ℚ.ℕ₊₁→ℤ (1+ b') ℤ.+ a' ℤ.· ℚ.ℕ₊₁→ℤ (1+ b)))) ∎

  where
   bb'√x = root ((1+ b) ·₊₁ (1+ b')) (x , 0<x)

   b√x≡ = sym (Iso.rightInv (nth-pow-root-iso (1+ b')) _) ∙
      (cong (_₊^ⁿ (suc b')) $ sym (cong Iso.inv (pow-root-+ℕ₊₁ (1+ b') (1+ b)) ≡$ x₊)
        ∙ cong (flip root x₊) (·₊₁-comm _ _))

   b'√x≡ = sym (Iso.rightInv (nth-pow-root-iso (1+ b)) _) ∙
      (cong (_₊^ⁿ (suc b)) $ sym (cong Iso.inv (pow-root-+ℕ₊₁ (1+ b) (1+ b')) ≡$ x₊))


^ℚ-· : ∀ x a b → ((x ^ℚ a) ^ℚ b) ≡ (x ^ℚ (a ℚ.· b))
^ℚ-· x₊@(x , 0<x) = SQ.ElimProp2.go w
 where
 w : ElimProp2 _
 w .ElimProp2.isPropB _ _ = isSetℝ₊ _ _
 w .ElimProp2.f (a , 1+ b) (a' , 1+ b') =
     cong (_^ℤ a')
       (sym (pow-root-comm _ _ _) ∙ cong (_^ℤ a) (
             sym (cong Iso.inv (pow-root-+ℕ₊₁ (1+ b') (1+ b)) ≡$ x₊)
          ∙ cong (flip root x₊) (·₊₁-comm _ _)))
       ∙ ^ℤ-· _ _ _



-- ^ⁿ-invℝ₊ : ∀ n x →
--             ((invℝ₊ x) ₊^ⁿ n) ≡ invℝ₊ (x ₊^ⁿ n)
-- ^ⁿ-invℝ₊ n = {!!}
-- uncurry
--   λ x 0<x →
--      ℝ₊≡ (≡ContinuousWithPred _ _ (openPred< 0) (openPred< 0)
--         _ _
--          (IsContinuousWP∘
--            (λ y → (0 <ᵣ y) , squash₁)
--            (λ y → (0 <ᵣ y) , squash₁)
--            _ _
--            (λ x 0<x → invℝ'-pos x 0<x) (IsContinuous₊^ⁿ n) (snd invℝ'))

--     (IsContinuousWP∘
--            (λ y → (0 <ᵣ y) , squash₁)
--            (λ y → (0 <ᵣ y) , squash₁)
--            _ _
--            (λ x 0<x → snd ((x , 0<x) ₊^ⁿ n)) (snd invℝ') (IsContinuous₊^ⁿ n) )
--     (λ r r<0 _ → {!!}) x 0<x 0<x)


invℝ₊^ℤ : ∀ x a → (invℝ₊ x) ^ℤ (ℤ.- a) ≡ x ^ℤ a
invℝ₊^ℤ x (pos zero) = refl
invℝ₊^ℤ x (pos (suc n)) = cong invℝ₊ (₊^ⁿ-invℝ₊ (suc n) x)
 ∙ invℝ₊Invol _
invℝ₊^ℤ x (ℤ.negsuc n) = ₊^ⁿ-invℝ₊ _ _

invℝ₊[^ℤ] : ∀ x a → (invℝ₊ x ^ℤ a) ≡ invℝ₊ (x ^ℤ a)
invℝ₊[^ℤ] x (pos zero) = ℝ₊≡ (sym (invℝ₊-rat 1))
invℝ₊[^ℤ] x (pos (suc n)) = ₊^ⁿ-invℝ₊ _ _
invℝ₊[^ℤ] x (ℤ.negsuc n) = cong invℝ₊ (₊^ⁿ-invℝ₊ _ _)

invℝ₊^ℤ' : ∀ x a → (invℝ₊ x) ^ℤ a ≡ x ^ℤ (ℤ.- a)
invℝ₊^ℤ' x a = cong ((invℝ₊ x) ^ℤ_) (sym (ℤ.-Involutive a)) ∙ invℝ₊^ℤ x (ℤ.- a)



invℝ₊^ℚ : ∀ x a → (invℝ₊ x ^ℚ a) ≡ invℝ₊ (x ^ℚ a)
invℝ₊^ℚ x = SQ.ElimProp.go w

 where
 w : ElimProp _
 w .ElimProp.isPropB _ = isSetℝ₊ _ _
 w .ElimProp.f (a , b) = cong (_^ℤ a) (sym (invCommRoot x b))
   ∙ invℝ₊[^ℤ] (root b x) a

^ℚ-minus : ∀ x a → (x ^ℚ a) ≡ ((invℝ₊ x) ^ℚ (ℚ.- a))
^ℚ-minus x = SQ.ElimProp.go w

 where
 w : ElimProp _
 w .ElimProp.isPropB _ = isSetℝ₊ _ _
 w .ElimProp.f (a , (1+ b)) =
  cong (λ b → (x ^ℚ [ a , b ]))
   (sym (·₊₁-identityˡ _))
  ∙
  (sym (invℝ₊^ℤ _ _))
   ∙ cong (_^ℤ _) (invCommRoot _ _)

^ℚ-minus' : ∀ x a → (x ^ℚ (ℚ.- a)) ≡ ((invℝ₊ x) ^ℚ a)
^ℚ-minus' x a = ^ℚ-minus x (ℚ.- a) ∙ cong ((invℝ₊ x) ^ℚ_) (ℚ.-Invol a)



1^ℚ≡1 : ∀ q → 1 ^ℚ q ≡ 1
1^ℚ≡1 = ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB _ = isSetℝ₊ _ _
 w .ElimProp.f (a , b) = cong (_^ℤ a) (ₙ√1 b) ∙ 1^ℤ≡1 _

Iso^ₙₒₜ₀ : ∀ q → 0 ℚ.# q  → Iso ℝ₊ ℝ₊
Iso^ₙₒₜ₀ q _ .Iso.fun = _^ℚ q
Iso^ₙₒₜ₀ q 0#q .Iso.inv = _^ℚ (invℚ q 0#q)
Iso^ₙₒₜ₀ q 0#q .Iso.rightInv x =
 ^ℚ-· x _ _ ∙∙ cong (x ^ℚ_) (ℚ.·Comm _ _ ∙ ℚ.ℚ-y/y q 0#q)
  ∙∙ ℝ₊≡ (·IdL (fst x))
Iso^ₙₒₜ₀ q 0#q .Iso.leftInv x =
 ^ℚ-· x _ _  ∙∙ cong (x ^ℚ_) (ℚ.ℚ-y/y q 0#q) ∙∙ ℝ₊≡ (·IdL (fst x))


-- pow-root-+ : ∀ (m n : ℚ₊) →
--          Iso^₊ (m ℚ₊· n)
--              ≡ compIso (Iso^₊ m) (Iso^₊ n)
-- pow-root-+ m n = SetsIso≡fun isSetℝ₊ isSetℝ₊
--   (funExt (λ x → {!Iso^₊!}))


factor-xᵃ-xᵇ : ∀ x a b → fst (x ^ℚ a) -ᵣ fst (x ^ℚ b) ≡
                        fst (x ^ℚ b) ·ᵣ (fst (x ^ℚ (a ℚ.- b)) -ᵣ 1)
factor-xᵃ-xᵇ x a b =
    cong₂ _-ᵣ_
      (cong (fst ∘ x ^ℚ_) (sym lem--05)
       ∙ cong fst (sym (^ℚ-+ _ _ _)))
      (sym (·IdR _))
  ∙ sym (·DistL- _ _ _)

factor-xᵃ-xᵇ' : ∀ x a b → fst (x ^ℚ a) -ᵣ fst (x ^ℚ b) ≡
                        fst (x ^ℚ a) ·ᵣ (1 -ᵣ fst (x ^ℚ (b ℚ.- a)))
factor-xᵃ-xᵇ' x a b =
 cong₂ _-ᵣ_ (sym (·IdR _))
            (cong fst (cong (x ^ℚ_) (sym lem--05))
              ∙ cong fst (sym (^ℚ-+ _ _ _)) )
   ∙ sym (·DistL- _ _ _)

factorOut-xᵃ : ∀ x a b → x ^ℚ a ≡
     ((x ^ℚ b) ₊·ᵣ (x ^ℚ (a ℚ.- b)))
factorOut-xᵃ x a b =
  cong (x ^ℚ_) (sym lem--05)
  ∙ sym (^ℚ-+ x b (a ℚ.- b))

^ℚ-StrictMonotone : ∀ {x y : ℝ₊} (q : ℚ₊)
    → fst x <ᵣ fst y
    → fst (x ^ℚ (fst q)) <ᵣ fst (y ^ℚ (fst q))
^ℚ-StrictMonotone {_ , 0<x} {_ , 0<y} = uncurry $ ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB _ = isPropΠ2 λ _ _ → isProp<ᵣ _ _
 w .ElimProp.f (pos (suc n) , b) 0<q x<y =
   ^ⁿ-StrictMonotone _ (ℕ.suc-≤-suc  ℕ.zero-≤)
      (<ᵣWeaken≤ᵣ _ _ (snd (root b (_ , 0<x))))
      (<ᵣWeaken≤ᵣ _ _ (snd (root b (_ , 0<y))))
     (ₙ√-StrictMonotone b x<y)

^ℚ-Monotone : ∀ {x y : ℝ₊} (q : ℚ₊)
    → fst x ≤ᵣ fst y
    → fst (x ^ℚ (fst q)) ≤ᵣ fst (y ^ℚ (fst q))
^ℚ-Monotone {_ , 0<x} {_ , 0<y} = uncurry $ ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB _ = isPropΠ2 λ _ _ → isProp≤ᵣ _ _
 w .ElimProp.f (pos (suc n) , b) 0<q x≤y =
   ^ⁿ-Monotone _ -- (ℕ.suc-≤-suc  ℕ.zero-≤)
      (<ᵣWeaken≤ᵣ _ _ (snd (root b (_ , 0<x))))
     (ₙ√-Monotone b x≤y)


1<^ℚ : ∀ x → (q : ℚ₊) → (1 <ᵣ fst x) → (1 <ᵣ fst (x ^ℚ (fst q)))
1<^ℚ x q₊@(q , 0<q) 1<x =
  subst (_<ᵣ fst (x ^ℚ q))
    (cong fst (1^ℚ≡1 q)) (^ℚ-StrictMonotone q₊ 1<x)


1≤^ℚ : ∀ x → (q : ℚ₊) → (1 ≤ᵣ fst x) → (1 ≤ᵣ fst (x ^ℚ (fst q)))
1≤^ℚ x q₊@(q , 0<q) 1≤x =
  subst (_≤ᵣ fst (x ^ℚ q))
    (cong fst (1^ℚ≡1 q)) (^ℚ-Monotone q₊ 1≤x)


^ℚ-StrictMonotoneR : ∀ {x : ℝ₊} → 1 <ᵣ fst x → (q r : ℚ)
    → q ℚ.< r
    → fst (x ^ℚ q) <ᵣ fst (x ^ℚ r)
^ℚ-StrictMonotoneR {x} 1<x q r q<r =
  isTrans<≡ᵣ _ _ _
    (isTrans≡<ᵣ _ _ _
      (sym (·IdR _ )) (<ᵣ-o·ᵣ _ _ (x ^ℚ q) (1<^ℚ _ (ℚ.<→ℚ₊ _ _ q<r) 1<x)))
   (cong fst $ sym (factorOut-xᵃ x  r q))

^ℚ-StrictMonotoneR' : ∀ {x : ℝ₊} → fst x <ᵣ 1  → (q r : ℚ)
    → q ℚ.< r
    → fst (x ^ℚ r) <ᵣ fst (x ^ℚ q)
^ℚ-StrictMonotoneR' {x} x<1 q r q<r =
   fst (invℝ₊-<-invℝ₊ (x ^ℚ q) (x ^ℚ r))
     (subst2 _<ᵣ_
       (cong fst (invℝ₊^ℚ x q))
       (cong fst (invℝ₊^ℚ x r))
       (^ℚ-StrictMonotoneR {invℝ₊ x}
         1/x<1 q r q<r))
   where
   1/x<1 = isTrans≡<ᵣ _ _ _ (cong fst (sym (invℝ₊1)))
            (invEq (invℝ₊-<-invℝ₊ 1 x) x<1)

⊆IsContinuousWithPred : ∀ P P' → (P'⊆P : P' ⊆ P) → ∀ f
        → IsContinuousWithPred P f
        → IsContinuousWithPred P' (λ x x∈ → f x (P'⊆P x x∈))
⊆IsContinuousWithPred _ _ P'⊆P f cp u ε u∈P =
  PT.map (map-snd (λ x _ → x _ ∘ (P'⊆P _)))
    (cp u ε (P'⊆P _ u∈P))


^ℚ-MonotoneR : ∀ {x : ℝ₊} → (q r : ℚ) → q ℚ.≤ r
    → 1 ≤ᵣ fst x
    → fst (x ^ℚ q) ≤ᵣ fst (x ^ℚ r)
^ℚ-MonotoneR {x} q r q≤r 1≤x =

  let z = ≤ContPos'pred {1}
             (⊆IsContinuousWithPred _ _
                (λ x → isTrans<≤ᵣ 0 1 x ((decℚ<ᵣ? {0} {1})))
                 (λ x x< → fst ((x , x<) ^ℚ q))
                (IsContinuous^ℚ q))
             (⊆IsContinuousWithPred _ _
                (λ x → isTrans<≤ᵣ 0 1 x ((decℚ<ᵣ? {0} {1})))
                 (λ x x< → fst ((x , x<) ^ℚ r))
                (IsContinuous^ℚ r))
                (λ u 1≤u → hh (ℚ.≤→<⊎≡ q r q≤r) u 1≤u (ℚ.≤→<⊎≡ 1 u 1≤u))
             (fst x) 1≤x
  in subst (λ 0<x → fst ((fst x , 0<x) ^ℚ q) ≤ᵣ fst ((fst x , 0<x) ^ℚ r))
       (isProp<ᵣ _ _ _ _)
       z


 where
 hh : ((q ≡ r) ⊎ (q ℚ.< r)) → (u : ℚ) (x₀<u : 1 ℚ.≤ u) → (1 ≡ u) ⊎ (1 ℚ.< u) →
        fst
        ((rat u , isTrans<≤ᵣ 0 1 (rat u) decℚ<ᵣ? (≤ℚ→≤ᵣ 1 u x₀<u)) ^ℚ q)
        ≤ᵣ
        fst
        ((rat u , isTrans<≤ᵣ 0 1 (rat u) decℚ<ᵣ? (≤ℚ→≤ᵣ 1 u x₀<u)) ^ℚ r)
 hh _ u x₀<u (inl x) =
   ≡ᵣWeaken≤ᵣ _ _
      (sym ((cong (fst ∘ _^ℚ q) (ℝ₊≡ (cong rat x))))
        ∙∙ cong fst (1^ℚ≡1 q) ∙
           cong fst (sym (1^ℚ≡1 r))
           ∙∙ cong fst (cong (_^ℚ r) (ℝ₊≡ (cong rat x))))
 hh (inr q<r) u 1≤u (inr 1<u) = subst
       (λ uu →
         fst ((rat u , uu) ^ℚ q)
           ≤ᵣ fst ((rat u , uu) ^ℚ r))
            (isProp<ᵣ _ _ _ _)
             (<ᵣWeaken≤ᵣ _ _ ( ^ℚ-StrictMonotoneR
                             {rat u , isTrans<ᵣ 0 1 (rat u)
                                 ((decℚ<ᵣ? {0} {1}))
                                   (<ℚ→<ᵣ _ _ 1<u)}
                              (<ℚ→<ᵣ _ _ 1<u) q r q<r))
 hh (inl q≡r) u 1≤u (inr 1<u) = ≡ᵣWeaken≤ᵣ _ _
   (cong (fst ∘ ((rat u , isTrans<≤ᵣ 0 1 (rat u) decℚ<ᵣ? (≤ℚ→≤ᵣ 1 u 1≤u)) ^ℚ_))
     q≡r)


fromNatℝ+ : ∀ {x y z} →
    x ℕ.+ y ≡ z →
    HasFromNat.fromNat fromNatℝ x +ᵣ HasFromNat.fromNat fromNatℝ y
      ≡ HasFromNat.fromNat fromNatℝ z
fromNatℝ+ p = +ᵣ-rat _ _ ∙ cong rat (ℚ.ℕ+→ℚ+  _ _ ∙ cong ([_/ 1 ] ∘ pos) p)

AM-GM₂ : ∀ z → 1 <ᵣ fst z → ∀ x (Δ : ℚ₊) →
          fst (2 ₊·ᵣ (z ^ℚ x)) <ᵣ
            fst ((z ^ℚ (x ℚ.- fst Δ)) ₊+ᵣ (z ^ℚ (x ℚ.+ fst Δ)))
AM-GM₂ z 1<z x Δ = isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
       (cong (2 ·ᵣ_) (cong (fst ∘ z ^ℚ_) lem--035
          ∙ sym (cong fst (^ℚ-+ z _ _)))
          ∙ ·ᵣComm _ _ ∙ sym (·ᵣAssoc _ _ _))
       (fst (z<x≃y₊·z<y₊·x _ _ (z ^ℚ (x ℚ.- fst Δ))) (isTrans≡<ᵣ _ _ _
         (cong (fst a ·ᵣ_) (sym (fromNatℝ+ refl))
           ∙ ·DistL+ (fst a) 1 1)
       (invEq (x<y≃0<y-x _ _)
      $ isTrans<≡ᵣ _ _ _ (ℝ₊· (_ , w') (_ , w'))
       (L𝐑.lem--073 {fst a} {1})))))
        (·DistL+ _ _ _ ∙ +ᵣComm _ _ ∙
          cong₂ _+ᵣ_
          (cong (((z ^ℚ (x ℚ.- fst Δ)) .fst) ·ᵣ_)
              (sym (rat·ᵣrat _ _)) ∙ ·IdR _)
              (cong (((z ^ℚ (x ℚ.- fst Δ)) .fst) ·ᵣ_)
                (cong fst (^ℚ-+ z _ _)) ∙
                  (cong fst (^ℚ-+ z _ _)) ∙
                    cong (fst ∘ z ^ℚ_)
                      lem--074))


 where
 a = z ^ℚ (fst Δ)
 w' = fst (x<y≃0<y-x _ _) (1<^ℚ z Δ 1<z)

invℚ₊-[/] : ∀ n m → [ n / 1 ] ℚ.· fst (invℚ₊ (fromNat (suc m))) ≡ [ n / 1+ m ]
invℚ₊-[/] n m = cong₂ [_/_]
  (ℤ.·IdR n)
    (·₊₁-identityˡ (1+ m))

[2+N]/[1+N]=2-N/[1+N] : ∀ n →
   [ pos (2 ℕ.+ n) , (1+ n) ] ≡ (fromNat 2) ℚ.- [ pos n / 1+ n ]
[2+N]/[1+N]=2-N/[1+N] n = cong₂ [_/_]
  (sym (ℤ.plusMinus _ _) ∙ cong₂ (ℤ._+_)
      (sym (ℤ.pos+ (2 ℕ.+ n) n) ∙ cong ℤ.sucℤ  (ℤ.pos+ _ _ ∙ cong₂ ℤ._+_
        (cong ℚ.ℕ₊₁→ℤ (sym (·₊₁-identityˡ (1+ n))))
        (cong pos (sym (ℕ.+-zero n)) )))
      (sym (ℤ.·IdR _)))
  (sym (·₊₁-identityˡ _) ∙ sym (·₊₁-identityˡ _))

module AM-GM-hlp (b : ℝ₊) (1<b : 1 <ᵣ (fst b)) (x₀ : ℚ) (s : ℚ₊) where

 x : ℕ → ℚ
 x n = x₀ ℚ.+ fromNat n ℚ.· fst s

 -- TODO : this should be used in few places bellow:
 x-suc : ∀ n → x n ℚ.+ fst s ≡ x (suc n)
 x-suc n = sym (ℚ.+Assoc _ _ _)
     ∙ cong (x₀ ℚ.+_) (
       cong ((fromNat n) ℚ.· (fst s) ℚ.+_) (sym (ℚ.·IdL _)) ∙∙
       sym (ℚ.·DistR+  (fromNat n) 1 (fst s)) ∙∙
           cong (ℚ._· (fst s)) (ℚ.+Comm _ _ ∙ (ℚ.ℕ+→ℚ+ 1 n) ) )

 α : ℝ₊
 α = (1 ₊+ᵣ (b ^ℚ (2 ℚ.· fst s))) ₊·ᵣ ℚ₊→ℝ₊ ( [ 1 / 2 ] , _ )

 y : ℕ → ℝ₊
 y zero = b ^ℚ x₀
 y (suc n) = (b ^ℚ (x n)) ₊·ᵣ α



 fromAM-GM : fst (b ^ℚ x 1) <ᵣ
      fst (b ^ℚ x₀) +ᵣ
      rat (fst (invℚ₊ (fromNat 2))) ·ᵣ (fst (b ^ℚ x 2) -ᵣ fst (b ^ℚ x₀))
 fromAM-GM = isTrans≡<ᵣ _ _ _ (cong (fst ∘ b ^ℚ_ ∘ (x₀ ℚ.+_ ))
      (ℚ.·IdL _))
    (isTrans<≡ᵣ _ _ _ (invEq (z<x/y₊≃y₊·z<x _ _ 2)
   (AM-GM₂ b 1<b (x₀ ℚ.+ fst s) s))
    (cong (_·ᵣ fst (invℝ₊ 2))
       (cong₂ _+ᵣ_
          (cong (fst ∘ b ^ℚ_) (sym lem--034)
            ∙ L𝐑.lem--034 {fst (b ^ℚ x₀)} {fst (b ^ℚ x₀)}
            ∙ cong (_-ᵣ fst (b ^ℚ x₀))
             (x+x≡2x _ ∙ ·ᵣComm _ _))
             ((cong (fst ∘ b ^ℚ_) (sym (ℚ.+Assoc _ _ _)
             ∙ cong (x₀ ℚ.+_) (ℚ.x+x≡2x _))))
         ∙ sym (+ᵣAssoc _ _ _))
      ∙ ·DistR+ (fst (b ^ℚ x₀) ·ᵣ 2) _ _
      ∙ cong₂ _+ᵣ_ ([x·yᵣ]/₊y _ _)
             (·ᵣComm _ _ ∙
             cong₂ _·ᵣ_ (invℝ'-rat 2 _ _)
               (+ᵣComm _ _))))

 opaque
  unfolding -ᵣ_ _+ᵣ_
  convStep : ∀ N → rat (fst (invℚ₊ (fromNat (suc N)))) ·ᵣ
       (fst (b ^ℚ x (suc N)) -ᵣ fst (b ^ℚ x₀))
       <ᵣ
       rat (fst (invℚ₊ (fromNat (suc (suc N))))) ·ᵣ
       (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀))

  convSteps : ∀ N n → n ℕ.< N →
                  fst (b ^ℚ (x (suc n))) <ᵣ
                     (fst (b ^ℚ x₀) +ᵣ (rat (fst (fromNat (suc n)
                      ℚ₊· invℚ₊ (fromNat (suc N)))) ·ᵣ
                       (fst (b ^ℚ (x (suc N))) -ᵣ fst (b ^ℚ x₀))  ))
  convSteps zero n n<0 = ⊥.rec (ℕ.¬-<-zero n<0)
  convSteps (suc N) n n<sN@(N-n@(suc k) , p) =
    let X = convSteps N n (k , cong predℕ p)
    in isTrans<ᵣ _ _ _ X (<ᵣ-o+ _ _ _
         (subst2 _<ᵣ_ (·ᵣAssoc _ _ _ ∙
             cong (_·ᵣ ((fst (b ^ℚ (x (suc N))) -ᵣ fst (b ^ℚ x₀))))
            (sym (rat·ᵣrat  (fromNat (suc n))
             (fst $ invℚ₊ (fromNat (suc N))))))

           (·ᵣAssoc _ _ _ ∙
             cong (_·ᵣ ((fst (b ^ℚ (x (suc (suc N)))) -ᵣ fst (b ^ℚ x₀))))
            (sym (rat·ᵣrat (fromNat (suc n))
             (fst $ invℚ₊ (fromNat (suc (suc N)))))))
           (fst (z<x≃y₊·z<y₊·x _ _ (fromNat (suc n)))
             (convStep N))))
  convSteps (suc zero) zero (zero , 1+n=1+N) = fromAM-GM
  convSteps (suc (suc N)) zero (zero , 1+n=1+N) =
    ⊥.rec (ℕ.znots (cong predℕ 1+n=1+N))
  convSteps (suc N) (suc n) (zero , 2+n=1+N) =
    subst2 _<ᵣ_ (cong (fst ∘ (b ^ℚ_) ∘ x) (sym 2+n=1+N))
      (cong (λ sn → fst (b ^ℚ x₀) +ᵣ
       rat (fst (fromNat (suc (predℕ sn)) ℚ₊· invℚ₊ (fromNat (suc (suc N)))))
       ·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀))) (sym (2+n=1+N)))
         (isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b (fst (b ^ℚ x (suc N))) _ _
           (invEq (z<x/y₊≃y₊·z<x _ _ (ℚ₊→ℝ₊ (invℚ₊ (fromNat (suc N)))))
            (convStep N)))
           (cong (_+ᵣ fst (b ^ℚ x₀))
            (sym (·ᵣAssoc _ _ _) ∙
              cong (rat (fst (invℚ₊ (fromNat (suc (suc N))))) ·ᵣ_)
               (·ᵣComm _ _)
              ∙ ·ᵣAssoc _ _ _
               ∙ cong (_·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀)))
                    ((cong (rat (fst (invℚ₊ (fromNat (suc (suc N))))) ·ᵣ_)
                      (invℝ'-rat _ _ (snd (ℚ₊→ℝ₊ (invℚ₊ (fromNat (suc N)))))
                        ∙ cong rat (ℚ.invℚ₊-invol _))
                     ∙ sym (rat·ᵣrat _ (fromNat (suc N)))) ∙
                        cong rat (ℚ.·Comm _ _)))
              ∙ +ᵣComm _ _ ))


  convStep zero = isTrans≡<ᵣ _ _ _
    (·IdL _) (a<c+b⇒a-c<b _ _  _ fromAM-GM)
  convStep (suc N) =
    isTrans<ᵣ _ _ _
       (isTrans<≡ᵣ _ _ _
          (invEq (z<x/y₊≃y₊·z<x _ _ (fromNat (suc (suc (suc N)))))
            (isTrans≡<ᵣ _ _ _
             (·ᵣAssoc _ _ _ ∙
              cong (_·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀)))
                (sym (rat·ᵣrat _ _) ∙
                 cong rat ((invℚ₊-[/] _ _) ∙ [2+N]/[1+N]=2-N/[1+N] (suc N)))
               ∙
                ·DistR+ 2 (-ᵣ (rat [ _ / _ ])
                ) _
                )
              (isTrans<≡ᵣ _ _ _
                 (<ᵣ-o+ _ _ _ (isTrans≡<ᵣ _ _ _ (-ᵣ· _ _)
                   (-ᵣ<ᵣ _ _
                  (isTrans<≡ᵣ _ _ _
             (a<c+b⇒a-c<b _ _ _ (convSteps (suc N) N ℕ.≤-refl))
            (cong (_·ᵣ (fst (b ^ℚ x (suc (suc N))) -ᵣ fst (b ^ℚ x₀)))
             (cong rat (invℚ₊-[/] (pos (suc N)) (suc N)))))) ))
                 (cong (_-ᵣ (fst (b ^ℚ x (suc N)) -ᵣ fst (b ^ℚ x₀)))
                   (sym (x+x≡2x _))
                  ∙∙ L𝐑.lem--076 ∙∙
                  cong ((_-ᵣ fst (b ^ℚ x₀)) ∘ (_-ᵣ fst (b ^ℚ x (suc N))))
                    (x+x≡2x _)))))
           (cong ((fst (2 ₊·ᵣ (b ^ℚ x (suc (suc N))))
           -ᵣ fst (b ^ℚ x (suc N)) +ᵣ
            -ᵣ fst (b ^ℚ x₀))
             ·ᵣ_) (invℝ'-rat _ _ _) ∙ ·ᵣComm _ _))

       (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊
             ((invℚ₊ ([ pos (suc (suc (suc N))) , (1+ 0) ] , tt)))) (
          (<ᵣ-+o _ _ _
             (a<c+b⇒a-c<b _ _
              (fst (b ^ℚ (x (suc N))))
               (isTrans<≡ᵣ _ _ _ (AM-GM₂ b 1<b (x (suc (suc N))) s)
                 (cong₂ _+ᵣ_
                   (cong (fst ∘ (b ^ℚ_)) (cong (ℚ._- (fst s))
                     (sym (x-suc (suc N)))
                     ∙ sym lem--034))
                    (cong (fst ∘ (b ^ℚ_)) (x-suc (suc (suc N))) )  ))))) )



AM-GM-strict : ∀ z x → (1 <ᵣ fst z) → (Δ : ℚ₊) → (α : ℚ) → 0 ℚ.< α → α ℚ.< 1 →
          fst (z ^ℚ (x ℚ.+ (α ℚ.· fst Δ))) <ᵣ
            fst (z ^ℚ x) +ᵣ
              (rat α) ·ᵣ
                (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x))
AM-GM-strict z x 1<z Δ = ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB _ = isPropΠ2 λ _ _ → isProp<ᵣ _ _
 w .ElimProp.f (pos zero , (1+ m)) 0<α α<1 =
   ⊥.rec (ℤ.¬-pos<-zero 0<α)
 w .ElimProp.f (pos (suc n) , (1+ m)) 0<α α<1 =
   subst2 _<ᵣ_
     (cong (fst ∘ z ^ℚ_ ∘ (x ℚ.+_))
         (ℚ.·Assoc _ [ pos 1 / 1+ m ] _ ∙
            cong (ℚ._· (fst Δ)) n/N-lem))
     ((cong (fst (z ^ℚ x) +ᵣ_)
       (cong₂ _·ᵣ_ (cong rat n/N-lem)
         (cong (_-ᵣ (fst (z ^ℚ x)))
           ((cong (fst ∘ z ^ℚ_ ∘ (x ℚ.+_))
              (ℚ.·Assoc _ [ pos 1 / 1+ m ] _ ∙
            cong (ℚ._· (fst Δ)) (ℚ.x·invℚ₊[x] (fromNat (suc m)))
              ∙ ℚ.·IdL _)))))))
     ww
  where
  Δ/N =  ([ pos 1 / 1+ m ] , _) ℚ₊· Δ

  n/N-lem = cong₂ [_/_] (ℤ.·IdR _) (·₊₁-identityˡ _)

  ww = AM-GM-hlp.convSteps z 1<z x Δ/N m n
       (ℕ.predℕ-≤-predℕ (ℤ.pos-≤-pos→ℕ≤ _ _
         (subst2 ℤ._<_ (ℤ.·IdR _) (ℤ.·IdL _)
           α<1)))
 w .ElimProp.f α@(ℤ.negsuc n , 1+ m) 0<α _ =
   ⊥.rec $ ℤ.¬pos≤negsuc (subst (0 ℤ.≤_) (ℤ.·IdR _)
            (ℚ.<Weaken≤ 0 SQ.[ α ] 0<α))

AM-GM : ∀ z x → (1 <ᵣ fst z) → (Δ : ℚ₊) → (α : ℚ) → 0 ℚ.≤ α → α ℚ.≤ 1 →
          fst (z ^ℚ (x ℚ.+ (α ℚ.· fst Δ))) ≤ᵣ
            fst (z ^ℚ x) +ᵣ
              (rat α) ·ᵣ
                (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x))

AM-GM z x 1<z Δ α 0≤α α≤1 =
 ⊎.rec
   (λ α≡1 → ≡ᵣWeaken≤ᵣ
       (fst (z ^ℚ (x ℚ.+ α ℚ.· fst Δ)))
       (fst (z ^ℚ x) +ᵣ rat α ·ᵣ (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x)))
       (cong {y = fst Δ} (fst ∘ (z ^ℚ_) ∘ (x ℚ.+_))
          (cong (ℚ._· _) α≡1 ∙ ℚ.·IdL _)
        ∙∙ sym (L𝐑.lem--05)
        ∙∙ cong (fst (z ^ℚ x) +ᵣ_)
             (sym (cong ((_·ᵣ (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x))
               ) ∘ rat) α≡1 ∙ ·IdL _))))
   (⊎.rec
      (λ 0=α _ → ≡ᵣWeaken≤ᵣ _ _
         (cong (fst ∘ (z ^ℚ_))
            (𝐐'.+IdR' x _
               (cong (ℚ._· (fst Δ)) (sym 0=α)
                 ∙ 𝐐'.0LeftAnnihilates _))
           ∙ sym (𝐑'.+IdR' _ _
           (cong (_·ᵣ (fst (z ^ℚ (x ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ x)))
             (cong rat (sym 0=α))
            ∙ 𝐑'.0LeftAnnihilates _))))
      ((<ᵣWeaken≤ᵣ _ _ ∘_) ∘ (AM-GM-strict z x 1<z Δ α))
      (ℚ.≤→≡⊎< 0 α 0≤α))
   (ℚ.≤→≡⊎< α 1 α≤1)

^ⁿ-1 : ∀ x → x ^ⁿ 1 ≡ x
^ⁿ-1 x = ·IdL _

^ℚ-1 : ∀ x → x ^ℚ 1 ≡ x
^ℚ-1 x = ℝ₊≡ (^ⁿ-1 _)

-- AM-GM



slope-incr-strict : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b c : ℚ)
  → (a<b : a ℚ.< b) → (b<c : b ℚ.< c) →  (a<c : a ℚ.< c) →
  ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
      <ᵣ
  ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))
slope-incr-strict z 1<z a b c a<b b<c a<c =
  isTrans≡<ᵣ _ _ _
     (cong (_·ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b))))
      (cong (_-ᵣ fst (z ^ℚ a))
          (cong (fst ∘ (z ^ℚ_))
            (sym lem--05 ∙ cong (a ℚ.+_) (sym (ℚ.y·[x/y] _ _) ∙
             ℚ.·Comm _ _ ∙
              cong (ℚ._· fst (ℚ.<→ℚ₊ a c a<c))
               (ℚ.·Comm _ _))))))
     (isTrans<≡ᵣ _ _ _
      amgm
      (·ᵣComm _ _ ∙
        cong₂ _·ᵣ_ (cong (_-ᵣ fst (z ^ℚ a))
          (cong (fst ∘ (z ^ℚ_))
            lem--05))
         (sym (invℝ'-rat _ _ (snd (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c )))))))

 where
 α₊ = (ℚ.<→ℚ₊ _ _  a<b ) ℚ₊· invℚ₊ (ℚ.<→ℚ₊ _ _  a<c )
 α<1 : fst α₊ ℚ.< 1
 α<1 = ℚ.x<y·z→x·invℚ₊y<z _ _ _
   (subst (b ℚ.- a ℚ.<_)
    (sym (ℚ.·IdR _))
    (ℚ.<-+o _ _ (ℚ.- a) b<c))


 amgm = invEq (z/y<x₊≃z<y₊·x _ _ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<b )))
  (isTrans<≡ᵣ _ _ _ (a<c+b⇒a-c<b _ _ _
      (AM-GM-strict z a 1<z ((ℚ.<→ℚ₊ _ _  a<c ))
          (fst α₊) (ℚ.0<ℚ₊ α₊) α<1))
           (cong (_·ᵣ (fst (z ^ℚ (a ℚ.+ fst (ℚ.<→ℚ₊ _ _ a<c))) -ᵣ
       fst (z ^ℚ a))) (rat·ᵣrat _ _)
        ∙ sym (·ᵣAssoc _ _ _)))

opaque
 unfolding _+ᵣ_
 slope-incr'-strict : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b c : ℚ)
   → (a ℚ.< b) → (b<c : b ℚ.< c) →  (a<c : a ℚ.< c) →
   ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<c))
       <ᵣ
   ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ b))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  b<c ))
 slope-incr'-strict z 1<z a b c a<b b<c a<c =
  let w = fst (x'/x<[x'+y']/[x+y]≃[x'+y']/[x+y]<y'/y
                  (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b)) ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)))
                  (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ b<c)) ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ b))))
              (isTrans<≡ᵣ _ _ _
                (slope-incr-strict z 1<z _ _ _ a<b b<c a<c)
                (cong₂ _／ᵣ₊_
                  L𝐑.lem--077
                  (ℝ₊≡ (cong rat lem--077))))
  in isTrans≡<ᵣ _ _ _
      (cong₂ _／ᵣ₊_
        L𝐑.lem--077
        ((ℝ₊≡ (cong rat lem--077)))) w

opaque
 unfolding _+ᵣ_ -ᵣ_
 slope-incr : (z : ℝ₊) (a b c : ℚ)
   → (a<b : a ℚ.< b) → (b≤c : b ℚ.≤ c) →  (a<c : a ℚ.< c) →
   ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
       ≤ᵣ
   ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))
 slope-incr (z , 0<z) a b c a<b b≤c a<c =
   <→≤ContPos'pred {0}
     {λ z 0<z →
        ((fst ((z , 0<z) ^ℚ b)
        -ᵣ fst ((z , 0<z) ^ℚ a))
      ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))}
      {λ z 0<z →
         ((fst ((z , 0<z) ^ℚ c)
           -ᵣ fst ((z , 0<z) ^ℚ a))
      ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))}
       ((IsContinuousWP∘' _ _ _
       (IsContinuous·ᵣR (fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b)))))
       (contDiagNE₂WP sumR _ _ _
         (⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ b))
            (IsContinuousWP∘' _ _ _ IsContinuous-ᵣ
              ((⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ a)))))))
       (((IsContinuousWP∘' _ _ _
       (IsContinuous·ᵣR (fst (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<c)))))
       (contDiagNE₂WP sumR _ _ _
         (⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ c))
            (IsContinuousWP∘' _ _ _ IsContinuous-ᵣ
              ((⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ a))))))))
       (ℚ.byTrichotomy 1 w)
         z 0<z

  where

   slope-incr** : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b c : ℚ)
     → (a<b : a ℚ.< b) → (b≤c : b ℚ.≤ c) →  (a<c : a ℚ.< c) →
     ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
         ≤ᵣ
     ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
       ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<c ))
   slope-incr** z 1<z a b c a<b =
      flip
        λ a<c → ⊎.rec
           (≡ᵣWeaken≤ᵣ _ _ ∘
             cong
               (λ (b , a<b) →
                 ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)) ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b)))
               ∘ Σ≡Prop {B = λ b → a ℚ.< b} (ℚ.isProp< _))
           (λ b<c → <ᵣWeaken≤ᵣ _ _ $  slope-incr-strict z 1<z a b c a<b b<c a<c)
          ∘ ℚ.≤→≡⊎< b c

   w : ℚ.TrichotomyRec 1
          λ u → (0<u : 0 <ᵣ rat u) → ((fst ((rat u , 0<u) ^ℚ b) -ᵣ fst ((rat u , 0<u) ^ℚ a)) ／ᵣ₊
                      ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a b a<b))
                     ≤ᵣ
                     ((fst ((rat u , 0<u) ^ℚ c) -ᵣ fst ((rat u , 0<u) ^ℚ a)) ／ᵣ₊
                      ℚ₊→ℝ₊ (ℚ.<→ℚ₊ a c a<c))
   w .ℚ.TrichotomyRec.lt-case u u<1 0<u =
     subst2 _≤ᵣ_
         (sym (-ᵣ· _ _ ) ∙ cong₂ (λ A B → A ／ᵣ₊ (ℚ₊→ℝ₊ B))
            (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_ (sym (cong fst (^ℚ-minus u₊ b)))
                        ((sym (cong fst (^ℚ-minus u₊ a)))))
                        {u = ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) (ℚ.minus-< _ _ a<b)}
                        (ℚ₊≡ (sym lem--083)))
         (sym (-ᵣ· _ _) ∙ (cong₂ (λ A B → A ／ᵣ₊ (ℚ₊→ℝ₊ B))
            (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_
               ((sym (cong fst (^ℚ-minus u₊ c))))
               ((sym (cong fst (^ℚ-minus u₊ a)))))
               {u = ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< _ _ a<c)}
                 (ℚ₊≡ (sym lem--083))))
           (-ᵣ≤ᵣ _ _
             (⊎.rec ww'' ww' (ℚ.≤→≡⊎< b c b≤c)))
     where
     u₊ : ℝ₊
     u₊ = (rat u , 0<u)
     1/u₊ : ℝ₊
     1/u₊ = (invℝ₊ (rat u , 0<u))
     1<1/u : 1 <ᵣ (fst 1/u₊)
     1<1/u = isTrans<≡ᵣ _ _ _
        (invEq (z<x/y₊≃y₊·z<x 1 1 (rat u , 0<u)) (isTrans≡<ᵣ _ _ _
            (·IdR _) (<ℚ→<ᵣ _ _ u<1)))
         (·IdL _)

     ww' : (b ℚ.< c) →   ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- c)))
                                  ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< a c a<c)))
                                    ≤ᵣ
                                ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- b)))
                                  ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) (ℚ.minus-< a b a<b) ))
     ww' b<c = <ᵣWeaken≤ᵣ _ _ $ slope-incr'-strict (invℝ₊ (rat u , 0<u)) 1<1/u (ℚ.- c) (ℚ.- b) (ℚ.- a)
              (ℚ.minus-< _ _ b<c) (ℚ.minus-< _ _ a<b) (ℚ.minus-< _ _ a<c)


     ww'' : (b ≡ c) →   ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- c)))
                                  ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< a c a<c)))
                                   ≤ᵣ
                                ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- b)))
                                  ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) (ℚ.minus-< a b a<b) ))
     ww'' b=c = ≡ᵣWeaken≤ᵣ _ _ (
             cong
               (λ (b , -b<-a) →
                 ((fst (1/u₊ ^ℚ (ℚ.- a)) -ᵣ fst (1/u₊ ^ℚ (ℚ.- b))) ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- b) (ℚ.- a) -b<-a)))
               (Σ≡Prop {B = λ b → (ℚ.- b) ℚ.< (ℚ.- a)} (λ _ → ℚ.isProp< _ _) (sym b=c)))


   w .ℚ.TrichotomyRec.eq-case _ = ≡ᵣWeaken≤ᵣ _ _
             (𝐑'.0LeftAnnihilates' _ _
                 (𝐑'.+InvR' _ _ (cong (fst ∘ (_^ℚ b)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 b)
                   ∙ sym (cong (fst ∘ (_^ℚ a)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 a))))
               ∙ sym (𝐑'.0LeftAnnihilates' _ _
                 (𝐑'.+InvR' _ _ ((cong (fst ∘ (_^ℚ c)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 c)
                   ∙ sym (cong (fst ∘ (_^ℚ a)) (ℝ₊≡ refl) ∙ cong fst (1^ℚ≡1 a)))))))
   w .ℚ.TrichotomyRec.gt-case u 1<u 0<u =
     slope-incr** (rat u , 0<u) (<ℚ→<ᵣ _ _ 1<u) a b c a<b b≤c a<c




slope-incr' : (z : ℝ₊) → (a b c : ℚ)
  → (a≤b : a ℚ.≤ b) → (b<c : b ℚ.< c) →  (a<c : a ℚ.< c) →
  ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<c))
      ≤ᵣ
  ((fst (z ^ℚ c) -ᵣ fst (z ^ℚ b))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  b<c ))
slope-incr' z a b c a≤b b<c a<c =
     subst2 _≤ᵣ_
       (sym (-ᵣ· _ _) ∙ cong₂ (λ A B → A ／ᵣ₊ (ℚ₊→ℝ₊ B))
          (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_ (sym (cong fst (^ℚ-minus z _)))
                      ((sym (cong fst (^ℚ-minus z _)))))
                      {u = ℚ.<→ℚ₊ (ℚ.- _) (ℚ.- _) (ℚ.minus-< _ _ _)}
                      (ℚ₊≡ (sym lem--083)))
       (sym (-ᵣ· _ _) ∙ (cong₂ (λ A B → A ／ᵣ₊ (ℚ₊→ℝ₊ B))
          (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_
             ((sym (cong fst (^ℚ-minus z _))))
             ((sym (cong fst (^ℚ-minus z _)))))
             {u = ℚ.<→ℚ₊ (ℚ.- _) (ℚ.- _) (ℚ.minus-< _ _ _)}
               (ℚ₊≡ (sym lem--083))))
              ww

 where
 ww : -ᵣ ((fst (invℝ₊ z ^ℚ (ℚ.- a)) -ᵣ fst (invℝ₊ z ^ℚ (ℚ.- c))) ／ᵣ₊
        ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- a) (ℚ.minus-< a c a<c)))
      ≤ᵣ
      -ᵣ ((fst (invℝ₊ z ^ℚ (ℚ.- b)) -ᵣ fst (invℝ₊ z ^ℚ (ℚ.- c))) ／ᵣ₊
        ℚ₊→ℝ₊ (ℚ.<→ℚ₊ (ℚ.- c) (ℚ.- b) (ℚ.minus-< b c b<c)))


 ww = -ᵣ≤ᵣ _ _ (slope-incr (invℝ₊ z) (ℚ.- c) (ℚ.- b) (ℚ.- a)
         (ℚ.minus-< _ _ b<c) (ℚ.minus-≤ _ _ a≤b) (ℚ.minus-< _ _ a<c))


slope-monotone : (z : ℝ₊)  → (a b a' b' : ℚ)
  → (a<b : a ℚ.< b) → (a'<b' : a' ℚ.< b') → (a≤a' : a ℚ.≤ a') →  (b≤b' : b ℚ.≤ b') →
  ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
      ≤ᵣ
  ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a'<b' ))
slope-monotone z a b a' b' a<b a'<b' a≤a' b≤b' =
  isTrans≤ᵣ _ _ _
    (slope-incr z a b b' a<b b≤b' (ℚ.isTrans<≤ _ _ _ a<b b≤b'))
      (slope-incr' z a a' b' a≤a' a'<b' (ℚ.isTrans<≤ _ _ _ a<b b≤b'))

opaque
 unfolding -ᵣ_ _+ᵣ_
 slope-monotone＃ : (z : ℝ₊) → (a b a' b' : ℚ)
   → (a＃b : rat a ＃ rat b) → (a'<b' : a' ℚ.< b') → (a≤a' : a ℚ.≤ a') →  (b≤b' : b ℚ.≤ b') →
   ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
     ／ᵣ[ rat b -ᵣ rat a  , invEq (＃Δ _ _) a＃b ])
       ≤ᵣ
   ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a'<b' ))
 slope-monotone＃ z a b a' b' (inl a<b) a'<b' a≤a' b≤b' =
   isTrans≡≤ᵣ _ _ _
     (cong ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)) ·ᵣ_)
       (sym (invℝ₊≡invℝ _ _)))
     (slope-monotone z  a b a' b' (<ᵣ→<ℚ _ _ a<b) a'<b' a≤a' b≤b')
 slope-monotone＃ z  a b a' b' (inr b<a) a'<b' a≤a' b≤b' =
   isTrans≡≤ᵣ _ _ _
      w
     (slope-monotone z b a a' b' (<ᵣ→<ℚ _ _ b<a) a'<b'
       (ℚ.isTrans≤ _ _ _
         (ℚ.<Weaken≤ _ _ (<ᵣ→<ℚ _ _ b<a)) a≤a')
          (ℚ.isTrans≤ _ _ _ a≤a' (ℚ.<Weaken≤ _ _ a'<b')))

  where
  w : ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a)) ／ᵣ[ rat b -ᵣ rat a ,
        invEq (＃Δ (rat b) (rat a)) (inr b<a) ])
       ≡
       ((fst (z ^ℚ a) -ᵣ fst (z ^ℚ b)) ／ᵣ₊
        ℚ₊→ℝ₊ (ℚ.<→ℚ₊ b a (<ᵣ→<ℚ b a b<a)))
  w = sym (-ᵣ·-ᵣ _ _) ∙
      cong₂ _·ᵣ_
        (-[x-y]≡y-x _ _)
        (-invℝ _ _ ∙∙ cong₂ invℝ (-[x-y]≡y-x (rat b) (rat a))
          (toPathP refl)
          ∙∙ sym (invℝ₊≡invℝ _ _))

 slope-monotone＃' : (z : ℝ₊) → (a b a' b' : ℚ)
   → (a<b : a ℚ.< b) → (a'＃b' : rat a' ＃ rat b')  → (a≤a' : a ℚ.≤ a') →  (b≤b' : b ℚ.≤ b') →
   ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a<b ))
       ≤ᵣ
   ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
      ／ᵣ[ rat b' -ᵣ rat a'  , invEq (＃Δ _ _) a'＃b' ])
 slope-monotone＃' z a b a' b' a<b (inl a'<b') a≤a' b≤b' =
   isTrans≤≡ᵣ _ _ _
     (slope-monotone z a b a' b' a<b (<ᵣ→<ℚ _ _ a'<b') a≤a' b≤b')
     ((cong ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a')) ·ᵣ_)
       (invℝ₊≡invℝ _ _)))
 slope-monotone＃' z a b a' b' a<b (inr b'<a') a≤a' b≤b' =
  isTrans≤≡ᵣ _ _ _
    ((slope-monotone z a b b' a' a<b (<ᵣ→<ℚ _ _ b'<a')
       (ℚ.isTrans≤ _ _ _ (ℚ.<Weaken≤ _ _ a<b) b≤b')
       (ℚ.isTrans≤ _ _ _ b≤b' ((ℚ.<Weaken≤ _ _ (<ᵣ→<ℚ _ _ b'<a'))))))
    (sym w)


  where
  w : ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a')) ／ᵣ[ rat b' -ᵣ rat a' ,
        invEq (＃Δ (rat b') (rat a')) (inr b'<a') ])
       ≡
       ((fst (z ^ℚ a') -ᵣ fst (z ^ℚ b')) ／ᵣ₊
        ℚ₊→ℝ₊ (ℚ.<→ℚ₊ b' a' (<ᵣ→<ℚ b' a' b'<a')))
  w = sym (-ᵣ·-ᵣ _ _) ∙
      cong₂ _·ᵣ_
        (-[x-y]≡y-x _ _)
        (-invℝ _ _ ∙∙ cong₂ invℝ (-[x-y]≡y-x (rat b') (rat a'))
          (toPathP refl)
          ∙∙ sym (invℝ₊≡invℝ _ _))




slope-monotone-strict : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b a' b' : ℚ)
  → (a<b : a ℚ.< b) → (a'<b' : a' ℚ.< b') → (a≤a' : a ℚ.≤ a') →  (b<b' : b ℚ.< b') →
  ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
      <ᵣ
  ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a'<b' ))
slope-monotone-strict z 1<z a b a' b' a<b a'<b' a≤a' b<b' =
  isTrans<≤ᵣ _ _ _
    (slope-incr-strict z 1<z a b b' a<b b<b' (ℚ.isTrans< _ _ _ a<b b<b'))
      (slope-incr' z a a' b' a≤a' a'<b' (ℚ.isTrans< _ _ _ a<b b<b'))

slope-monotone-strict' : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b a' b' : ℚ)
  → (a<b : a ℚ.< b) → (a'<b' : a' ℚ.< b') → (a<a' : a ℚ.< a') →  (b≤b' : b ℚ.≤ b') →
  ((fst (z ^ℚ b) -ᵣ fst (z ^ℚ a))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ a<b))
      <ᵣ
  ((fst (z ^ℚ b') -ᵣ fst (z ^ℚ a'))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  a'<b' ))
slope-monotone-strict' z 1<z a b a' b' a<b a'<b' a<a' b≤b' =
  isTrans≤<ᵣ _ _ _
    (slope-incr z a b b' a<b b≤b' (ℚ.isTrans<≤ _ _ _ a<b b≤b'))
      (slope-incr'-strict z 1<z a a' b' a<a' a'<b' (ℚ.isTrans<≤ _ _ _ a<b b≤b'))

opaque
 unfolding invℝ
 bernoulli's-ineq-^ℚ-r<1 : ∀ x r → 1 <ᵣ fst x → 0 ℚ.< r → r ℚ.< 1 → fst (x ^ℚ r) <ᵣ 1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1)
 bernoulli's-ineq-^ℚ-r<1 x r 1<x 0<r r<1 =
   isTrans<≡ᵣ _ _ _ (a-b<c⇒a<c+b _ 1 _
       ((fst (z/y<x₊≃z<y₊·x _ _ _)
             (slope-incr-strict x 1<x 0 r 1
                0<r r<1 ℚ.decℚ<?))))
              (+ᵣComm _ _ ∙ cong (1 +ᵣ_)
                (cong₂ _·ᵣ_ (cong rat (ℚ.+IdR _))
                  (𝐑'.·IdR' _ _ (cong rat ℚ.decℚ?)
                   ∙ cong₂ (_-ᵣ_) (cong fst (^ℚ-1 x)) (cong fst (1^ℚ≡1 0)))))

 bernoulli's-ineq-^ℚ : ∀ x r → 1 <ᵣ fst x
  → 1 ℚ.< r → 1 +ᵣ rat r ·ᵣ (fst x -ᵣ 1)  <ᵣ fst (x ^ℚ r)
 bernoulli's-ineq-^ℚ x r 1<x 1<r =
   isTrans≡<ᵣ _ _ _
        (cong (1 +ᵣ_) (cong₂ _·ᵣ_
          (sym (cong rat (ℚ.+IdR _)))
          (cong₂ (_-ᵣ_) (sym (cong fst (^ℚ-1 x))) (cong fst (sym (1^ℚ≡1 0)))
           ∙ sym (𝐑'.·IdR' _ _ (cong rat ℚ.decℚ?))))
          ∙ +ᵣComm _ _)
        (a<b-c⇒a+c<b _ _ 1 (fst (z<x/y₊≃y₊·z<x _ _ _)
         (slope-incr-strict x 1<x 0 1 r ℚ.decℚ<?
          1<r (ℚ.isTrans< _ 1 _ ℚ.decℚ<? 1<r))))


power-slope-Δ : (z : ℝ₊) (1<z : 1 <ᵣ fst z) → (a b : ℚ) → a ℚ.< b →
   (Δ : ℚ₊) →
  fst (z ^ℚ b) -ᵣ fst (z ^ℚ a) <ᵣ
   fst (z ^ℚ (b ℚ.+ fst Δ)) -ᵣ fst (z ^ℚ (a ℚ.+ fst Δ))
power-slope-Δ z 1<z a b a<b Δ =
  isTrans<≡ᵣ _ _ _
    (isTrans≡<ᵣ _ _ _
       (sym (·IdL _))
       (<ᵣ-·ᵣo _ _ (_ ,
         x<y→0<y-x _ _ (^ℚ-StrictMonotoneR 1<z _ _ a<b ))
        (1<^ℚ z Δ 1<z)  ))
    (·DistL- (fst (z ^ℚ (fst Δ))) _ _ ∙
      cong₂ _-ᵣ_
       (·ᵣComm _ _ ∙ cong fst (^ℚ-+ z _ _))
       (·ᵣComm _ _ ∙ cong fst (^ℚ-+ z _ _)))


fromNatℝ≡fromNatℚ : ∀ n → fromNat (suc n) ≡ ℚ₊→ℝ₊ (fromNat (suc n))
fromNatℝ≡fromNatℚ n = ℝ₊≡ refl

bound : ℝ₊ → ℚ₊ → ℝ
bound z B = ((fst (z ^ℚ (2 ℚ.· (fst B))) -ᵣ fst (z ^ℚ (fst B))) ·ᵣ
   rat (fst (invℚ₊ B)))

bound1≡0 : ∀ q → bound 1 q ≡ 0
bound1≡0 q = 𝐑'.0LeftAnnihilates' _ _
  (𝐑'.+InvR' _ _ ((cong fst (1^ℚ≡1 _) ∙ cong fst (sym (1^ℚ≡1 _)))))

2x-x≡x : ∀ q → (2 ℚ.· q) ℚ.- q ≡ q
2x-x≡x q = cong ((2 ℚ.· q) ℚ.+_)
            (cong (ℚ.-_) (sym (ℚ.·IdL _)))
              ∙ sym (𝐐'.·DistL- 2 1 q)
              ∙ ℚ.·IdL _

module _ (Z N : ℕ) where

 N<2N : fromNat (suc N) ℚ.< 2 ℚ.· fromNat (suc N)
 N<2N = (ℚ.<ℤ→<ℚ _ _
         (ℤ.suc-≤-suc (subst (pos (suc N) ℤ.≤_) (cong pos (ℕ.+-suc _ _)
          ∙ ℤ.pos+ _ _)
           (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-+k {0} {N} {k = suc N} ℕ.zero-≤)))))

 N<2N' : fromNat (suc N) ℚ.< fromNat (2 ℕ.· suc N)
 N<2N' = subst (fromNat (suc N) ℚ.<_) (ℚ.ℕ·→ℚ· _ _) N<2N



 1<2+Z = (<ℚ→<ᵣ 1 (fromNat (2 ℕ.+ Z)) (ℚ.<ℤ→<ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
        (ℕ.≤-k+ {k = 2} ℕ.zero-≤))))

 boundℚ : ℚ₊
 boundℚ = ℚ.<→ℚ₊ _ _
    (<ᵣ→<ℚ ((fromNat (2 ℕ.+ Z)) ℚ^ⁿ suc N)
           ((fromNat (2 ℕ.+ Z)) ℚ^ⁿ (2 ℕ.· suc N))
      (subst2 _<ᵣ_
        (^ⁿ-ℚ^ⁿ _ _)
        (cong (fst ∘ (fromNat (suc (suc Z)) ^ℚ_))
          (ℚ.ℕ·→ℚ· _ _)
         ∙ ^ⁿ-ℚ^ⁿ _ _)
       (^ℚ-StrictMonotoneR {fromNat (suc (suc Z))}
       1<2+Z
       (fromNat (suc N)) (2 ℚ.· fromNat (suc N)) N<2N)))
         ℚ₊·
       (invℚ₊ (fromNat (suc N)))

 boundℚInv : ℚ₊
 boundℚInv = ℚ.<→ℚ₊ _ _
    (<ᵣ→<ℚ ([ 1 / fromNat (2 ℕ.+ Z) ] ℚ^ⁿ (2 ℕ.· suc N))
           ([ 1 / fromNat (2 ℕ.+ Z) ] ℚ^ⁿ (suc N))
      (subst2 _<ᵣ_
        (^ⁿ-ℚ^ⁿ _ _)
        (^ⁿ-ℚ^ⁿ _ _)
        (^ℚ-StrictMonotoneR' {ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , _)}
           (<ℚ→<ᵣ _ _ (fst (ℚ.invℚ₊-<-invℚ₊ 1 (fromNat (2 ℕ.+ Z)))
             (ℚ.<ℤ→<ℚ _ _ ((ℤ.ℕ≤→pos-≤-pos _ _
               (ℕ.≤-k+ {k = 2} ℕ.zero-≤))))))
           (fromNat (suc N)) (fromNat (2 ℕ.· suc N))
              (subst (λ n → fromNat (n) ℚ.< fromNat (2 ℕ.· suc N))
                (ℕ.·-identityˡ _)
                (ℚ.<ℤ→<ℚ _ _ (
                  invEq (ℤ.pos-<-pos≃ℕ< _ _)
                    (ℕ.<-·sk {1} {2} {N} ℕ.≤-refl)))))))
         ℚ₊·
       (invℚ₊ (fromNat (suc N)))


 hlp : fst
      (invℝ₊
       (ℚ₊→ℝ₊
        (ℚ.<→ℚ₊ [ pos (suc N) / 1+ 0 ]
         [ pos (suc (N ℕ.+ suc (N ℕ.+ zero))) / 1+ 0 ] N<2N')))
      ≡ rat (fst (invℚ₊ ([ pos (suc N) , (1+ 0) ] , tt)))
 hlp = (invℝ₊-rat _ ∙
            cong (rat ∘ fst ∘ invℚ₊)
              (ℚ₊≡ (cong (ℚ._- (fromNat (suc N))) (sym (ℚ.ℕ·→ℚ· _ _))
               ∙ 2x-x≡x (fromNat (suc N)))))

 hlp2 : invℝ₊ (fromNat (2 ℕ.+ Z)) ≡
      ℚ₊→ℝ₊ ([ 1 / fromNat (2 ℕ.+ Z) ] , _)
 hlp2 = ℝ₊≡ (cong (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ _)
  ∙ invℝ₊-rat (fromNat (2 ℕ.+ Z)))

 opaque
  unfolding -ᵣ_ _+ᵣ_
  boundℚInv<boundℚ : fst (boundℚInv) ℚ.< fst (boundℚ)
  boundℚInv<boundℚ =
    <ᵣ→<ℚ _ _
      (subst2 _<ᵣ_
        (cong₂ _·ᵣ_
           (cong₂ _-ᵣ_
             (cong fst (^ℚ-minus' _ _ ∙ cong (_^ℚ fromNat (suc N))
                  hlp2)
              ∙ ^ⁿ-ℚ^ⁿ (suc N) _)
             (cong fst (^ℚ-minus' _ _ ∙ cong (_^ℚ fromNat (2 ℕ.· suc N))
                  hlp2) ∙ ^ⁿ-ℚ^ⁿ (2 ℕ.· suc N) _))
           (cong (fst ∘ invℝ₊ ∘ ℚ₊→ℝ₊)
             (ℚ₊≡ (sym lem--083))
             ∙ hlp)
          ∙ sym (rat·ᵣrat _ _))
        (cong₂ _·ᵣ_
           (cong₂ _-ᵣ_
             (^ⁿ-ℚ^ⁿ _ _)
             (^ⁿ-ℚ^ⁿ _ _))
           hlp
          ∙ sym (rat·ᵣrat _ _))
        (slope-monotone-strict (fromNat (2 ℕ.+ Z))
           1<2+Z
          (ℚ.- (fromNat (2 ℕ.· suc N))) (ℚ.- (fromNat (suc N)))
          (fromNat (suc N)) (fromNat (2 ℕ.· suc N))
          (ℚ.minus-< _ _ N<2N')
          N<2N'
          (ℚ.isTrans≤ _ 0 _  (ℚ.neg≤pos _ _) (ℚ.0≤pos _ _))
          (ℚ.isTrans≤< _ 0 _  (ℚ.neg≤pos _ _) (ℚ.0<pos _ _))))

1<boundℚ : ∀ Z n → 1 ℚ.< fst (boundℚ Z n)
1<boundℚ Z n = w

 where
 w : 1 ℚ.< (((fromNat (2 ℕ.+ Z)) ℚ^ⁿ (2 ℕ.· suc n)) ℚ.- ((fromNat (2 ℕ.+ Z)) ℚ^ⁿ suc n))
              ℚ.· fst (invℚ₊ (fromNat (suc n)))
 w = subst (1 ℚ.<_)
    (ℚ.·Assoc _ _ _
       ∙ cong (ℚ._· fst (invℚ₊ (fromNat (suc n))))
         (ℚ.·DistR+ (fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n) (-1) (fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n)
           ∙ cong₂ (ℚ._+_)
           (ℚ.·-ℚ^ⁿ (suc n) (suc n) (fromNat (2 ℕ.+ Z)) ∙ cong {x = (suc n) ℕ.+ (suc n)} ((fromNat (2 ℕ.+ Z)) ℚ^ⁿ_)
             (cong (λ n' → suc (n ℕ.+ suc n')) (sym (ℕ.+-zero n))))
             (sym (ℚ.-·- (ℚ.- 1) _) ∙ ℚ.·IdL _)
             ) )
    (ℚ.≤<Monotone·-onPos 1 ((fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n) ℚ.- 1)
       1 _
       (ℚ.≤-+o 2 ((fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n)) -1
         (ℚ.isTrans≤ _ (fromNat (2 ℕ.+ Z)) _ (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos 2 (2 ℕ.+ Z)
          (ℕ.suc-≤-suc (ℕ.suc-≤-suc (ℕ.zero-≤ {Z})))))
          (subst (fromNat (2 ℕ.+ Z) ℚ.≤_) (sym (ℚ.fromNat-^ (2 ℕ.+ Z) (suc n)))
            (ℚ.≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _
              (subst (ℕ._≤ ((2 ℕ.+ Z) ^ suc n))
                (cong (suc ∘ suc) (·-identityʳ Z))
                 (ℕ.^-monotone (2 ℕ.+ Z) 0 n (ℕ.zero-≤ {n}))))))))
       (subst (ℚ._<
          (fromNat (2 ℕ.+ Z) ℚ^ⁿ suc n) ℚ.· fst (invℚ₊ (fromNat (suc n))))
            (ℚ.x·invℚ₊[x] (fromNat (suc n)))
              (ℚ.<-·o _ _ (fst (invℚ₊ (fromNat (suc n))))
                (ℚ.0<ℚ₊ (invℚ₊ (fromNat (suc n))))
                 (subst (fst (fromNat (suc n)) ℚ.<_)
                   (sym (ℚ.fromNat-^ (2 ℕ.+ Z) (suc n)))
                   (ℚ.<ℤ→<ℚ _ _ (invEq (ℤ.pos-<-pos≃ℕ< _ _) (ℕ.sn<ssm^sn n Z))))))
       (ℚ.decℚ<? {0} {1}) (ℚ.decℚ≤? {0} {1}))

pred0< : ℙ ℝ
pred0< = λ x → (0 <ᵣ x) , isProp<ᵣ _ _

pred1< : ℙ ℝ
pred1< = λ x → (1 <ᵣ x) , isProp<ᵣ _ _


opaque
 unfolding -ᵣ_ _+ᵣ_
 contBound : ∀ B → IsContinuousWithPred pred0< (curry (flip bound B))
 contBound B =
   IsContinuousWP∘ ⊤Pred _ _ _ _
     (AsContinuousWithPred _ _ (IsContinuous·ᵣR (rat (fst (invℚ₊ B)))))
     (contDiagNE₂WP sumR _
        _ _
          (IsContinuous^ℚ _)
           (IsContinuousWP∘ pred0< _ _ _
             (curry (snd ∘ (_^ℚ fst B))) (AsContinuousWithPred _ _  IsContinuous-ᵣ)
               (IsContinuous^ℚ _)))




-- module ExpSlopeBound (z : ℝ₊) (1<z : 1 <ᵣ fst z)  where
--  module _ (B : ℚ₊) where



--   ineqStrict : ∀ x y → y ℚ.≤ fst B → x ℚ.< y →
--            (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) <ᵣ
--               bound z B ·ᵣ rat (y ℚ.- x)
--   ineqStrict x y y≤B x<y =
--        isTrans<≡ᵣ _ _ _
--          (fst (z/y<x₊≃z<y₊·x _ _ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ x<y)))
--            (isTrans≤<ᵣ _ _ _
--              (slope-incr' z x x' y
--                (ℚ.≤max _ _) x'<y x<y)
--              (isTrans<≤ᵣ _ _ _
--                (<ᵣ-·ᵣo _ _ (invℝ₊ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ x' y x'<y)))
--                 (power-slope-Δ z 1<z x' y x'<y
--                (ℚ.<→ℚ₊ _ _ (ℚ.isTrans<≤  _ _ _ x'<y y≤B))))
--                (isTrans≡≤ᵣ _ _ _
--                  (cong₂ _／ᵣ₊_ (cong (λ v →
--                         fst (z ^ℚ (y ℚ.+ (fst B ℚ.- x'))) -ᵣ fst (z ^ℚ v))
--                        lem--05)
--                    (ℝ₊≡ (cong rat lem--078)))
--                  (isTrans≤≡ᵣ _ _ _
--                     (slope-incr z
--                       (fst B) (y ℚ.+ (fst B ℚ.- x')) (2 ℚ.· (fst B))
--                        (subst2 (ℚ._<_) (ℚ.+IdL (fst B))
--                          (sym (ℚ.+Assoc _ _ _)
--                          ∙ cong (y ℚ.+_) (ℚ.+Comm _ _))
--                          (ℚ.<-+o 0 _ (fst B) (ℚ.-< _ _ x'<y)))
--                        (subst2 ℚ._≤_
--                          ( sym (ℚ.+Assoc _ _ _)
--                          ∙ cong (y ℚ.+_) (ℚ.+Comm _ _)) (ℚ.x+x≡2x (fst B))
--                          (ℚ.≤-+o _ _ _ y-x'≤B))
--                        (subst (ℚ._< (2 ℚ.· fst B)) (ℚ.·IdL (fst B))
--                          (ℚ.<-·o _ _ (fst B) (ℚ.0<ℚ₊ B)
--                            (ℚ.decℚ<? {1} {2})))) ww)))))
--          (·ᵣComm _ _)

--     where
--     x' = ℚ.max x (y ℚ.- fst B)

--     x'<y : x' ℚ.< y
--     x'<y = ℚ.max< _ _ _ x<y (ℚ.<-ℚ₊' y y B (ℚ.isRefl≤ y ) )

--     y-x'≤B : y ℚ.- x' ℚ.≤ fst B
--     y-x'≤B = subst (y ℚ.- x' ℚ.≤_) lem--079
--      (ℚ.≤-o+ _ _ y
--      (ℚ.minus-≤ (y ℚ.- fst B) x' (ℚ.≤max' x (y ℚ.- fst B))))

--     ww' = (ℚ.<→ℚ₊ (fst B) (2 ℚ.· fst B)
--              (subst (ℚ._< 2 ℚ.· fst B) (ℚ.·IdL (fst B))
--               (ℚ.<-·o 1 2 (fst B) (ℚ.0<ℚ₊ B) ℚ.decℚ<?)))

--     ww : ((fst (z ^ℚ (2 ℚ.· fst B)) -ᵣ fst (z ^ℚ fst B)) ／ᵣ₊
--             (ℚ₊→ℝ₊ ww'))
--            ≡ ((fst (z ^ℚ (2 ℚ.· (fst B))) -ᵣ fst (z ^ℚ (fst B))) ·ᵣ
--      rat (fst (invℚ₊ B)))
--     ww =
--      cong ((fst (z ^ℚ (2 ℚ.· fst B)) -ᵣ fst (z ^ℚ fst B)) ·ᵣ_)
--        (invℝ'-rat _ (snd ww') (snd (ℚ₊→ℝ₊ ww')) ∙
--          cong (rat ∘ fst ∘ invℚ₊) (ℚ₊≡
--           (cong (ℚ._- (fst B)) (sym (ℚ.x+x≡2x (fst B)))
--            ∙ sym (lem--034 {fst B}))) )


--   ineqStrictInv : ∀ x y → (ℚ.- (fst B)) ℚ.≤ x → x ℚ.< y →
--                 (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat (y ℚ.- x) <ᵣ  (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x))
--   ineqStrictInv x y -B≤x x<y =
--      isTrans≡<ᵣ _ _ _ (·ᵣComm _ _)
--        (fst (z<x/y₊≃y₊·z<x _ _ _) w)
--     where

--     -2B<-B = (ℚ.minus-< _ _ (subst (ℚ._< 2 ℚ.· (fst B))
--                 (ℚ.·IdL (fst B)) (ℚ.<-·o 1 2 (fst B) (ℚ.0<ℚ₊ B)
--                   ℚ.decℚ<?)))

--     w : (-ᵣ (bound (invℝ₊ z) B))  <ᵣ  ((fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  x<y ))
--     w = isTrans≡<ᵣ _ _ _ (sym (-ᵣ· _ _) ∙
--        cong₂ _·ᵣ_ (-[x-y]≡y-x _ _ ∙ cong₂ _-ᵣ_
--                     (cong fst (cong (invℝ₊ z ^ℚ_) (sym (ℚ.-Invol _)) ∙ sym (^ℚ-minus _ _)))
--                     (cong fst (cong (invℝ₊ z ^ℚ_) (sym (ℚ.-Invol _)) ∙ sym (^ℚ-minus _ _))))
--                   (sym (invℝ₊-rat B)
--                    ∙ cong (fst ∘ invℝ₊ ∘ ℚ₊→ℝ₊)
--                      (ℚ₊≡ ((sym (ℚ.·IdL _) ∙ ℚ.·DistR+ 2 -1 (fst B))
--                       ∙ cong (ℚ._+ (ℚ.- fst B)) (sym (ℚ.-Invol _))
--                       ∙ ℚ.+Comm _ _))) )
--       (slope-monotone-strict z 1<z
--         (ℚ.- (2 ℚ.· fst B)) (ℚ.- (fst B))
--           x y -2B<-B x<y
--             (ℚ.isTrans≤ _ _ _ (ℚ.<Weaken≤ _ _ -2B<-B) -B≤x)
--             (ℚ.isTrans≤< _ _ _ -B≤x x<y))

--   ineq : ∀ x y → y ℚ.≤ fst B → x ℚ.≤ y →
--            (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
--               bound z B ·ᵣ rat (y ℚ.- x)
--   ineq x y y≤B = ⊎.rec
--     (λ x≡y → ≡ᵣWeaken≤ᵣ _ _
--       (𝐑'.+InvR' _ _ (cong (fst ∘ z ^ℚ_) (sym x≡y))
--         ∙∙ sym (𝐑'.0RightAnnihilates (bound z B)) ∙∙
--         cong (bound z B ·ᵣ_) (cong rat (sym (𝐐'.+InvR' _ _ (sym x≡y))))))
--     (<ᵣWeaken≤ᵣ _ _ ∘ ineqStrict x y y≤B )
--     ∘ ℚ.≤→≡⊎< x y



--   ineqInv : ∀ x y → (ℚ.- (fst B)) ℚ.≤ x → x ℚ.≤ y →
--                 (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat (y ℚ.- x) ≤ᵣ  (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x))
--   ineqInv x y -B≤x =
--     ⊎.rec
--       (λ x≡y → ≡ᵣWeaken≤ᵣ _ _
--          (cong (-ᵣ bound (invℝ₊ z) B ·ᵣ_) (cong rat (𝐐'.+InvR' y x (sym x≡y))) ∙∙
--            𝐑'.0RightAnnihilates (-ᵣ bound (invℝ₊ z) B) ∙∙
--             (sym (𝐑'.+InvR' (fst (z ^ℚ y)) (fst (z ^ℚ x))
--              (cong (fst ∘ (z ^ℚ_)) (sym x≡y))) )))
--       (<ᵣWeaken≤ᵣ _ _ ∘ ineqStrictInv x y -B≤x)
--      ∘ ℚ.≤→≡⊎< x y

--   opaque
--    unfolding -ᵣ_ absᵣ
--    ineq-abs : ∀ x y → x ℚ.≤ fst B → y ℚ.≤ fst B →
--             absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
--                bound z B ·ᵣ rat (ℚ.abs' (y ℚ.- x))
--    ineq-abs x y x≤B y≤B = w (ℚ.≡⊎# x y)

--     where
--     w : (x ≡ y) ⊎ (x ℚ.# y) → absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
--                bound z B ·ᵣ rat (ℚ.abs' (y ℚ.- x))
--     w (inl x≡y) =
--       ≡ᵣWeaken≤ᵣ _ _
--        (cong absᵣ (𝐑'.+InvR' _ _ (cong (fst ∘ z ^ℚ_) (sym x≡y)))
--          ∙∙ sym (𝐑'.0RightAnnihilates (bound z B)) ∙∙
--          cong (bound z B ·ᵣ_)
--           (cong (rat ∘ ℚ.abs') (sym (𝐐'.+InvR' _ _ (sym x≡y))))
--           )
--     w (inr (inl x<y)) = <ᵣWeaken≤ᵣ _ _ (isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
--           (absᵣNonNeg _ (x≤y→0≤y-x _ _ (^ℚ-MonotoneR x y
--              (ℚ.<Weaken≤ _ _ x<y)
--             (<ᵣWeaken≤ᵣ _ _ 1<z))))
--            (ineqStrict x y y≤B x<y))
--          (cong (bound z B ·ᵣ_)
--           (cong rat (sym (ℚ.absPos _ (ℚ.-< _ _ x<y)) ∙ ℚ.abs'≡abs _))))
--     w (inr (inr y<x)) =
--       <ᵣWeaken≤ᵣ _ _ (isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
--           (minusComm-absᵣ _ _ ∙
--            absᵣPos _ (x<y→0<y-x _ _ (^ℚ-StrictMonotoneR 1<z y x y<x)))
--            (ineqStrict y x x≤B y<x))
--          (cong (bound z B ·ᵣ_)
--           (cong rat ((sym (ℚ.-[x-y]≡y-x _ _) ∙ sym (ℚ.absNeg _
--             (subst ((y ℚ.- x) ℚ.<_)
--               (ℚ.+InvR _) (ℚ.<-+o _ _ (ℚ.- x) y<x)))) ∙ ℚ.abs'≡abs _))))

--   ineqInv-abs : ∀ x y → (ℚ.- (fst B)) ℚ.≤ x → (ℚ.- (fst B)) ℚ.≤ y →
--                 (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat (ℚ.abs (y ℚ.- x)) ≤ᵣ
--                     absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x))
--   ineqInv-abs = ℚ.elimBy≤ (λ x y X u v →
--     subst2 (λ a b → (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat a ≤ᵣ b)
--                     (ℚ.absComm- _ _) (minusComm-absᵣ _ _) (X v u))
--      λ x y x≤y x≤ _ →
--         subst2 (λ a b → (-ᵣ (bound (invℝ₊ z) B)) ·ᵣ rat a ≤ᵣ b)
--           (sym (ℚ.absNonNeg _ (ℚ.-≤ _ _ x≤y)))
--            (sym (absᵣNonNeg _ (x≤y→0≤y-x _ _ (^ℚ-MonotoneR _ _ x≤y (<ᵣWeaken≤ᵣ _ _ 1<z) ))))
--            (ineqInv x y x≤ x≤y)
