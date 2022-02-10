{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.Instances.CommAlgebras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Instances.CommRings

open import Cubical.HITs.PropositionalTruncation

open Category
open CommAlgebraHoms
open Cospan
open Pullback

private
 variable
  ℓ ℓ' ℓ'' : Level

module _ (R : CommRing ℓ) where
  CommAlgebrasCategory : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  ob CommAlgebrasCategory       = CommAlgebra R _
  Hom[_,_] CommAlgebrasCategory = CommAlgebraHom
  id CommAlgebrasCategory {A}   = idCommAlgebraHom A
  _⋆_ CommAlgebrasCategory {A} {B} {C}     = compCommAlgebraHom A B C
  ⋆IdL CommAlgebrasCategory {A} {B}           = compIdCommAlgebraHom {A = A} {B}
  ⋆IdR CommAlgebrasCategory {A} {B}           = idCompCommAlgebraHom {A = A} {B}
  ⋆Assoc CommAlgebrasCategory {A} {B} {C} {D} = compAssocCommAlgebraHom {A = A} {B} {C} {D}
  isSetHom CommAlgebrasCategory               = isSetAlgebraHom _ _


module PullbackFromCommRing (R : CommRing ℓ)
                            (commRingCospan : Cospan (CommRingsCategory {ℓ = ℓ}))
                            (commRingPB : Pullback _ commRingCospan)
                            (f₁ : CommRingHom R (commRingPB .pbOb))
                            (f₂ : CommRingHom R (commRingCospan .r))
                            (f₃ : CommRingHom R (commRingCospan .l))
                            (f₄ : CommRingHom R (commRingCospan .m))
                            where

 open CommAlgChar R
 private
  CommAlgCat = CommAlgebrasCategory {ℓ = ℓ} R {ℓ' = ℓ}

  A = commRingPB .pbOb
  B = commRingCospan .r
  C = commRingCospan .l
  D = commRingCospan .m

  g₁ = commRingPB .pbPr₂
  g₂ = commRingPB .pbPr₁
  g₃ = commRingCospan .s₂
  g₄ = commRingCospan .s₁

  {-
              g₁
           A  →  B
             ⌟
        g₂ ↓     ↓ g₃

           C  →  D
              g₄
  -}


 algCospan : (isRHom₁ : isCommRingWithHomHom (A , f₁) (B , f₂) g₁)
             (isRHom₂ : isCommRingWithHomHom (A , f₁) (C , f₃) g₂)
             (isRHom₃ : isCommRingWithHomHom (B , f₂) (D , f₄) g₃)
             (isRHom₄ : isCommRingWithHomHom (C , f₃) (D , f₄) g₄)
           → Cospan CommAlgCat
 l (algCospan isRHom₁ isRHom₂ isRHom₃ isRHom₄) = toCommAlg (C , f₃)
 m (algCospan isRHom₁ isRHom₂ isRHom₃ isRHom₄) = toCommAlg (D , f₄)
 r (algCospan isRHom₁ isRHom₂ isRHom₃ isRHom₄) = toCommAlg (B , f₂)
 s₁ (algCospan isRHom₁ isRHom₂ isRHom₃ isRHom₄) = toCommAlgebraHom _ _ g₄ isRHom₄
 s₂ (algCospan isRHom₁ isRHom₂ isRHom₃ isRHom₄) = toCommAlgebraHom _ _ g₃ isRHom₃


 algPullback : (isRHom₁ : isCommRingWithHomHom (A , f₁) (B , f₂) g₁)
               (isRHom₂ : isCommRingWithHomHom (A , f₁) (C , f₃) g₂)
               (isRHom₃ : isCommRingWithHomHom (B , f₂) (D , f₄) g₃)
               (isRHom₄ : isCommRingWithHomHom (C , f₃) (D , f₄) g₄)
             → Pullback CommAlgCat (algCospan isRHom₁ isRHom₂ isRHom₃ isRHom₄)
 pbOb (algPullback isRHom₁ isRHom₂ isRHom₃ isRHom₄) = toCommAlg (A , f₁)
 pbPr₁ (algPullback isRHom₁ isRHom₂ isRHom₃ isRHom₄) = toCommAlgebraHom _ _ g₂ isRHom₂
 pbPr₂ (algPullback isRHom₁ isRHom₂ isRHom₃ isRHom₄) = toCommAlgebraHom _ _ g₁ isRHom₁
 pbCommutes (algPullback isRHom₁ isRHom₂ isRHom₃ isRHom₄) =
               AlgebraHom≡ (cong fst (pbCommutes commRingPB))
 univProp (algPullback isRHom₁ isRHom₂ isRHom₃ isRHom₄) {d = F} h₂ h₁ g₄∘h₂≡g₃∘h₁ = (k , {!!}) , {!!}
  where
  open RingHoms
  univPropCommRingWithHomHom : (E,f₅ : CommRingWithHom)
                               (h₂ : CommRingWithHomHom E,f₅ (C , f₃))
                               (h₁ : CommRingWithHomHom E,f₅ (B , f₂))
                             → g₄ ∘r fst h₂ ≡ g₃ ∘r fst h₁
                             → ∃![ h₃ ∈ CommRingWithHomHom E,f₅ (A , f₁) ]
                                  (fst h₂ ≡ g₂ ∘r fst h₃) × (fst h₁ ≡ g₁ ∘r fst h₃)
  univPropCommRingWithHomHom (E , f₅) (h₂ , comm₂) (h₁ , comm₁) squareComm =
   ((h₃ , h₃∘f₅≡f₁) , h₂≡g₂∘h₃ , h₁≡g₁∘h₃) , λ h₃' → Σ≡Prop (λ _ → isProp× (isSetRingHom _ _ _ _) (isSetRingHom _ _ _ _))
                                                       (Σ≡Prop (λ _ → isSetRingHom _ _ _ _)
                                                         (cong fst (commRingPB .univProp h₂ h₁ squareComm .snd
                                                           (h₃' .fst .fst , h₃' .snd .fst , h₃' .snd .snd))))
   where
   h₃ : CommRingHom E A
   h₃ = commRingPB .univProp h₂ h₁ squareComm .fst .fst
   h₂≡g₂∘h₃ : h₂ ≡ g₂ ∘r h₃
   h₂≡g₂∘h₃ = commRingPB .univProp h₂ h₁ squareComm .fst .snd .fst
   h₁≡g₁∘h₃ : h₁ ≡ g₁ ∘r h₃
   h₁≡g₁∘h₃ = commRingPB .univProp h₂ h₁ squareComm .fst .snd .snd

   -- the crucial obervation:
   -- we can apply the universal property to maps R → A
   fgSquare : g₄ ∘r f₃ ≡ g₃ ∘r f₂
   fgSquare = isRHom₄ ∙ sym isRHom₃

   h₃∘f₅≡f₁ : h₃ ∘r f₅ ≡ f₁
   h₃∘f₅≡f₁ = cong fst (isContr→isProp (commRingPB .univProp f₃ f₂ fgSquare)
                         (h₃ ∘r f₅ , triangle1 , triangle2) (f₁ , (sym isRHom₂) , sym isRHom₁))
     where
     triangle1 : f₃ ≡ g₂ ∘r (h₃ ∘r f₅)
     triangle1 = sym comm₂ ∙∙ cong (compRingHom f₅) h₂≡g₂∘h₃ ∙∙ sym (compAssocRingHom f₅ h₃ g₂)

     triangle2 : f₂ ≡ g₁ ∘r (h₃ ∘r f₅)
     triangle2 = sym comm₁ ∙∙ cong (compRingHom f₅) h₁≡g₁∘h₃ ∙∙ sym (compAssocRingHom f₅ h₃ g₁)


  E = fromCommAlg F .fst
  f₅ = fromCommAlg F .snd

  k : CommAlgebraHom F (toCommAlg (A , f₁))
  k = {!!}




module PreSheafFromUniversalProp (C : Category ℓ ℓ') (P : ob C → Type ℓ)
         {R : CommRing ℓ''} (𝓕 : Σ (ob C) P → CommAlgebra R ℓ'')
         (uniqueHom : ∀ x y → C [ fst x , fst y ] → isContr (CommAlgebraHom (𝓕 y) (𝓕 x)))
         where

 private
  ∥P∥ : ℙ (ob C)
  ∥P∥ x  = ∥ P x ∥ , isPropPropTrunc
  ΣC∥P∥Cat = ΣPropCat C ∥P∥
  CommAlgCat = CommAlgebrasCategory {ℓ = ℓ''} R {ℓ' = ℓ''}

 𝓕UniqueEquiv : (x : ob C) (p q : P x) → isContr (CommAlgebraEquiv (𝓕 (x , p)) (𝓕 (x , q)))
 𝓕UniqueEquiv x = contrCommAlgebraHom→contrCommAlgebraEquiv (curry 𝓕 x) λ p q → uniqueHom _ _ (id C)

 theMap : (x : ob C) → ∥ P x ∥ → CommAlgebra R ℓ''
 theMap x = recPT→CommAlgebra (curry 𝓕 x) (λ p q → 𝓕UniqueEquiv x p q .fst)
                                         λ p q r → 𝓕UniqueEquiv x p r .snd _

 theAction : (x y : ob C) → C [ x , y ]
           → (p : ∥ P x ∥) (q : ∥ P y ∥) → isContr (CommAlgebraHom (theMap y q) (theMap x p))
 theAction _ _ f = elim2 (λ _ _ → isPropIsContr) λ _ _ → uniqueHom _ _ f

 open Functor
 universalPShf : Functor (ΣC∥P∥Cat ^op) CommAlgCat
 F-ob universalPShf = uncurry theMap
 F-hom universalPShf {x = x} {y = y} f = theAction _ _ f (y .snd) (x. snd) .fst
 F-id universalPShf {x = x} = theAction (x .fst) (x .fst) (id C) (x .snd) (x .snd) .snd _
 F-seq universalPShf {x = x} {z = z} f g = theAction _ _ (g ⋆⟨ C ⟩ f) (z .snd) (x .snd) .snd _


 -- a big transport to help verifying the sheaf property
 module toSheaf {x y u v : ob ΣC∥P∥Cat}
                {f : C [ v .fst , y . fst ]} {g : C [ v .fst , u .fst ]}
                {h : C [ u .fst , x . fst ]} {k : C [ y .fst , x .fst ]}
                (Csquare : f ⋆⟨ C ⟩ k ≡ g ⋆⟨ C ⟩ h)
                {-
                    v → y
                    ↓   ↓
                    u → x
                -}
                (AlgCospan : Cospan CommAlgCat)
                (AlgPB : Pullback _ AlgCospan)
                (p₁ : AlgPB .pbOb ≡ F-ob universalPShf x) (p₂ : AlgCospan .l ≡ F-ob universalPShf y)
                (p₃ : AlgCospan .r ≡ F-ob universalPShf u) (p₄ : AlgCospan .m ≡ F-ob universalPShf v)
                where

  private
   -- just: 𝓕 k ⋆ 𝓕 f ≡ 𝓕 h ⋆ 𝓕 g
   inducedSquare : seq' CommAlgCat {x = F-ob universalPShf x}
                                   {y = F-ob universalPShf y}
                                   {z = F-ob universalPShf v}
                                   (F-hom universalPShf k) (F-hom universalPShf f)
                 ≡ seq' CommAlgCat {x = F-ob universalPShf x}
                                   {y = F-ob universalPShf u}
                                   {z = F-ob universalPShf v}
                                   (F-hom universalPShf h) (F-hom universalPShf g)
   inducedSquare = F-square universalPShf Csquare

   f' = F-hom universalPShf {x = y} {y = v} f
   g' = F-hom universalPShf {x = u} {y = v} g
   h' = F-hom universalPShf {x = x} {y = u} h
   k' = F-hom universalPShf {x = x} {y = y} k

   fPathP : PathP (λ i → CommAlgCat [ p₂ i , p₄ i ]) (AlgCospan .s₁) f'
   fPathP = toPathP (sym (theAction _ _ f (v .snd) (y .snd) .snd _))

   gPathP : PathP (λ i → CommAlgCat [ p₃ i , p₄ i ]) (AlgCospan .s₂) g'
   gPathP = toPathP (sym (theAction _ _ g (v .snd) (u .snd) .snd _))

   hPathP : PathP (λ i → CommAlgCat [ p₁ i , p₃ i ]) (AlgPB .pbPr₂) h'
   hPathP = toPathP (sym (theAction _ _ h (u .snd) (x .snd) .snd _))

   kPathP : PathP (λ i → CommAlgCat [ p₁ i , p₂ i ]) (AlgPB .pbPr₁) k'
   kPathP = toPathP (sym (theAction _ _ k (y .snd) (x .snd) .snd _))

   fgCospan : Cospan CommAlgCat
   l fgCospan = F-ob universalPShf y
   m fgCospan = F-ob universalPShf v
   r fgCospan = F-ob universalPShf u
   s₁ fgCospan = f'
   s₂ fgCospan = g'

   cospanPath : AlgCospan ≡ fgCospan
   l (cospanPath i) = p₂ i
   m (cospanPath i) = p₄ i
   r (cospanPath i) = p₃ i
   s₁ (cospanPath i) = fPathP i
   s₂ (cospanPath i) = gPathP i

   squarePathP : PathP (λ i → kPathP i ⋆⟨ CommAlgCat ⟩ fPathP i ≡ hPathP i ⋆⟨ CommAlgCat ⟩ gPathP i)
                      (AlgPB .pbCommutes) inducedSquare
   squarePathP = toPathP (CommAlgCat .isSetHom _ _ _ _)

  lemma : isPullback CommAlgCat fgCospan {c = F-ob universalPShf x} k' h' inducedSquare
  lemma = transport (λ i → isPullback CommAlgCat (cospanPath i) {c = p₁ i}
                                                 (kPathP i) (hPathP i) (squarePathP i))
                    (AlgPB .univProp)
