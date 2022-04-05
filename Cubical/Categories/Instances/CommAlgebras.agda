{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.Instances.CommAlgebras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Instances.CommRings

open import Cubical.HITs.PropositionalTruncation

open Category hiding (_∘_) renaming (_⋆_ to _⋆c_)
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
  _⋆c_ CommAlgebrasCategory {A} {B} {C}     = compCommAlgebraHom A B C
  ⋆IdL CommAlgebrasCategory {A} {B}           = compIdCommAlgebraHom {A = A} {B}
  ⋆IdR CommAlgebrasCategory {A} {B}           = idCompCommAlgebraHom {A = A} {B}
  ⋆Assoc CommAlgebrasCategory {A} {B} {C} {D} = compAssocCommAlgebraHom {A = A} {B} {C} {D}
  isSetHom CommAlgebrasCategory               = isSetAlgebraHom _ _

  TerminalCommAlgebra : Terminal (CommAlgebrasCategory {ℓ' = ℓ'})
  fst TerminalCommAlgebra = UnitCommAlgebra R
  fst (fst (snd TerminalCommAlgebra A)) = λ _ → tt*
  snd (fst (snd TerminalCommAlgebra A)) = makeIsAlgebraHom
                                            refl (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)
  snd (snd TerminalCommAlgebra A) f = AlgebraHom≡ (funExt (λ _ → refl))

module PullbackFromCommRing (R : CommRing ℓ)
                            (commRingCospan : Cospan (CommRingsCategory {ℓ = ℓ}))
                            (commRingPB : Pullback _ commRingCospan)
                            (f₁ : CommRingHom R (commRingPB .pbOb))
                            (f₂ : CommRingHom R (commRingCospan .r))
                            (f₃ : CommRingHom R (commRingCospan .l))
                            (f₄ : CommRingHom R (commRingCospan .m))
                            where

 open AlgebraHoms
 open CommAlgChar R
 open CommAlgebraStr ⦃...⦄

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

 open RingHoms
 univPropCommRingWithHomHom : (isRHom₁ : isCommRingWithHomHom (A , f₁) (B , f₂) g₁)
                              (isRHom₂ : isCommRingWithHomHom (A , f₁) (C , f₃) g₂)
                              (isRHom₃ : isCommRingWithHomHom (B , f₂) (D , f₄) g₃)
                              (isRHom₄ : isCommRingWithHomHom (C , f₃) (D , f₄) g₄)
                              (E,f₅ : CommRingWithHom)
                              (h₂ : CommRingWithHomHom E,f₅ (C , f₃))
                              (h₁ : CommRingWithHomHom E,f₅ (B , f₂))
                            → g₄ ∘r fst h₂ ≡ g₃ ∘r fst h₁
                            → ∃![ h₃ ∈ CommRingWithHomHom E,f₅ (A , f₁) ]
                                 (fst h₂ ≡ g₂ ∘r fst h₃) × (fst h₁ ≡ g₁ ∘r fst h₃)
 univPropCommRingWithHomHom isRHom₁ isRHom₂ isRHom₃ isRHom₄
                             (E , f₅) (h₂ , comm₂) (h₁ , comm₁) squareComm =
    ((h₃ , h₃∘f₅≡f₁) , h₂≡g₂∘h₃ , h₁≡g₁∘h₃)
  , λ h₃' → Σ≡Prop (λ _ → isProp× (isSetRingHom _ _ _ _) (isSetRingHom _ _ _ _))
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
 univProp (algPullback isRHom₁ isRHom₂ isRHom₃ isRHom₄) {d = F} h₂' h₁' g₄∘h₂'≡g₃∘h₁' =
  (k , kComm₂ , kComm₁) , uniqueness
  where
  E = fromCommAlg F .fst
  f₅ = fromCommAlg F .snd

  h₁ : CommRingHom E B
  fst h₁ = fst h₁'
  IsRingHom.pres0 (snd h₁) = IsAlgebraHom.pres0 (snd h₁')
  IsRingHom.pres1 (snd h₁) = IsAlgebraHom.pres1 (snd h₁')
  IsRingHom.pres+ (snd h₁) = IsAlgebraHom.pres+ (snd h₁')
  IsRingHom.pres· (snd h₁) = IsAlgebraHom.pres· (snd h₁')
  IsRingHom.pres- (snd h₁) = IsAlgebraHom.pres- (snd h₁')

  h₁comm : h₁ ∘r f₅ ≡ f₂
  h₁comm = RingHom≡ (funExt (λ x → IsAlgebraHom.pres⋆ (snd h₁') x 1a
                                      ∙∙ cong (fst f₂ x ·_) (IsAlgebraHom.pres1 (snd h₁'))
                                      ∙∙ ·Rid _))
   where
   instance
    _ = snd F
    _ = snd (toCommAlg (B , f₂))

  h₂ : CommRingHom E C
  fst h₂ = fst h₂'
  IsRingHom.pres0 (snd h₂) = IsAlgebraHom.pres0 (snd h₂')
  IsRingHom.pres1 (snd h₂) = IsAlgebraHom.pres1 (snd h₂')
  IsRingHom.pres+ (snd h₂) = IsAlgebraHom.pres+ (snd h₂')
  IsRingHom.pres· (snd h₂) = IsAlgebraHom.pres· (snd h₂')
  IsRingHom.pres- (snd h₂) = IsAlgebraHom.pres- (snd h₂')

  h₂comm : h₂ ∘r f₅ ≡ f₃
  h₂comm = RingHom≡ (funExt (λ x → IsAlgebraHom.pres⋆ (snd h₂') x 1a
                                      ∙∙ cong (fst f₃ x ·_) (IsAlgebraHom.pres1 (snd h₂'))
                                      ∙∙ ·Rid _))
   where
   instance
    _ = snd F
    _ = snd (toCommAlg (C , f₃))

  commRingSquare : g₄ ∘r h₂ ≡ g₃ ∘r h₁
  commRingSquare = RingHom≡ (funExt (λ x → funExt⁻ (cong fst g₄∘h₂'≡g₃∘h₁') x))

  uniqueH₃ : ∃![ h₃ ∈ CommRingWithHomHom (E , f₅) (A , f₁) ] (h₂ ≡ g₂ ∘r fst h₃) × (h₁ ≡ g₁ ∘r fst h₃)
  uniqueH₃ = univPropCommRingWithHomHom isRHom₁ isRHom₂ isRHom₃ isRHom₄
                                          (E , f₅) (h₂ , h₂comm) (h₁ , h₁comm) commRingSquare

  h₃ : CommRingHom E A
  h₃ = uniqueH₃ .fst .fst .fst

  h₃comm = uniqueH₃ .fst .fst .snd

  k : CommAlgebraHom F (toCommAlg (A , f₁))
  fst k = fst h₃
  IsAlgebraHom.pres0 (snd k) = IsRingHom.pres0 (snd h₃)
  IsAlgebraHom.pres1 (snd k) = IsRingHom.pres1 (snd h₃)
  IsAlgebraHom.pres+ (snd k) = IsRingHom.pres+ (snd h₃)
  IsAlgebraHom.pres· (snd k) = IsRingHom.pres· (snd h₃)
  IsAlgebraHom.pres- (snd k) = IsRingHom.pres- (snd h₃)
  IsAlgebraHom.pres⋆ (snd k) =
    λ r y → sym (fst f₁ r · fst h₃ y ≡⟨ cong (_· fst h₃ y) (sym (funExt⁻ (cong fst h₃comm) r)) ⟩
                 fst h₃ (fst f₅ r) · fst h₃ y ≡⟨ sym (IsRingHom.pres· (snd h₃) _ _) ⟩
                 fst h₃ (fst f₅ r · y) ≡⟨ refl ⟩
                 fst h₃ ((r ⋆ 1a) · y) ≡⟨ cong (fst h₃) (⋆-lassoc _ _ _) ⟩
                 fst h₃ (r ⋆ (1a · y)) ≡⟨ cong (λ x → fst h₃ (r ⋆ x)) (·Lid y) ⟩
                 fst h₃ (r ⋆ y) ∎)
   where
   instance
    _ = snd F
    _ = (toCommAlg (A , f₁) .snd)

  kComm₂ : h₂' ≡ toCommAlgebraHom _ _ g₂ isRHom₂ ∘a k
  kComm₂ = AlgebraHom≡ (cong fst (uniqueH₃ .fst .snd .fst))

  kComm₁ : h₁' ≡ toCommAlgebraHom _ _ g₁ isRHom₁ ∘a k
  kComm₁ = AlgebraHom≡ (cong fst (uniqueH₃ .fst .snd .snd))

  uniqueness : (y : Σ[ k' ∈ CommAlgebraHom F (toCommAlg (A , f₁)) ]
                       (h₂' ≡ toCommAlgebraHom _ _ g₂ isRHom₂ ∘a k')
                     × (h₁' ≡ toCommAlgebraHom _ _ g₁ isRHom₁ ∘a k'))
             → (k , kComm₂ , kComm₁) ≡ y
  uniqueness (k' , k'Comm₂ , k'Comm₁) = Σ≡Prop (λ _ → isProp× (isSetAlgebraHom _ _ _ _)
                                                              (isSetAlgebraHom _ _ _ _))
                                               (AlgebraHom≡ (cong (fst ∘ fst ∘ fst) uniqHelper))
   where
   h₃' : CommRingHom E A
   fst h₃' = fst k'
   IsRingHom.pres0 (snd h₃') = IsAlgebraHom.pres0 (snd k')
   IsRingHom.pres1 (snd h₃') = IsAlgebraHom.pres1 (snd k')
   IsRingHom.pres+ (snd h₃') = IsAlgebraHom.pres+ (snd k')
   IsRingHom.pres· (snd h₃') = IsAlgebraHom.pres· (snd k')
   IsRingHom.pres- (snd h₃') = IsAlgebraHom.pres- (snd k')

   h₃'IsRHom : h₃' ∘r f₅ ≡ f₁
   h₃'IsRHom = RingHom≡ (funExt (λ x → IsAlgebraHom.pres⋆ (snd k') x 1a
                                     ∙ cong (fst f₁ x ·_) (IsAlgebraHom.pres1 (snd k'))
                                     ∙ ·Rid (fst f₁ x)))
    where
    instance
     _ = snd F
     _ = (toCommAlg (A , f₁) .snd)

   h₃'Comm₂ : h₂ ≡ g₂ ∘r h₃'
   h₃'Comm₂ = RingHom≡ (cong fst k'Comm₂)

   h₃'Comm₁ : h₁ ≡ g₁ ∘r h₃'
   h₃'Comm₁ = RingHom≡ (cong fst k'Comm₁)

   -- basically saying that h₃≡h₃' but we have to give all the commuting triangles
   uniqHelper : uniqueH₃ .fst ≡ ((h₃' , h₃'IsRHom) , h₃'Comm₂ , h₃'Comm₁)
   uniqHelper = uniqueH₃ .snd ((h₃' , h₃'IsRHom) , h₃'Comm₂ , h₃'Comm₁)



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
 module toSheaf (x y u v : ob ΣC∥P∥Cat)
                {f : C [ v .fst , y . fst ]} {g : C [ v .fst , u .fst ]}
                {h : C [ u .fst , x . fst ]} {k : C [ y .fst , x .fst ]}
                (Csquare : g ⋆⟨ C ⟩ h ≡ f ⋆⟨ C ⟩ k)
                {-
                    v → y
                    ↓   ↓
                    u → x
                -}
                (AlgCospan : Cospan CommAlgCat)
                (AlgPB : Pullback _ AlgCospan)
                (p₁ : AlgPB .pbOb ≡ F-ob universalPShf x) (p₂ : AlgCospan .l ≡ F-ob universalPShf u)
                (p₃ : AlgCospan .r ≡ F-ob universalPShf y) (p₄ : AlgCospan .m ≡ F-ob universalPShf v)
                where

  private
   -- just: 𝓕 k ⋆ 𝓕 f ≡ 𝓕 h ⋆ 𝓕 g
   inducedSquare : seq' CommAlgCat {x = F-ob universalPShf x}
                                   {y = F-ob universalPShf u}
                                   {z = F-ob universalPShf v}
                                   (F-hom universalPShf h) (F-hom universalPShf g)
                 ≡ seq' CommAlgCat {x = F-ob universalPShf x}
                                   {y = F-ob universalPShf y}
                                   {z = F-ob universalPShf v}
                                   (F-hom universalPShf k) (F-hom universalPShf f)
   inducedSquare = F-square universalPShf Csquare

   f' = F-hom universalPShf {x = y} {y = v} f
   g' = F-hom universalPShf {x = u} {y = v} g
   h' = F-hom universalPShf {x = x} {y = u} h
   k' = F-hom universalPShf {x = x} {y = y} k

   gPathP : PathP (λ i → CommAlgCat [ p₂ i , p₄ i ]) (AlgCospan .s₁) g'
   gPathP = toPathP (sym (theAction _ _ g (v .snd) (u .snd) .snd _))

   fPathP : PathP (λ i → CommAlgCat [ p₃ i , p₄ i ]) (AlgCospan .s₂) f'
   fPathP = toPathP (sym (theAction _ _ f (v .snd) (y .snd) .snd _))

   kPathP : PathP (λ i → CommAlgCat [ p₁ i , p₃ i ]) (AlgPB .pbPr₂) k'
   kPathP = toPathP (sym (theAction _ _ k (y .snd) (x .snd) .snd _))

   hPathP : PathP (λ i → CommAlgCat [ p₁ i , p₂ i ]) (AlgPB .pbPr₁) h'
   hPathP = toPathP (sym (theAction _ _ h (u .snd) (x .snd) .snd _))

   fgCospan : Cospan CommAlgCat
   l fgCospan = F-ob universalPShf u
   m fgCospan = F-ob universalPShf v
   r fgCospan = F-ob universalPShf y
   s₁ fgCospan = g'
   s₂ fgCospan = f'

   cospanPath : AlgCospan ≡ fgCospan
   l (cospanPath i) = p₂ i
   m (cospanPath i) = p₄ i
   r (cospanPath i) = p₃ i
   s₁ (cospanPath i) = gPathP i
   s₂ (cospanPath i) = fPathP i

   squarePathP : PathP (λ i → hPathP i ⋆⟨ CommAlgCat ⟩ gPathP i ≡ kPathP i ⋆⟨ CommAlgCat ⟩ fPathP i)
                      (AlgPB .pbCommutes) inducedSquare
   squarePathP = toPathP (CommAlgCat .isSetHom _ _ _ _)

  abstract
   lemma : isPullback CommAlgCat fgCospan {c = F-ob universalPShf x} h' k' inducedSquare
   lemma = transport (λ i → isPullback CommAlgCat (cospanPath i) {c = p₁ i}
                                                  (hPathP i) (kPathP i) (squarePathP i))
                     (AlgPB .univProp)
