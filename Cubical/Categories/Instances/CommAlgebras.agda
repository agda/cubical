{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.Instances.CommAlgebras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Pullback

open import Cubical.HITs.PropositionalTruncation

open Category
open CommAlgebraHoms

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
 open Cospan
 open Pullback
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
