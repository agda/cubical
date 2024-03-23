{-# OPTIONS --safe #-}

{-
This file contians a proof that the smash product turns the universe
of pointed types into a symmetric monoidal wild category. The pentagon
and hexagon are proved in separate files due to the length of the
proofs. The remaining identities and the main result are proved here.
-}

module Cubical.HITs.SmashProduct.SymmetricMonoidalCat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Data.Bool
open import Cubical.HITs.SmashProduct.Base
open import Cubical.HITs.SmashProduct.Pentagon
open import Cubical.HITs.SmashProduct.Hexagon
open import Cubical.HITs.SmashProduct.SymmetricMonoidal

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product
open import Cubical.WildCat.BraidedSymmetricMonoidal
open import Cubical.WildCat.Instances.Pointed

open WildCat
open WildFunctor
open isSymmetricWildCat
open isMonoidalWildCat
open WildNatIso
open WildNatTrans
open wildIsIso

private
  variable
    ℓ ℓ' : Level

-- ⋀ as a functor
⋀F : ∀ {ℓ} → WildFunctor (PointedCat ℓ × PointedCat ℓ) (PointedCat ℓ)
F-ob ⋀F (A , B) = A ⋀∙ B
F-hom ⋀F (f , g) = f ⋀→∙ g
F-id ⋀F = ⋀→∙-idfun
F-seq ⋀F (f , g) (f' , g') = ⋀→∙-comp f f' g g'

⋀lUnitNatIso : WildNatIso (PointedCat ℓ) (PointedCat ℓ)
      (restrFunctorₗ ⋀F Bool*∙) (idWildFunctor (PointedCat ℓ))
N-ob (trans ⋀lUnitNatIso) X = ≃∙map ⋀lIdEquiv∙
N-hom (trans ⋀lUnitNatIso) f = ⋀lId-sq f
inv' (isIs ⋀lUnitNatIso c) = ≃∙map (invEquiv∙ ⋀lIdEquiv∙)
sect (isIs (⋀lUnitNatIso {ℓ = ℓ}) c) =
  ≃∙→ret/sec∙ (⋀lIdEquiv∙ {ℓ = ℓ} {A = c}) .snd
retr (isIs ⋀lUnitNatIso c) =
  ≃∙→ret/sec∙ ⋀lIdEquiv∙ .fst

makeIsIso-Pointed : ∀ {ℓ} {A B : Pointed ℓ} {f : A →∙ B}
  → isEquiv (fst f) → wildIsIso {C = PointedCat ℓ} f
inv' (makeIsIso-Pointed {f = f} eq) = ≃∙map (invEquiv∙ ((fst f , eq) , snd f))
sect (makeIsIso-Pointed {f = f} eq) = ≃∙→ret/sec∙ ((fst f , eq) , snd f)  .snd
retr (makeIsIso-Pointed {f = f} eq) = ≃∙→ret/sec∙ ((fst f , eq) , snd f)  .fst

restrₗᵣ : WildNatIso (PointedCat ℓ) (PointedCat ℓ)
      (restrFunctorᵣ ⋀F Bool*∙) (restrFunctorₗ ⋀F Bool*∙)
N-ob (trans restrₗᵣ) X = ⋀comm→∙
N-hom (trans restrₗᵣ) f = ⋀comm-sq f (idfun∙ Bool*∙)
isIs restrₗᵣ c = makeIsIso-Pointed (isoToIsEquiv ⋀CommIso)

-- main result
⋀Symm : ∀ {ℓ} → isSymmetricWildCat (PointedCat ℓ)
_⊗_ (isMonoidal ⋀Symm) = ⋀F
𝟙 (isMonoidal ⋀Symm) = Bool*∙
N-ob (trans (⊗assoc (isMonoidal ⋀Symm))) (A , B , C) = ≃∙map SmashAssocEquiv∙
N-hom (trans (⊗assoc (isMonoidal ⋀Symm))) (f , g , h) = ⋀assoc-⋀→∙ f g h
inv' (isIs (⊗assoc (isMonoidal ⋀Symm)) (A , B , C)) =
  ≃∙map (invEquiv∙ SmashAssocEquiv∙)
sect (isIs (⊗assoc (isMonoidal ⋀Symm)) (A , B , C)) =
  ≃∙→ret/sec∙ SmashAssocEquiv∙ .snd
retr (isIs (⊗assoc (isMonoidal ⋀Symm)) (A , B , C)) =
  ≃∙→ret/sec∙ SmashAssocEquiv∙ .fst
⊗lUnit (isMonoidal ⋀Symm) = ⋀lUnitNatIso
⊗rUnit (isMonoidal ⋀Symm) = compWildNatIso _ _ _ restrₗᵣ ⋀lUnitNatIso
triang (isMonoidal (⋀Symm {ℓ})) X Y = ⋀triang
⊗pentagon (isMonoidal ⋀Symm) X Y Z W =
  (∘∙-assoc assc₅∙ assc₄∙ assc₃∙) ∙ pentagon∙
N-ob (trans (Braid ⋀Symm)) X = ⋀comm→∙
N-hom (trans (Braid ⋀Symm)) (f , g) = ⋀comm-sq f g
isIs (Braid ⋀Symm) _ = makeIsIso-Pointed (isoToIsEquiv ⋀CommIso)
isSymmetricWildCat.hexagon ⋀Symm a b c = hexagon∙
symBraiding ⋀Symm X Y =
  ΣPathP ((funExt (Iso.rightInv ⋀CommIso)) , (sym (rUnit refl)))
