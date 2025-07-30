module Cubical.Categories.Instances.FunctorAlgebras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Univalence

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base

open _≅_

private
  variable ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (F : Functor C C) where

  open Category
  open Functor

  IsAlgebra : ob C → Type ℓC'
  IsAlgebra x = C [ F-ob F x , x ]

  record Algebra : Type (ℓ-max ℓC ℓC') where
    constructor algebra
    field
      carrier : ob C
      str : IsAlgebra carrier
  open Algebra

  IsAlgebraHom : (algA algB : Algebra) → C [ carrier algA , carrier algB ] → Type ℓC'
  IsAlgebraHom algA algB f = (f ∘⟨ C ⟩ str algA) ≡ (str algB ∘⟨ C ⟩ F-hom F f)

  record AlgebraHom (algA algB : Algebra) : Type ℓC' where
    constructor algebraHom
    field
      carrierHom : C [ carrier algA , carrier algB ]
      strHom : IsAlgebraHom algA algB carrierHom
  open AlgebraHom

  RepAlgebraHom : (algA algB : Algebra) → Type ℓC'
  RepAlgebraHom algA algB = Σ[ f ∈ C [ carrier algA , carrier algB ] ] IsAlgebraHom algA algB f

  isoRepAlgebraHom : (algA algB : Algebra) → AlgebraHom algA algB ≅ RepAlgebraHom algA algB
  fun (isoRepAlgebraHom algA algB) (algebraHom f isalgF) = f , isalgF
  inv (isoRepAlgebraHom algA algB) (f , isalgF) = algebraHom f isalgF
  rightInv (isoRepAlgebraHom algA algB) (f , isalgF) = refl
  leftInv (isoRepAlgebraHom algA algB) (algebraHom f isalgF)= refl

  pathRepAlgebraHom : (algA algB : Algebra) → AlgebraHom algA algB ≡ RepAlgebraHom algA algB
  pathRepAlgebraHom algA algB = ua (isoToEquiv (isoRepAlgebraHom algA algB))

  AlgebraHom≡ : {algA algB : Algebra} {algF algG : AlgebraHom algA algB}
    → (carrierHom algF ≡ carrierHom algG) → algF ≡ algG
  carrierHom (AlgebraHom≡ {algA} {algB} {algF} {algG} p i) = p i
  strHom (AlgebraHom≡ {algA} {algB} {algF} {algG} p i) = idfun
    (PathP (λ j → (p j ∘⟨ C ⟩ str algA) ≡ (str algB ∘⟨ C ⟩ F-hom F (p j)))
      (strHom algF)
      (strHom algG)
    )
    (fst (idfun (isContr _) (isOfHLevelPathP' 0
        (isOfHLevelPath' 1 (isSetHom C) _ _)
      (strHom algF) (strHom algG))))
    i

  idAlgebraHom : {algA : Algebra} → AlgebraHom algA algA
  carrierHom (idAlgebraHom {algA}) = id C
  strHom (idAlgebraHom {algA}) =
    ⋆IdR C (str algA) ∙∙ sym (⋆IdL C (str algA)) ∙∙ cong (λ φ → φ ⋆⟨ C ⟩ str algA) (sym (F-id F))

  seqAlgebraHom : {algA algB algC : Algebra}
    (algF : AlgebraHom algA algB) (algG : AlgebraHom algB algC)
    → AlgebraHom algA algC
  carrierHom (seqAlgebraHom {algA} {algB} {algC} algF algG) = carrierHom algF ⋆⟨ C ⟩ carrierHom algG
  strHom (seqAlgebraHom {algA} {algB} {algC} algF algG) =
    str algA ⋆⟨ C ⟩ (carrierHom algF ⋆⟨ C ⟩ carrierHom algG)
      ≡⟨ sym (⋆Assoc C (str algA) (carrierHom algF) (carrierHom algG)) ⟩
    (str algA ⋆⟨ C ⟩ carrierHom algF) ⋆⟨ C ⟩ carrierHom algG
      ≡⟨ cong (λ φ → φ ⋆⟨ C ⟩ carrierHom algG) (strHom algF) ⟩
    (F-hom F (carrierHom algF) ⋆⟨ C ⟩ str algB) ⋆⟨ C ⟩ carrierHom algG
      ≡⟨ ⋆Assoc C (F-hom F (carrierHom algF)) (str algB) (carrierHom algG) ⟩
    F-hom F (carrierHom algF) ⋆⟨ C ⟩ (str algB ⋆⟨ C ⟩ carrierHom algG)
      ≡⟨ cong (λ φ → F-hom F (carrierHom algF) ⋆⟨ C ⟩ φ) (strHom algG) ⟩
    F-hom F (carrierHom algF) ⋆⟨ C ⟩ (F-hom F (carrierHom algG) ⋆⟨ C ⟩ str algC)
      ≡⟨ sym (⋆Assoc C (F-hom F (carrierHom algF)) (F-hom F (carrierHom algG)) (str algC)) ⟩
    (F-hom F (carrierHom algF) ⋆⟨ C ⟩ F-hom F (carrierHom algG)) ⋆⟨ C ⟩ str algC
      ≡⟨ cong (λ φ → φ ⋆⟨ C ⟩ str algC) (sym (F-seq F (carrierHom algF) (carrierHom algG))) ⟩
    F-hom F (carrierHom algF ⋆⟨ C ⟩ carrierHom algG) ⋆⟨ C ⟩ str algC ∎

  AlgebrasCategory : Category (ℓ-max ℓC ℓC') ℓC'
  ob AlgebrasCategory = Algebra
  Hom[_,_] AlgebrasCategory = AlgebraHom
  id AlgebrasCategory = idAlgebraHom
  _⋆_ AlgebrasCategory = seqAlgebraHom
  ⋆IdL AlgebrasCategory algF = AlgebraHom≡ (⋆IdL C (carrierHom algF))
  ⋆IdR AlgebrasCategory algF = AlgebraHom≡ (⋆IdR C (carrierHom algF))
  ⋆Assoc AlgebrasCategory algF algG algH =
    AlgebraHom≡ (⋆Assoc C (carrierHom algF) (carrierHom algG) (carrierHom algH))
  isSetHom AlgebrasCategory = subst isSet (sym (pathRepAlgebraHom _ _))
    (isSetΣ (isSetHom C) (λ f → isProp→isSet (isSetHom C _ _)))

  ForgetAlgebra : Functor AlgebrasCategory C
  F-ob ForgetAlgebra = carrier
  F-hom ForgetAlgebra = carrierHom
  F-id ForgetAlgebra = refl
  F-seq ForgetAlgebra algF algG = refl

module _ {C : Category ℓC ℓC'} {F G : Functor C C} (τ : NatTrans F G) where

  private
    module C = Category C
  open Functor
  open NatTrans
  open AlgebraHom

  AlgebrasFunctor : Functor (AlgebrasCategory G) (AlgebrasCategory F)
  F-ob AlgebrasFunctor (algebra a α) = algebra a (α C.∘ N-ob τ a)
  carrierHom (F-hom AlgebrasFunctor (algebraHom f isalgF)) = f
  strHom (F-hom AlgebrasFunctor {algebra a α} {algebra b β} (algebraHom f isalgF)) =
    (N-ob τ a C.⋆ α) C.⋆ f
      ≡⟨ C.⋆Assoc (N-ob τ a) α f ⟩
    N-ob τ a C.⋆ (α C.⋆ f)
      ≡⟨ cong (N-ob τ a C.⋆_) isalgF ⟩
    N-ob τ a C.⋆ (F-hom G f C.⋆ β)
      ≡⟨ sym (C.⋆Assoc _ _ _) ⟩
    (N-ob τ a C.⋆ F-hom G f) C.⋆ β
      ≡⟨ cong (C._⋆ β) (sym (N-hom τ f)) ⟩
    (F-hom F f C.⋆ N-ob τ b) C.⋆ β
      ≡⟨ C.⋆Assoc _ _ _ ⟩
    F-hom F f C.⋆ (N-ob τ b C.⋆ β) ∎
  F-id AlgebrasFunctor = AlgebraHom≡ F refl
  F-seq AlgebrasFunctor algΦ algΨ = AlgebraHom≡ F refl
