module Cubical.Categories.Instances.FunctorAlgebras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (F : Functor C C) where

  open Category
  open Functor

  record Algebra : Type (ℓ-max ℓC ℓC') where
    constructor algebra
    field
      carrier : ob C
      str : C [ F-ob F carrier , carrier ]
  open Algebra

  record AlgebraHom (algA algB : Algebra) : Type ℓC' where
    constructor algebraHom
    field
      carrierHom : C [ carrier algA , carrier algB ]
      strHom : (carrierHom ∘⟨ C ⟩ str algA) ≡ (str algB ∘⟨ C ⟩ F-hom F carrierHom)
  open AlgebraHom

  AlgebraHom≡ : {algA algB : Algebra} {algF algG : AlgebraHom algA algB} → (carrierHom algF ≡ carrierHom algG) → algF ≡ algG
  carrierHom (AlgebraHom≡ {algA} {algB} {algF} {algG} p i) = p i
  strHom (AlgebraHom≡ {algA} {algB} {algF} {algG} p i) = idfun
    (PathP (λ j → (p j ∘⟨ C ⟩ str algA) ≡ (str algB ∘⟨ C ⟩ F-hom F (p j))) (strHom algF) (strHom algG))
    (fst (idfun (isContr _) (isOfHLevelPathP' 0
        (isOfHLevelPath' 1 (isSetHom C) _ _)
      (strHom algF) (strHom algG))))
    i

  idAlgebraHom : {algA : Algebra} → AlgebraHom algA algA
  carrierHom (idAlgebraHom {algA}) = id C
  strHom (idAlgebraHom {algA}) =
    ⋆IdR C (str algA) ∙∙ sym (⋆IdL C (str algA)) ∙∙ cong (λ φ → φ ⋆⟨ C ⟩ str algA) (sym (F-id F))

  seqAlgebraHom : {algA algB algC : Algebra} (algF : AlgebraHom algA algB) (algG : AlgebraHom algB algC) → AlgebraHom algA algC
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

  AlgebrasCategory : Category {!!} {!!}
  ob AlgebrasCategory = Algebra
  Hom[_,_] AlgebrasCategory = AlgebraHom
  id AlgebrasCategory = idAlgebraHom
  _⋆_ AlgebrasCategory = seqAlgebraHom
  ⋆IdL AlgebrasCategory algF = AlgebraHom≡ (⋆IdL C (carrierHom algF))
  ⋆IdR AlgebrasCategory algF = AlgebraHom≡ (⋆IdR C (carrierHom algF))
  ⋆Assoc AlgebrasCategory algF algG algH = AlgebraHom≡ (⋆Assoc C (carrierHom algF) (carrierHom algG) (carrierHom algH))
  isSetHom AlgebrasCategory algA algB p q = {!AlgebraHom≡!}
