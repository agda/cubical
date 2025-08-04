module Cubical.Algebra.CommAlgebra.AsModule.Instances.Pointwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.Pointwise
open import Cubical.Algebra.CommAlgebra.AsModule.Base
open import Cubical.Algebra.Algebra using (IsAlgebraHom)

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {R : CommRing ℓ} (X : Type ℓ'') (A : CommAlgebra R ℓ') where
  pointwiseAlgebra : CommAlgebra R _
  pointwiseAlgebra =
    let open CommAlgebraStr (snd A)
        isSetX→A = isOfHLevelΠ 2 (λ (x : X) → is-set)
    in commAlgebraFromCommRing
         (pointwiseRing X (CommAlgebra→CommRing A))
         (λ r f → (λ x → r ⋆ (f x)))
         (λ r s f i x → ⋆Assoc r s (f x) i)
         (λ r f g i x → ⋆DistR+ r (f x) (g x) i)
         (λ r s f i x → ⋆DistL+ r s (f x) i)
         (λ f i x → ⋆IdL (f x) i)
         λ r f g i x → ⋆AssocL r (f x) (g x) i

  open IsAlgebraHom

  evaluationHom : X → CommAlgebraHom pointwiseAlgebra A
  fst (evaluationHom x) f = f x
  pres0 (snd (evaluationHom x)) = refl
  pres1 (snd (evaluationHom x)) = refl
  pres+ (snd (evaluationHom x)) _ _ = refl
  pres· (snd (evaluationHom x)) _ _ = refl
  pres- (snd (evaluationHom x)) _ = refl
  pres⋆ (snd (evaluationHom x)) _ _ = refl
