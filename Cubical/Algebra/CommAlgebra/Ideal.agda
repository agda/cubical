{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Ideal where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal renaming (IdealsIn to IdealsInCommRing;
                                                     makeIdeal to makeIdealCommRing)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.Ring

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  IdealsIn : Type _
  IdealsIn = IdealsInCommRing (CommAlgebra→CommRing A)

  open CommAlgebraStr (snd A)

  makeIdeal : (I : fst A → hProp ℓ)
              → (+-closed : {x y : fst A} → x ∈ I → y ∈ I → (x + y) ∈ I)
              → (0-closed : 0a ∈ I)
              → (·-closedLeft : {x : fst A} → (r : fst A) → x ∈ I → r · x ∈ I)
              → IdealsIn
  makeIdeal = makeIdealCommRing {R = CommAlgebra→CommRing A}

  zeroIdeal : IdealsIn
  fst zeroIdeal = λ x → (x ≡ 0a) , (isSetCommAlgebra A x 0a)
  CommIdeal.isCommIdeal.+Closed (snd zeroIdeal) = λ x≡0 y≡0 →  _ + _      ≡[ i ]⟨ x≡0 i + y≡0 i ⟩
                                                               0a + 0a    ≡⟨ +-rid 0a ⟩
                                                               0a ∎
  CommIdeal.isCommIdeal.contains0 (snd zeroIdeal) = refl
  CommIdeal.isCommIdeal.·Closed (snd zeroIdeal) =
    let open RingTheory (CommAlgebra→Ring A)
    in λ r x≡0 → r · _ ≡⟨ cong (λ u → r · u) x≡0 ⟩ r · 0a ≡⟨ 0RightAnnihilates _ ⟩ 0a ∎
