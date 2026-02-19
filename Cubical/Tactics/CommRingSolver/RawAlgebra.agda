module Cubical.Tactics.CommRingSolver.RawAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Tactics.CommRingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)

private
  variable
    ℓ ℓ' : Level

record RawAlgebra (R : RawRing ℓ) (ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  constructor rawalgebra

  field
    Carrier : Type ℓ'
    scalar  : ⟨ R ⟩ᵣ → Carrier
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

  infixl 8 _·_
  infixl 7 -_
  infixl 6 _+_

⟨_⟩ : {R : RawRing ℓ} → RawAlgebra R ℓ' → Type ℓ'
⟨_⟩ = RawAlgebra.Carrier
