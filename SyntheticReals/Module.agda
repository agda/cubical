{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Module where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Structures.Ring
open import Cubical.Structures.Group
open import Cubical.Structures.AbGroup

open import NumberBundles2

record IsLeftRModule {ℓ ℓᴿ : Level}
  {R : Type ℓᴿ} (   1ᴿ : R) (_+ᴿ_ _·ᴿ_ : R → R → R)
  {X  : Type ℓ} (0ᴹ    : X) (_+ᴹ_      : X → X → X) (_·ᴹ_ : R → X → X) (-ᴹ_ : X → X)
  : Type (ℓ-max ℓ ℓᴿ) where
  field
    isAbGroupᴹ  : IsAbGroup 0ᴹ    _+ᴹ_      -ᴹ_
    ·ᴹ-dist-+ᴹ  : ∀ r x y → r ·ᴹ (x +ᴹ y) ≡ (r ·ᴹ x) +ᴹ (r ·ᴹ y)
    ·ᴹ-dist-+ᴿ  : ∀ r s x → (r +ᴿ s) ·ᴹ x ≡ (r ·ᴹ x) +ᴹ (s ·ᴹ x)
    ·ᴹ-assoc-·ᴿ : ∀ r s x → (r ·ᴿ s) ·ᴹ x ≡ r ·ᴹ (s ·ᴹ x)
    ·ᴹ-identity : ∀ x → 1ᴿ ·ᴹ x ≡ x
  open IsAbGroup isAbGroupᴹ renaming
    ( _-_ to _-ᴹ_
    ; assoc       to +ᴹ-assoc
    ; identity    to +ᴹ-identity
    ; lid         to +ᴹ-lid
    ; rid         to +ᴹ-rid
    ; inverse     to +ᴹ-inv
    ; invl        to +ᴹ-linv
    ; invr        to +ᴹ-rinv
    ; comm        to +ᴹ-comm
    ; isSemigroup to +ᴹ-isSemigroup
    ; isMonoid    to +ᴹ-isMonoid
    ; isGroup     to +ᴹ-isGroup
    ) public

ApartnessRingWithAbs = Ring -- TODO define `ApartnessRingWithAbs`

record LeftRModule {ℓ ℓᴿ : Level} (ring : ApartnessRingWithAbs {ℓᴿ}) : Type (ℓ-suc (ℓ-max ℓ ℓᴿ)) where
  open Ring ring renaming
    ( Carrier       to Carrierᴿ
    ; 0r            to 0ᴿ
    ; 1r            to 1ᴿ
    ; _+_           to _+ᴿ_
    ; _·_           to _·ᴿ_
    ; -_            to -ᴿ_
    ; is-set        to is-setᴿ
    ; +-assoc       to +ᴿ-assoc
    ; +-identity    to +ᴿ-identity
    ; +-lid         to +ᴿ-lid
    ; +-rid         to +ᴿ-rid
    ; +-inv         to +ᴿ-inv
    ; +-linv        to +ᴿ-linv
    ; +-rinv        to +ᴿ-rinv
    ; +-comm        to +ᴿ-comm
    ; +-isSemigroup to +ᴿ-isSemigroup
    ; +-isMonoid    to +ᴿ-isMonoid
    ; +-isGroup     to +ᴿ-isGroup
    ; ·-assoc       to ·ᴿ-assoc
    ; ·-identity    to ·ᴿ-identity
    ; ·-lid         to ·ᴿ-lid
    ; ·-rid         to ·ᴿ-rid
    ; ·-isSemigroup to ·ᴿ-isSemigroup
    ; ·-rdist-+     to ·ᴿ-rdist-+ᴿ
    ; ·-ldist-+     to ·ᴿ-ldist-+ᴿ
    ) public

  field
    Carrier  : Type ℓ
    0ᴹ       : Carrier
    _+ᴹ_     : Carrier → Carrier → Carrier
    _·ᴹ_     : Carrierᴿ → Carrier → Carrier
    -ᴹ_      : Carrier → Carrier
    isLeftRModule : IsLeftRModule 1ᴿ _+ᴿ_ _·ᴿ_ 0ᴹ _+ᴹ_ _·ᴹ_ -ᴹ_

  open IsLeftRModule isLeftRModule public

  infix  8 -ᴹ_
  infixl 7 _·ᴹ_
  infixl 6 _+ᴹ_

record LeftKModule {ℓ ℓᴷ : Level} (ffield : CompleteApartnessFieldWithAbs {ℓᴷ}) : Type (ℓ-suc (ℓ-max ℓ ℓᴷ)) where
   open CompleteApartnessFieldWithAbs ffield renaming
     ( Carrier       to Carrierᴷ
     ; 0f            to 0ᴷ
     ; 1f            to 1ᴷ
     ; _+_           to _+ᴷ_
     ; _·_           to _·ᴷ_
     ; -_            to -ᴷ_
     ) public
   field
     Carrier  : Type ℓ
     0ᴹ       : Carrier
     _+ᴹ_     : Carrier → Carrier → Carrier
     _·ᴹ_     : Carrierᴷ → Carrier → Carrier
     -ᴹ_      : Carrier → Carrier
     isLeftRModule : IsLeftRModule 1ᴷ _+ᴷ_ _·ᴷ_ 0ᴹ _+ᴹ_ _·ᴹ_ -ᴹ_
