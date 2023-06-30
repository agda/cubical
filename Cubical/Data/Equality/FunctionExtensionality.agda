{-

- Function Extensionality stated in terms of the inductively defined equality type

- Function Extensionality is stated as in the book: the function happly is defined
  in terms of J and satisfies happly refl = refl by definition

-}
{-# OPTIONS --safe #-}
module Cubical.Data.Equality.FunctionExtensionality where

open import Cubical.Foundations.Prelude
  hiding (_≡_ ; step-≡ ; _∎ ; isPropIsContr)
  renaming ( refl      to reflPath
           ; transport to transportPath
           ; J         to JPath
           ; JRefl     to JPathRefl
           ; sym       to symPath
           ; _∙_       to compPath
           ; cong      to congPath
           ; subst     to substPath
           ; substRefl to substPathReflPath
           ; funExt    to funExtPath
           ; isContr   to isContrPath
           ; isProp    to isPropPath
           )

open import Cubical.Data.Equality.Base
open import Cubical.Data.Equality.Conversion

private
  variable
    a ℓ : Level
    A : Type a
    P : A → Type ℓ

happlyFunExt : (f g : (x : A) → P x) (p : (x : A) → f x ≡ g x) → happly (funExt p) ≡ p
happlyFunExt f g p = funExt λ x →
    happly (pathToEq (λ i x → eqToPath (p x) i)) x   ≡⟨ lem f g (λ i x → eqToPath (p x) i) x ⟩
    pathToEq (eqToPath (p x))                        ≡⟨ pathToEq (pathToEq-eqToPath (p x)) ⟩
    p x                                              ∎
  where
    lem : (f g : (x : A) → P x) (p : Path _ f g) (x : A) → happly (pathToEq p) x ≡ pathToEq (λ i → p i x)
    lem f g = JPath (λ g p → ∀ x → happly (pathToEq p) x ≡ pathToEq (λ i → p i x)) λ x →
      happly (pathToEq λ i → f) x   ≡⟨ ap (λ p → happly {f = f} p x) pathToEq-reflPath ⟩
      happly (refl {x = f}) x       ≡⟨ sym pathToEq-reflPath ⟩
      pathToEq reflPath             ∎

funExtHapply : (f g : (x : A) → P x) (p : f ≡ g) → funExt (happly p) ≡ p
funExtHapply f .f refl = funExtRefl

functionExtensionality : {f g : (x : A) → P x} → (f ≡ g) ≃ ((x : A) → f x ≡ g x)
functionExtensionality = isoToEquiv (iso happly funExt (happlyFunExt _ _) (funExtHapply _ _))
