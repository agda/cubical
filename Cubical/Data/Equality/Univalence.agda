{- Univalence in terms of _≡_

- Univalence stated in terms of the inductively defined equality type

- Univalence is stated as in the book: the function idToEquiv is an equivalence

-}

module Cubical.Data.Equality.Univalence where

open import Cubical.Foundations.Prelude
  using ()
  renaming ( refl      to reflPath
           ; subst     to substPath
           )
open import Cubical.Foundations.Equiv
  using ()
  renaming ( isPropIsEquiv to isPropIsEquivPath
           ; idEquiv       to idEquivPath
           )

open import Cubical.Foundations.Univalence
  using ()
  renaming ( ua        to uaPath
           ; uaβ       to uaPathβ
           ; uaIdEquiv to uaIdEquivPath
           )

open import Cubical.Data.Equality.Base
open import Cubical.Data.Equality.Conversion

private
 variable
  a b ℓ ℓ' : Level
  A : Type a
  B : Type b
  x y z : A

idToEquiv : A ≡ B → A ≃ B
idToEquiv {A = A} p = transport id p , J (λ B p → isEquiv {A = A} {B = B} (transport id p)) isEquivId p

ua : (A ≃ B) → (A ≡ B)
ua e = pathToEq (uaPath (equivToEquivPath e))

uaβ : (e : A ≃ B) → transport id (ua e) x ≡ equivFun e x
uaβ {x = x} e@(f , p) =
    transport id (pathToEq (uaPath (equivToEquivPath e))) x ≡⟨ step1 ⟩
    substPath id (uaPath (equivToEquivPath e)) x            ≡⟨ step2 ⟩
    f x ∎
  where
    step1 = transportPathToEq→transportPath id (uaPath (equivToEquivPath e)) x
    step2 = pathToEq (uaPathβ (equivToEquivPath e) x)

uaId : ua (id , isEquivId) ≡ refl {x = A}
uaId =
    pathToEq (uaPath (equivToEquivPath (id , isEquivId))) ≡⟨ step1 ⟩
    pathToEq (uaPath (idEquivPath _))                     ≡⟨ step2 ⟩
    pathToEq reflPath                                     ≡⟨ step3 ⟩
    refl ∎
  where
    step1 = ap (λ t → pathToEq (uaPath t)) (Σ≡Prop (λ f g h → pathToEq (isPropIsEquivPath f g h)) refl)
    step2 = ap pathToEq (pathToEq uaIdEquivPath)
    step3 = pathToEq-reflPath

univalence : (A ≡ B) ≃ (A ≃ B)
univalence =
  isoToEquiv
    (iso idToEquiv ua
         (λ e → Σ≡Prop (λ _ f g → pathToEq (isPropIsEquiv f g)) (funExt λ _ → uaβ e))
         (λ where refl → uaId))
