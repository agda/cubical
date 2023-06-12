{-# OPTIONS --safe #-}

module Cubical.Data.Equality.Univalence where

open import Cubical.Foundations.Prelude
  hiding ( _≡_ ; step-≡ ; _∎ ; isPropIsContr)
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
           ; isProp    to isPropPath )
open import Cubical.Foundations.Equiv
  renaming ( fiber         to fiberPath
           ; isEquiv       to isEquivPath
           ; _≃_           to EquivPath
           ; equivFun      to equivFunPath
           ; isPropIsEquiv to isPropIsEquivPath
           ; idEquiv       to idEquivPath
           )
  hiding   ( equivCtr
           ; equivIsEquiv )

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
  ℓ ℓ' : Level
  A B : Type ℓ
  x y z : A

idToEquiv : A ≡ B → A ≃ B
idToEquiv {A = A} p = transport id p , J (λ B p → isEquiv {A = A} {B = B} (transport id p)) isEquivId p

ua : (A ≃ B) → (A ≡ B)
ua e = pathToEq (uaPath (equivToEquivPath e))

uaβ : (e : A ≃ B) → transport id (ua e) x ≡ equivFun e x
uaβ {x = x} e@(f , p) =
  transport id (pathToEq (uaPath (equivToEquivPath e))) x
    ≡⟨ transportPathToEq→transportPath id (uaPath (equivToEquivPath e)) x ⟩
  substPath id (uaPath (equivToEquivPath e)) x
    ≡⟨ pathToEq (uaPathβ (equivToEquivPath e) x) ⟩
  f x ∎

uaId : ua (id , isEquivId) ≡ refl {x = A}
uaId =
  pathToEq (uaPath (equivToEquivPath (id , isEquivId)))
    ≡⟨ ap (λ t → pathToEq (uaPath t)) (Σ≡Prop (λ f g h → pathToEq (isPropIsEquivPath f g h)) refl) ⟩
  pathToEq (uaPath (idEquivPath _))
    ≡⟨ ap pathToEq (pathToEq uaIdEquivPath) ⟩
  pathToEq reflPath
    ≡⟨ pathToEq-reflPath ⟩
  refl ∎

univalence : (A ≡ B) ≃ (A ≃ B)
univalence = isoToEquiv (iso idToEquiv ua (λ e → Σ≡Prop (λ _ f g → pathToEq (isPropIsEquiv f g)) (funExt λ _ → uaβ e)) (λ where refl → uaId))

-- -- Univalence formulated using ≡ everywhere
-- univalenceEq : (A ≡ B) ≃ (A ≃ B)
-- univalenceEq {A = A} {B = B} = equivPathToEquiv rem
--   where
--   rem0 : Path _ (Lift (EquivPath A B)) (Lift (A ≃ B))
--   rem0 = congPath Lift equivPath≡Equiv
-- 
--   rem1 : Path _ (A ≡ B) (Lift (A ≃ B))
--   rem1 i = hcomp (λ j → λ { (i = i0) → path≡Eq {A = A} {B = B} j
--                           ; (i = i1) → rem0 j })
--                  (univalencePath {A = A} {B = B} i)
-- 
--   rem : EquivPath (A ≡ B) (A ≃ B)
--   rem = compEquiv (eqweqmap rem1) (invEquiv LiftEquiv)
