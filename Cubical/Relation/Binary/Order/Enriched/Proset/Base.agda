{-
These are prosets enriched over an ordered monoid Ω (to be thought of as a set of generalized truth values).
This is a decategorification of the notion of enriched categories.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.OrderedCommMonoid

open Iso

module Cubical.Relation.Binary.Order.Enriched.Proset.Base {ℓΩ} {ℓ⊢} (ΩCMonoid : OrderedCommMonoid ℓΩ ℓ⊢) where

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
  
  Ω = ΩCMonoid .fst

open OrderedCommMonoidStr (ΩCMonoid .snd) renaming (
  _≤_ to infix 5 _⊢_;
  _·_ to infix 6 _⊗_;
  ε to T;
  is-set to isSetΩ;
  is-prop-valued to isProp⊢;
  is-refl to ⊢refl;
  is-trans to ⊢trans;
  is-antisym to ⊢antisym;
  ·Assoc to ⊗Assoc;
  ·IdL to ⊗IdL;
  ·IdR to ⊗IdR;
  ·Comm to ⊗Comm
 )

record IsProset {A : Type ℓ} (_≲_ : A → A → Ω) : Type (ℓ-max ℓ ℓ⊢) where
  no-eta-equality
  constructor isproset

  field
    is-set : isSet A
    is-refl : ∀ x → T ⊢ x ≲ x
    is-trans : ∀ x y z → x ≲ y ⊗ y ≲ z ⊢ x ≲ z

unquoteDecl IsProsetIsoΣ = declareRecordIsoΣ IsProsetIsoΣ (quote IsProset)

record ProsetStr (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓΩ ℓ⊢)) where
  constructor prosetstr
  field
    _≲_     : A → A → Ω
    isProset : IsProset _≲_

  infixl 7 _≲_

  open IsProset isProset public

Proset : ∀ ℓ → Type (ℓ-max (ℓ-max ℓΩ ℓ⊢) (ℓ-suc ℓ))
Proset ℓ = TypeWithStr ℓ ProsetStr

proset : (A : Type ℓ) → (_≲_ : A → A → Ω) → IsProset _≲_ → Proset ℓ
proset A _≲_ pros = A , prosetstr _≲_ pros

record IsProsetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : ProsetStr A) (e : A ≃ B) (N : ProsetStr B)
  : Type (ℓ-max ℓ₀ ℓΩ)
  where
  constructor
   isprosetequiv
  -- Shorter qualified names
  private
    module M = ProsetStr M
    module N = ProsetStr N

  field
    pres≲ : (x y : A) → x M.≲ y ≡ equivFun e x N.≲ equivFun e y

ProsetEquiv : Proset ℓ₀ → Proset ℓ₁ → Type (ℓ-max (ℓ-max ℓΩ ℓ₀) ℓ₁)
ProsetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsProsetEquiv (M .snd) e (N .snd)

isPropIsProset : {A : Type ℓ} (_≲_ : A → A → Ω) → isProp (IsProset _≲_)
isPropIsProset _≲_ = isOfHLevelRetractFromIso 1 IsProsetIsoΣ
  (isProp×2 isPropIsSet (isPropΠ λ _ → isProp⊢ _ _) (isPropΠ3 λ _ _ _ → isProp⊢ _ _))

𝒮ᴰ-Proset : DUARel (𝒮-Univ ℓ) ProsetStr (ℓ-max ℓΩ ℓ)
𝒮ᴰ-Proset =
  𝒮ᴰ-Record (𝒮-Univ _) IsProsetEquiv
    (fields:
      data[ _≲_ ∣ autoDUARel _ _ ∣ pres≲ ]
      prop[ isProset ∣ (λ _ _ → isPropIsProset _) ])
    where
    open ProsetStr
    open IsProset
    open IsProsetEquiv

ProsetPath : (M N : Proset ℓ) → ProsetEquiv M N ≃ (M ≡ N)
ProsetPath = ∫ 𝒮ᴰ-Proset .UARel.ua

-- an easier way of establishing an equivalence of prosets
module _ {P : Proset ℓ₀} {S : Proset ℓ₁} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = ProsetStr (P .snd)
    module S = ProsetStr (S .snd)

  module _ (isMon : ∀ x y → x P.≲ y ⊢ equivFun e x S.≲ equivFun e y)
           (isMonInv : ∀ x y → x S.≲ y ⊢ invEq e x P.≲ invEq e y) where
    open IsProsetEquiv
    open IsProset

    makeIsProsetEquiv : IsProsetEquiv (P .snd) e (S .snd)
    makeIsProsetEquiv .pres≲ x y = ⊢antisym _ _ (isMon _ _) isMonInv' where
      isMonInv' = subst (_ ⊢_) (cong₂ P._≲_ (retEq e x) (retEq e y)) (isMonInv (e .fst x) (e .fst y))
