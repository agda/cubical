{-# OPTIONS --cubical --safe #-}

module Cubical.Homotopy.PointedFibration where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Nat

module _ {ℓ : Level} {X : Type ℓ} where
  -- Lemma 7.2.8 in the HoTT book
  -- For n >= -1, if X being inhabited implies X is an n-type, then X is an n-type
  inh→ntype→ntype : {n : ℕ} (t : X → isOfHLevel (suc n) X) → isOfHLevel (suc n) X
  inh→ntype→ntype {n = 0} t = λ x y → t x x y
  inh→ntype→ntype {n = suc _} t = λ x y → t x x y

module _ {ℓ : Level} {X : Type ℓ} where
  -- Theorem 7.2.7 in the HoTT book
  -- For n >= -1, X is an (n+1)-type if all its loop spaces are n-types
  truncSelfId→truncId : {n : ℕ} → ((x : X) → isOfHLevel (suc n) (x ≡ x)) → isOfHLevel (suc (suc n)) X
  truncSelfId→truncId {n = 0} t =
    λ x x' → inh→ntype→ntype {n = 0}
                              λ p → J (λ y q → isOfHLevel 1 (x ≡ y))
                                      (t x)
                                      p
  truncSelfId→truncId {n = suc m} t =
    λ x x' → inh→ntype→ntype {n = suc m}
                              λ p → J (λ y q → isOfHLevel (suc (suc m)) (x ≡ y))
                                      (t x)
                                      p

  open import Cubical.Foundations.Univalence
  EquivPresHLevel : {Y : Type ℓ} → {n : ℕ} → (X≃Y : X ≃ Y) → (hX : isOfHLevel n X) → isOfHLevel n Y
  EquivPresHLevel {Y} {n} X≃Y hX = subst (λ x → isOfHLevel n x) (ua X≃Y) hX

-- Theorem 3 p. 9. The index shift isn't annoying at all and no, there is no salt to be found here.
sec∙Trunc : {ℓ ℓ' : Level} {n k : ℕ}
            (X : Pointed ℓ) (isConnX : isHLevelConnected (k + 1) (typ X))
            (Y : typ X → Σ[ Yx ∈ Pointed ℓ' ] (isOfHLevel ((n + 1) + (k + 2)) (typ Yx)))
            → isOfHLevel (n + 1) (Π∙ X (λ x → typ (fst (Y x))) (pt (fst (Y (pt X)))))
sec∙Trunc {n = 0} {k} X isConnX Y = isContr→isProp
  (((λ a → pt (fst (Y a))) , refl) ,
  λ s → funExt∙P (∙∼→∙∼P {!!}))
sec∙Trunc {n = 1} {k} X isConnX Y = {!!}
sec∙Trunc {ℓ} {ℓ'} {n = suc (suc m)} {k} X isConnX Y =
  -- suffices to show that loop spaces are truncated
  truncSelfId→truncId
    -- each self-identity type of a section s is equivalent to a type of sections
    -- TODO: note that here sec≃ s is obtained from an isomorophism, and EquivPresLevel
    -- uses univalence and transport, so right now it would be more efficient to
    -- convert the iso to a path
    λ s → EquivPresHLevel (sec≃ s)
      -- that the induction hypothesis can be applied to
      (sec∙Trunc {n = suc m} X isConnX λ x → ((s .fst x ≡ s .fst x) , refl) , snd (Y x) (s .fst x) (s .fst x))
  where
    -- The type of pointed sections (x : X) →ₚₜ Y x
    sec∙ : Type (ℓ-max ℓ ℓ')
    sec∙ = Π∙ X (λ x → typ (fst (Y x))) (pt (fst (Y (pt X))))

    -- Given s, the type of pointed sections (x : X) →ₚₜ Ω(Y x, s x)
    sec∙' : (s : sec∙) → Type (ℓ-max ℓ ℓ')
    sec∙' = λ s → Π∙ X (λ x → s .fst x ≡ s .fst x) refl

    -- for each s these are equivalent
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Sigma
    open import Cubical.Foundations.GroupoidLaws
    open import Cubical.Foundations.Equiv

    secIso : (s : sec∙) → Iso (s ∙∼P s) (sec∙' s)
    secIso s = iso (λ tp → fst tp , snd (∙∼P→∙∼ tp) ∙ rCancel (snd s))
                    (λ tp → ∙∼→∙∼P (fst tp , snd tp ∙ sym (rCancel (snd s))))
                    (λ tp → {!!})
                    λ tp → {!!}



    -- invert the iso and turn it into equivalence
    sec≃ = λ (s : sec∙) → compEquiv (isoToEquiv (invIso (secIso s))) (funExt∙P≃ s s)
