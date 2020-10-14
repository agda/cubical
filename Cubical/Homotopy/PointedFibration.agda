{-# OPTIONS --cubical --safe #-}

module Cubical.Homotopy.PointedFibration where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.Base
open import Cubical.Homotopy.ConnectedOld
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open LowerBoundedInduction
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.HLevels'
open import Cubical.Foundations.Structure

private
  variable
    ℓ ℓ' : Level

-- Different versions of Theorem 9. We abstract ℓ' again here
-- to avoid some issues with implicit arguments.
module _ {ℓ' : Level} (X : Pointed ℓ) where
  -- block of private stuff to reduce redundancy in the proof of the theorme
  private
    module _ (n k : ℕ) where
      -- A, together with its paramenters/context, is just the statement of the theorem.
      A : Type (ℓ-max ℓ (ℓ-suc ℓ'))
      A = (isConnX : isConnected (k + 1) (typ X))
          → (Y : typ X → Σ[ Yx ∈ Pointed ℓ' ] (isOfHLevel (n + k) (typ Yx)))
          → isOfHLevel (n) (Π∙ X (λ x → typ (fst (Y x))) (pt (fst (Y (pt X)))))

    module PointSec (n k : ℕ)
                    (isConnX : isConnected (k + 1) (typ X))
                    (Y : typ X → Σ[ Yx ∈ Pointed ℓ' ] (isOfHLevel (n + k) (typ Yx))) where
      -- The type of pointed sections (x : X) →ₚₜ Y x
      sec∙ : Type (ℓ-max ℓ ℓ')
      sec∙ = Π∙ X (λ x → typ (fst (Y x))) (pt (fst (Y (pt X))))

      -- Note that if isOfHLevel had a uniform interface for n ≥ 1 then this should be a part of the where
      -- clause in the theorem.
      module PointSecProps where
        -- Given s, the type of pointed sections (x : X) →ₚₜ Ω(Y x, s x)
        sec∙' : (s : sec∙) → Type (ℓ-max ℓ ℓ')
        sec∙' s = Π∙ X (λ x → s .fst x ≡ s .fst x) refl

        -- towards sec∙' s ≃ (s ≡ s)
        secIso : (s : sec∙) → Iso (sec∙' s) (s ∙∼ s)
        secIso (_ , s₂) = iso (λ (H , p) → H , p ∙ sym (rCancel s₂))
                        (λ (H , p) → H , p ∙ rCancel s₂)
                        (λ (H , p) → ΣPathP (refl ,
                                            sym (assoc p (rCancel s₂) (sym (rCancel s₂))) ∙∙
                                            cong (p ∙_) (rCancel (rCancel s₂)) ∙∙
                                            sym (rUnit p)))
                        (λ (H , p) → ΣPathP (refl ,
                                            sym (assoc p
                                                       (sym (rCancel s₂))
                                                       (rCancel s₂)) ∙∙
                                            cong (p ∙_) (lCancel (rCancel s₂)) ∙∙
                                            sym (rUnit p)))

        -- compose the equivalences
        sec≃ : (s : sec∙) → sec∙' s ≃ (s ≡ s)
        sec≃ = λ (s : sec∙) → compEquiv (isoToEquiv (secIso s)) (funExt∙≃ s s)

  -- p.9 Theorem 3 of Higher Types in HoTT
  sec∙Trunc : {n k : ℕ} → A (n + 1) (k)
  sec∙Trunc {n = 0} {k} isConnX Y = isContr→isProp (s₀ , λ s → funExt∙ (s₀∙∼s s))
    where
      sec∙ : Type (ℓ-max ℓ ℓ')
      sec∙ = Π∙ X (λ x → typ (fst (Y x))) (pt (fst (Y (pt X))))

      module _ where
        -- trivial section
        s₀ : sec∙
        s₀ = (λ a → pt (fst (Y a))) , refl

        -- abbreviations
        s₀₁ = fst s₀
        ⋆ = pt X

        -- the k-connected map 𝟙 → X
        f : Unit → typ X
        f tt = ⋆

        -- proof that f is k-connected
        fkconn : isConnectedFun k f
        fkconn = UnitConnectedFunElim isConnX f

        -- use the elimnation principle of the k-connected map f
        open elim f

        -- notation
        module _ (s : sec∙) where
          s₁ = fst s
          s₂ = snd s

          -- the regular homotopies between the trivial section and s coincide with the
          -- identity type s₀₁ ⋆ ≡ s₁ ⋆
          -- the Unit type will be eliminated in the next step
          IsoHtpy𝟙Idpt : Iso (s₀₁ ∼ s₁) (Unit → s₀₁ ⋆ ≡ s₁ ⋆)
          IsoHtpy𝟙Idpt = isIsoPrecompose k (λ (x : typ X) → (s₀₁ x ≡ s₁ x) , HL← (HL→ (snd (Y x)) (s₀₁ x) (s₁ x))) fkconn
          -- IsoHtpy𝟙Idpt = isIsoPrecompose (λ (x : typ X) → (s₀₁ x ≡ s₁ x) , HL← ((HL→ (snd (Y x))) (s₀₁ x) (s₁ x))) fkconn

          IsoHtpyIdpt : Iso (s₀₁ ∼ s₁) (s₀₁ ⋆ ≡ s₁ ⋆)
          IsoHtpyIdpt = compIso IsoHtpy𝟙Idpt (𝟙-universal (s₀₁ ⋆ ≡ s₁ ⋆))

          -- judgementally,
          -- (s₀ ∙∼ s) ≡ (Σ[ h ∈ (s₀₁ ∼ s₁) ] (h ⋆ ≡ (snd s₀) ∙ s₂ ⁻¹))
          -- The right inverse of IsoHtpyIdpt gives such a pointed homotopy
          s₀∙∼s : s₀ ∙∼ s
          fst s₀∙∼s = Iso.inv IsoHtpyIdpt (refl ∙ s₂ ⁻¹)
          snd s₀∙∼s =
            Iso.inv IsoHtpyIdpt (refl ∙ s₂ ⁻¹) ⋆
              ≡⟨ refl ⟩
            Iso.fun IsoHtpyIdpt (Iso.inv IsoHtpyIdpt (refl ∙ s₂ ⁻¹))
              ≡⟨ Iso.rightInv IsoHtpyIdpt (refl ∙ s₂ ⁻¹) ⟩
            refl ∙ s₂ ⁻¹ ∎
         

  sec∙Trunc {n = 1} {k} isConnX Y = truncSelfId→truncId {n = 0} (λ s → EquivPresHLevel {n = 1} (sec≃ s) (sec∙Trunc {n = 0} {k} isConnX λ x → ((s .fst x ≡ s .fst x) , refl) , (snd (Y x) (s .fst x) (s .fst x))))
    where
      open PointSec 2 k isConnX Y
      open PointSecProps

  sec∙Trunc {n = suc (suc m)} {k} isConnX Y =
    -- suffices to show that loop spaces are truncated
    truncSelfId→truncId
      -- each self-identity type of a section s is equivalent to a type of sections
      λ s → EquivPresHLevel (sec≃ s)
        -- that the induction hypothesis can be applied to
        (sec∙Trunc {n = suc m} isConnX λ x → ((s .fst x ≡ s .fst x) , refl) , snd (Y x) (s .fst x) (s .fst x))
    where
      open PointSec (suc (suc m) + 1) k isConnX Y
      open PointSecProps


  -- alternate version of sec∙Trunc with bound on n instead of adding a bound
  sec∙Trunc' : {n k : ℕ} (1≤n : 1 ≤ n) → A n k
  sec∙Trunc' {n = n} {k = k} 1≤n
    = +Type→≤Type 1 (λ n → A n k) (λ r isConnX Y → sec∙Trunc {n = r} {k = k} isConnX Y) n 1≤n


module _ (X : Pointed ℓ) (Y : Pointed ℓ') where
  pointed-maps-truncated : {n k : ℕ}
                           → 1 ≤ n
                           → isConnected (k + 1) (typ X)
                           → isOfHLevel (n + k) (typ Y)
                           → isOfHLevel (n) (X →∙ Y)
  pointed-maps-truncated {n = n} 1≤n connX truncY =
    sec∙Trunc' X 1≤n connX λ _ → Y , truncY
