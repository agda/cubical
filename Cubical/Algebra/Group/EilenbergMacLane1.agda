{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}

module Cubical.Algebra.Group.EilenbergMacLane1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1

private
  variable ℓ : Level

module _ (Ĝ : Group ℓ) where
  private
    G = fst Ĝ
  open GroupStr (snd Ĝ)

  emloop-id : emloop 1g ≡ refl
  emloop-id =
    emloop 1g                                 ≡⟨ rUnit (emloop 1g) ⟩
    emloop 1g ∙ refl                          ≡⟨ cong (emloop 1g ∙_) (rCancel (emloop 1g) ⁻¹) ⟩
    emloop 1g ∙ (emloop 1g ∙ (emloop 1g) ⁻¹)  ≡⟨ ∙assoc _ _ _ ⟩
    (emloop 1g ∙ emloop 1g) ∙ (emloop 1g) ⁻¹  ≡⟨ cong (_∙ emloop 1g ⁻¹)
                                                   ((emloop-comp Ĝ 1g 1g) ⁻¹) ⟩
    emloop (1g · 1g) ∙ (emloop 1g) ⁻¹         ≡⟨ cong (λ g → emloop {Group = Ĝ} g
                                                             ∙ (emloop 1g) ⁻¹)
                                                      (rid 1g) ⟩
    emloop 1g ∙ (emloop 1g) ⁻¹                ≡⟨ rCancel (emloop 1g) ⟩
    refl ∎

  emloop-inv : (g : G) → emloop (inv g) ≡ (emloop g) ⁻¹
  emloop-inv g =
    emloop (inv g)                              ≡⟨ rUnit (emloop (inv g)) ⟩
    emloop (inv g) ∙ refl                       ≡⟨ cong (emloop (inv g) ∙_)
                                                      (rCancel (emloop g) ⁻¹) ⟩
    emloop (inv g) ∙ (emloop g ∙ (emloop g) ⁻¹) ≡⟨ ∙assoc _ _ _ ⟩
    (emloop (inv g) ∙ emloop g) ∙ (emloop g) ⁻¹ ≡⟨ cong (_∙ emloop g ⁻¹)
                                                      ((emloop-comp Ĝ (inv g) g) ⁻¹) ⟩
    emloop (inv g · g) ∙ (emloop g) ⁻¹          ≡⟨ cong (λ h → emloop {Group = Ĝ} h
                                                            ∙ (emloop g) ⁻¹)
                                                      (invl g) ⟩
    emloop 1g ∙ (emloop g) ⁻¹                 ≡⟨ cong (_∙ (emloop g) ⁻¹) emloop-id ⟩
    refl ∙ (emloop g) ⁻¹                      ≡⟨ (lUnit ((emloop g) ⁻¹)) ⁻¹ ⟩
    (emloop g) ⁻¹ ∎

  isGroupoidEM₁ : isGroupoid (EM₁ Ĝ)
  isGroupoidEM₁ = emsquash

  isConnectedEM₁ : isConnected 2 (EM₁ Ĝ)
  isConnectedEM₁ = ∣ embase ∣ , h
    where
      h : (y : hLevelTrunc 2 (EM₁ Ĝ)) → ∣ embase ∣ ≡ y
      h = trElim (λ y → isOfHLevelSuc 1 (isOfHLevelTrunc 2 ∣ embase ∣ y))
            (elimProp Ĝ (λ x → isOfHLevelTrunc 2 ∣ embase ∣ ∣ x ∣) refl)

  {- since we write composition in diagrammatic order,
     and function composition in the other order,
     we need right multiplication here -}
  rightEquiv : (g : G) → G ≃ G
  rightEquiv g = isoToEquiv isom
    where
    isom : Iso G G
    isom .Iso.fun = _· g
    isom .Iso.inv = _· inv g
    isom .Iso.rightInv h =
      (h · inv g) · g ≡⟨ (assoc h (inv g) g) ⁻¹ ⟩
        h · inv g · g ≡⟨ cong (h ·_) (invl g) ⟩
             h · 1g ≡⟨ rid h ⟩ h ∎
    isom .Iso.leftInv h =
      (h · g) · inv g ≡⟨ (assoc h g (inv g)) ⁻¹ ⟩
        h · g · inv g ≡⟨ cong (h ·_) (invr g) ⟩
             h · 1g ≡⟨ rid h ⟩ h ∎

  compRightEquiv : (g h : G)
    → compEquiv (rightEquiv g) (rightEquiv h) ≡ rightEquiv (g · h)
  compRightEquiv g h = equivEq (funExt (λ x → (assoc x g h) ⁻¹))

  CodesSet : EM₁ Ĝ → hSet ℓ
  CodesSet = rec Ĝ (isOfHLevelTypeOfHLevel 2) (G , is-set) RE REComp
    where
      RE : (g : G) → Path (hSet ℓ) (G , is-set) (G , is-set)
      RE g = Σ≡Prop (λ X → isPropIsOfHLevel {A = X} 2) (ua (rightEquiv g))

      lemma₁ : (g h : G) → Square
        (ua (rightEquiv g)) (ua (rightEquiv (g · h)))
        refl (ua (rightEquiv h))
      lemma₁ g h = invEq
                   (Square≃doubleComp (ua (rightEquiv g)) (ua (rightEquiv (g · h)))
                     refl (ua (rightEquiv h)))
                   (ua (rightEquiv g) ∙ ua (rightEquiv h)
                       ≡⟨ (uaCompEquiv (rightEquiv g) (rightEquiv h)) ⁻¹ ⟩
                    ua (compEquiv (rightEquiv g) (rightEquiv h))
                       ≡⟨ cong ua (compRightEquiv g h) ⟩
                    ua (rightEquiv (g · h)) ∎)

      lemma₂ : {A₀₀ A₀₁ : hSet ℓ} (p₀₋ : A₀₀ ≡ A₀₁)
               {A₁₀ A₁₁ : hSet ℓ} (p₁₋ : A₁₀ ≡ A₁₁)
               (p₋₀ : A₀₀ ≡ A₁₀) (p₋₁ : A₀₁ ≡ A₁₁)
               (s : Square (cong fst p₀₋) (cong fst p₁₋) (cong fst p₋₀) (cong fst p₋₁))
               → Square p₀₋ p₁₋ p₋₀ p₋₁
      fst (lemma₂ p₀₋ p₁₋ p₋₀ p₋₁ s i j) = s i j
      snd (lemma₂ p₀₋ p₁₋ p₋₀ p₋₁ s i j) =
        isSet→SquareP {A = (λ i j → isSet (s i j))}
          (λ i j → isProp→isSet (isPropIsOfHLevel 2))
          (cong snd p₀₋) (cong snd p₁₋) (cong snd p₋₀) (cong snd p₋₁) i j

      REComp : (g h : G) → Square (RE g) (RE (g · h)) refl (RE h)
      REComp g h = lemma₂ (RE g) (RE (g · h)) refl (RE h) (lemma₁ g h)
  Codes : EM₁ Ĝ → Type ℓ
  Codes x = CodesSet x .fst

  encode : (x : EM₁ Ĝ) → embase ≡ x → Codes x
  encode x p = subst Codes p 1g

  decode : (x : EM₁ Ĝ) → Codes x → embase ≡ x
  decode = elimSet Ĝ (λ x → isOfHLevelΠ 2 (λ c → isGroupoidEM₁ (embase) x))
    emloop λ g → ua→ λ h → emcomp h g


  decode-encode : (x : EM₁ Ĝ) (p : embase ≡ x) → decode x (encode x p) ≡ p
  decode-encode x p = J (λ y q → decode y (encode y q) ≡ q)
    (emloop (transport refl 1g) ≡⟨ cong emloop (transportRefl 1g) ⟩
     emloop 1g ≡⟨ emloop-id ⟩ refl ∎) p

  encode-decode : (x : EM₁ Ĝ) (c : Codes x) → encode x (decode x c) ≡ c
  encode-decode = elimProp Ĝ (λ x → isOfHLevelΠ 1 (λ c → CodesSet x .snd _ _))
    λ g → encode embase (decode embase g) ≡⟨ refl ⟩
          encode embase (emloop g) ≡⟨ refl ⟩
          transport (ua (rightEquiv g)) 1g ≡⟨ uaβ (rightEquiv g) 1g ⟩
          1g · g ≡⟨ lid g ⟩
          g ∎

  ΩEM₁Iso : Iso (Path (EM₁ Ĝ) embase embase) G
  Iso.fun ΩEM₁Iso = encode embase
  Iso.inv ΩEM₁Iso = emloop
  Iso.rightInv ΩEM₁Iso = encode-decode embase
  Iso.leftInv ΩEM₁Iso = decode-encode embase

  ΩEM₁≡ : (Path (EM₁ Ĝ) embase embase) ≡ G
  ΩEM₁≡ = isoToPath ΩEM₁Iso
