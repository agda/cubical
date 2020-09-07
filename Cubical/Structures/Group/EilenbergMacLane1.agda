{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Structures.Group.EilenbergMacLane1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Base
open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Group.Base
open import Cubical.Structures.Group.Properties
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Nullification as Null hiding (rec; elim)
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1

private
  variable ℓ : Level

module _ (G : Group {ℓ}) where

  open Group G

  emloop-id : emloop 0g ≡ refl
  emloop-id =
    -- emloop 0g ≡⟨ rUnit (emloop 0g) ⟩
    emloop 0g ≡⟨ rUnit (emloop 0g) ⟩
    emloop 0g ∙ refl ≡⟨ cong (emloop 0g ∙_) (rCancel (emloop 0g) ⁻¹) ⟩
    emloop 0g ∙ (emloop 0g ∙ (emloop 0g) ⁻¹) ≡⟨ ∙assoc _ _ _ ⟩
    (emloop 0g ∙ emloop 0g) ∙ (emloop 0g) ⁻¹ ≡⟨ cong (_∙ emloop 0g ⁻¹) ((emloop-comp G 0g 0g) ⁻¹) ⟩
    emloop (0g + 0g) ∙ (emloop 0g) ⁻¹ ≡⟨ cong (λ g → emloop {G = G} g ∙ (emloop 0g) ⁻¹)  (rid 0g) ⟩
    emloop 0g ∙ (emloop 0g) ⁻¹ ≡⟨ rCancel (emloop 0g) ⟩
    refl ∎

  emloop-inv : (g : Carrier) → emloop (- g) ≡ (emloop g) ⁻¹
  emloop-inv g =
    emloop (- g) ≡⟨ rUnit (emloop (- g)) ⟩
    emloop (- g) ∙ refl ≡⟨ cong (emloop (- g) ∙_) (rCancel (emloop g) ⁻¹) ⟩
    emloop (- g) ∙ (emloop g ∙ (emloop g) ⁻¹) ≡⟨ ∙assoc _ _ _ ⟩
    (emloop (- g) ∙ emloop g) ∙ (emloop g) ⁻¹ ≡⟨ cong (_∙ emloop g ⁻¹) ((emloop-comp G (- g) g) ⁻¹) ⟩
    emloop (- g + g) ∙ (emloop g) ⁻¹ ≡⟨ cong (λ h → emloop {G = G} h ∙ (emloop g) ⁻¹) (invl g) ⟩
    emloop 0g ∙ (emloop g) ⁻¹ ≡⟨ cong (_∙ (emloop g) ⁻¹) emloop-id ⟩
    refl ∙ (emloop g) ⁻¹ ≡⟨ (lUnit ((emloop g) ⁻¹)) ⁻¹ ⟩
    (emloop g) ⁻¹ ∎

  EM₁Groupoid : isGroupoid (EM₁ G)
  EM₁Groupoid = emsquash

  EM₁Connected : isConnected 2 (EM₁ G)
  EM₁Connected = ∣ embase ∣ , h
    where
      h : (y : hLevelTrunc 2 (EM₁ G)) → ∣ embase ∣ ≡ y
      h = trElim (λ y → isOfHLevelSuc 1 (isOfHLevelTrunc 2 ∣ embase ∣ y))
            (elimProp G (λ x → isOfHLevelTrunc 2 ∣ embase ∣ ∣ x ∣) refl)

  {- since we write composition in diagrammatic order,
     and function composition in the other order,
     we need right multiplication here -}
  rightEquiv : (g : Carrier) → Carrier ≃ Carrier
  rightEquiv g = isoToEquiv (iso (_+ g) (_+ - g)
    (λ h → (h + - g) + g ≡⟨ (assoc h (- g) g) ⁻¹ ⟩
             h + - g + g ≡⟨ cong (h +_) (invl g) ⟩
                  h + 0g ≡⟨ rid h ⟩ h ∎)
    λ h → (h + g) + - g ≡⟨ (assoc h g (- g)) ⁻¹ ⟩
            h + g + - g ≡⟨ cong (h +_) (invr g) ⟩
                 h + 0g ≡⟨ rid h ⟩ h ∎)

  compRightEquiv : (g h : Carrier)
    → compEquiv (rightEquiv g) (rightEquiv h) ≡ rightEquiv (g + h)
  compRightEquiv g h = equivEq _ _ (funExt (λ x → (assoc x g h) ⁻¹))

  CodesSet : EM₁ G → hSet ℓ
  CodesSet = rec G (isOfHLevelTypeOfHLevel 2) (Carrier , is-set) RE REComp
    where
      RE : (g : Carrier) → Path (hSet ℓ) (Carrier , is-set) (Carrier , is-set)
      RE g = Σ≡Prop (λ X → isPropIsOfHLevel {A = X} 2) (ua (rightEquiv g))

      lemma₁ : (g h : Carrier) → Square
        (ua (rightEquiv g)) (ua (rightEquiv (g + h)))
        refl (ua (rightEquiv h))
      lemma₁ g h = invEq
                   (Square≃doubleComp (ua (rightEquiv g)) (ua (rightEquiv (g + h)))
                     refl (ua (rightEquiv h)))
                   (ua (rightEquiv g) ∙ ua (rightEquiv h)
                       ≡⟨ (uaCompEquiv (rightEquiv g) (rightEquiv h)) ⁻¹ ⟩
                    ua (compEquiv (rightEquiv g) (rightEquiv h))
                       ≡⟨ cong ua (compRightEquiv g h) ⟩
                    ua (rightEquiv (g + h)) ∎)

      lemma₂ : {A₀₀ A₀₁ : hSet ℓ} (p₀₋ : A₀₀ ≡ A₀₁)
               {A₁₀ A₁₁ : hSet ℓ} (p₁₋ : A₁₀ ≡ A₁₁)
               (p₋₀ : A₀₀ ≡ A₁₀) (p₋₁ : A₀₁ ≡ A₁₁)
                 (s : Square (cong fst p₀₋) (cong fst p₁₋) (cong fst p₋₀) (cong fst p₋₁))
               → Square p₀₋ p₁₋ p₋₀ p₋₁
      fst (lemma₂ p₀₋ p₁₋ p₋₀ p₋₁ s i j) = s i j
      snd (lemma₂ p₀₋ p₁₋ p₋₀ p₋₁ s i j) =
        isSet→isSetDep (λ X → isProp→isSet (isPropIsOfHLevel {A = X} 2))
          (cong fst p₀₋) (cong fst p₁₋) (cong fst p₋₀) (cong fst p₋₁) s
          (cong snd p₀₋) (cong snd p₁₋) (cong snd p₋₀) (cong snd p₋₁) i j

      REComp : (g h : Carrier) → Square (RE g) (RE (g + h)) refl (RE h)
      REComp g h = lemma₂ (RE g) (RE (g + h)) refl (RE h) (lemma₁ g h)


  Codes : EM₁ G → Type ℓ
  Codes x = CodesSet x .fst

  encode : (x : EM₁ G) → embase ≡ x → Codes x
  encode x p = subst Codes p 0g

  decode : (x : EM₁ G) → Codes x → embase ≡ x
  decode = elimSet G (λ x → isOfHLevelΠ 2 (λ c → EM₁Groupoid (embase) x))
    emloop λ g → ua→ λ h → emcomp h g

  decode-encode : (x : EM₁ G) (p : embase ≡ x) → decode x (encode x p) ≡ p
  decode-encode x p = J (λ y q → decode y (encode y q) ≡ q)
    (emloop (transport refl 0g) ≡⟨ cong emloop (transportRefl 0g) ⟩
     emloop 0g ≡⟨ emloop-id ⟩ refl ∎) p

  encode-decode : (x : EM₁ G) (c : Codes x) → encode x (decode x c) ≡ c
  encode-decode = elimProp G (λ x → isOfHLevelΠ 1 (λ c → CodesSet x .snd _ _))
    λ g → encode embase (decode embase g) ≡⟨ refl ⟩
          encode embase (emloop g) ≡⟨ refl ⟩
          transport (ua (rightEquiv g)) 0g ≡⟨ uaβ (rightEquiv g) 0g ⟩
          0g + g ≡⟨ lid g ⟩
          g ∎

  ΩEM₁Iso : Iso (Path (EM₁ G) embase embase) Carrier
  Iso.fun ΩEM₁Iso = encode embase
  Iso.inv ΩEM₁Iso = emloop
  Iso.rightInv ΩEM₁Iso = encode-decode embase
  Iso.leftInv ΩEM₁Iso = decode-encode embase

  ΩEM₁≡ : (Path (EM₁ G) embase embase) ≡ Carrier
  ΩEM₁≡ = isoToPath ΩEM₁Iso
