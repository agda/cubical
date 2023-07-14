{-# OPTIONS --safe --postfix-projections #-}

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Homotopy.Base

open import Cubical.Reflection.RecordEquiv


module Cubical.Modalities.ReflectiveSubuniverse where

private
  variable
    ℓ : Level

module _ (isModal : Type ℓ → Type ℓ) (isPropIsModal : (A : Type ℓ) → isProp (isModal A)) where
  -- A type A such that - ∘ η induces an equivalence of hom sets into modal types
  record HasLift (A : Type ℓ) : Type (ℓ-suc ℓ) where
    constructor hasLift
    field
      ◯A : Type ℓ
      η : A → ◯A
      isModal-◯A : isModal ◯A
      up : (B : Type ℓ) → isModal B → isEquiv (λ (g : ◯A → B) → g ∘ η)

    module _ {B : Type ℓ} (isModalB : isModal B) where
      open Iso

      isContrLift : (f : A → B) → isContr (Σ[ f' ∈ (◯A → B) ] f' ∘ η ≡ f)
      isContrLift f = up B isModalB .equiv-proof f

      lift≃ : Iso (◯A → B) (A → B)
      lift≃ = equivToIso (_∘ η , up B isModalB)

      ◯-rec : (A → B) → (◯A → B)
      ◯-rec = lift≃ .inv

      ◯-rec-η : (f : ◯A → B) → ◯-rec (f ∘ η) ≡ f
      ◯-rec-η f = lift≃ .leftInv f

      ◯-rec-β : (f : A → B) → ◯-rec f ∘ η ≡ f
      ◯-rec-β f = lift≃ .rightInv f

    -- the lifted map is unique, this implies the uniqueness below
    lift-unique : {B : Type ℓ} (p : isModal B) (f : A → B) (g : ◯A → B) → f ≡ g ∘ η → ◯-rec p f ≡ g
    lift-unique isModalB f g q = cong (◯-rec isModalB) q ∙ ◯-rec-η isModalB g

    lift-η : ◯-rec isModal-◯A η ≡ idfun ◯A
    lift-η = ◯-rec-η isModal-◯A (idfun _)
  open HasLift

  module _ (A : Type ℓ) (x y : HasLift A) where
    private
      variable
        B : Type ℓ
        C : Type ℓ
    private
      f : x .◯A → y .◯A
      f = ◯-rec x (y .isModal-◯A) (y .η)

      fη : f ∘ x .η ≡ y .η
      fη = ◯-rec-β x (y .isModal-◯A) (y .η)

      g : y .◯A → x .◯A
      g = ◯-rec y (x .isModal-◯A) (x .η)

      gη : g ∘ y .η ≡ x .η
      gη = ◯-rec-β y (x .isModal-◯A) (x .η)

      sec : f ∘ g ≡ idfun _
      sec = sym (lift-unique y (y .isModal-◯A) (y .η) (f ∘ g) (sym fη ∙ cong (f ∘_) (sym gη))) ∙ lift-η y

      ret : g ∘ f ≡ idfun _
      ret = sym (lift-unique x (x .isModal-◯A) (x .η) (g ∘ f) (sym gη ∙ cong (g ∘_) (sym fη))) ∙ lift-η x

    ◯A≃◯'A : x .◯A ≃ y .◯A
    ◯A≃◯'A = isoToEquiv (iso f g (funExt⁻ sec) (funExt⁻ ret))

    ◯A≡◯'A : x .◯A ≡ y .◯A
    ◯A≡◯'A = ua ◯A≃◯'A

    η≡η' : transport (cong (λ t → A → t) ◯A≡◯'A) (x .η) ≡ y .η
    η≡η' =
      transport (cong (λ t → A → t) ◯A≡◯'A) (x .η)
        ≡⟨ refl ⟩
      transport ◯A≡◯'A ∘ x .η ∘ transport (λ _ → A)
        ≡⟨ funExt (λ z → cong (transport ◯A≡◯'A ∘ x .η) (transportRefl z)) ⟩
      transport ◯A≡◯'A ∘ x .η
        ≡⟨ funExt (λ z → uaβ ◯A≃◯'A (x .η z)) ⟩
      f ∘ x .η
        ≡⟨ fη ⟩
      y .η ∎

  isPropHasLift : (A : Type ℓ) → isProp (HasLift A)
  isPropHasLift A x y i .◯A = ◯A≡◯'A A x y i
  isPropHasLift A x y i .η = toPathP {A = λ j → A → ◯A≡◯'A A x y j} {x = x .η} {y = y .η} (η≡η' A x y) i
  isPropHasLift A x y i .isModal-◯A = toPathP {A = λ j → isModal (◯A≡◯'A A x y j)} {x = x .isModal-◯A} {y = y .isModal-◯A} (isPropIsModal (y .◯A) _ _) i
  isPropHasLift A x y i .up B isModalB = toPathP
    {A = λ j → isEquiv λ (g : ◯A≡◯'A A x y j → B) (a : A) → g (toPathP {A = λ j → A → ◯A≡◯'A A x y j}
    {x = x .η} {y = y .η} (η≡η' A x y) j a)} {x = x .up B isModalB} {y = y .up B isModalB} (toPathP (isPropIsEquiv _ _ _)) i

--   -- Can we also do it this way?
--   unquoteDecl HasLiftIsoΣ = declareRecordIsoΣ HasLiftIsoΣ (quote HasLift)
--
--   HasLift≡Σ : HasLift A ≡ _
--   HasLift≡Σ = ua (isoToEquiv HasLiftIsoΣ)
--
--   isPropHasLift2 : (A : Type ℓ) → isProp (HasLift A)
--   isPropHasLift2 A = isOfHLevelRetractFromIso 1 HasLiftIsoΣ λ x y →
--     ΣPathTransport→PathΣ x y (◯A≡◯'A A (transport⁻ HasLift≡Σ x) (transport⁻ HasLift≡Σ y) ,
--      let P : _ ≡ _
--          P = (λ i →
--             Σ
--             (A → ◯A≡◯'A A (transport⁻ HasLift≡Σ x) (transport⁻ HasLift≡Σ y) i)
--             (λ z₁ →
--                Σ
--                (isModal
--                 (◯A≡◯'A A (transport⁻ HasLift≡Σ x) (transport⁻ HasLift≡Σ y) i))
--                (λ z₂ → (B : Type ℓ) → isModal B → isEquiv (λ g₁ → g₁ ∘ z₁))))
--      in ΣPathTransport→PathΣ (transport (λ i → P i) (snd x)) (snd y)
--        ((transport (λ j → A → ◯A≡◯'A A (transport⁻ HasLift≡Σ x) (transport⁻ HasLift≡Σ y) j) (fst (snd x))
--          ≡⟨ η≡η' A (transport⁻ HasLift≡Σ x) (transport⁻ {!HasLift≡Σ {A = A}!} y) ⟩
--         fst (snd y) ∎)
--        , {!!}))


record IsReflectiveSubuniverse (isModal : Type ℓ → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    isPropIsModal : (A : Type ℓ) → isProp (isModal A)
    universalProperty : (A : Type ℓ) → HasLift isModal isPropIsModal A

  private variable A B C : Type ℓ

  ◯_ : Type ℓ → Type ℓ
  ◯ A = universalProperty A .HasLift.◯A

  η : A → ◯ A
  η = universalProperty _ .HasLift.η

  isModal-◯ : (A : Type ℓ) → isModal (◯ A)
  isModal-◯ A = universalProperty A .HasLift.isModal-◯A

  module _ (p : isModal B) where
    ◯-rec : (A → B) → (◯ A → B)
    ◯-rec = HasLift.◯-rec (universalProperty _) p

    ◯-rec-η : (f : ◯ A → B) → ◯-rec (f ∘ η) ≡ f
    ◯-rec-η = HasLift.◯-rec-η (universalProperty _) p

    ◯-rec-β : (f : A → B) → ◯-rec f ∘ η ≡ f
    ◯-rec-β = HasLift.◯-rec-β (universalProperty _) p

    isModal→isContrLift : (f : A → B) → isContr (Σ[ f' ∈ (◯ A → B) ] f' ∘ η ≡ f)
    isModal→isContrLift = HasLift.isContrLift (universalProperty _) p

    lift-unique : (f : A → B) (g : ◯ A → B) → f ≡ g ∘ η → ◯-rec f ≡ g
    lift-unique = HasLift.lift-unique (universalProperty _) p

  -- Lemma 1.19. (i)
  isEquivη→isModalA : (A : Type ℓ) → isEquiv (η {A = A}) → isModal A
  isEquivη→isModalA A isEquivη = subst⁻ isModal (ua (η , isEquivη)) (isModal-◯ A)

  -- Lemma 1.20.
  retract→isEquivη : (A : Type ℓ) (f : ◯ A → A) → retract η f → isEquiv (η {A = A})
  retract→isEquivη A f ret = snd (isoToEquiv (iso η f sec ret))
    where
      sec : section η f
      sec z =
        (η ∘ f) z
          ≡⟨ sym (funExt⁻ (◯-rec-η (isModal-◯ A) (η ∘ f)) z) ⟩
        ◯-rec (isModal-◯ A) (η ∘ f ∘ η) z
          ≡⟨ cong (λ t → ◯-rec (isModal-◯ A) (η ∘ t) z) (funExt ret) ⟩
        ◯-rec (isModal-◯ A) η z
          ≡⟨ funExt⁻ (◯-rec-η (isModal-◯ A) (idfun _)) z ⟩
        z ∎

  retractIsModal : (A : Type ℓ) (f : ◯ A → A) → retract η f → isModal A
  retractIsModal A f ret = isEquivη→isModalA A (retract→isEquivη A f ret)

  -- Lemma 1.19. (ii)
  isModalA→isEquivη : (A : Type ℓ) → isModal A → isEquiv (η {A = A})
  isModalA→isEquivη A isModalA = retract→isEquivη A (◯-rec isModalA (idfun _)) (funExt⁻ (◯-rec-β isModalA (idfun _)))

  -- Lemma 1.21.
  ◯-map : (A → B) → ◯ A → ◯ B
  ◯-map f = ◯-rec (isModal-◯ _) (η ∘ f)

  ◯-map-id : ◯-map (idfun _) ≡ idfun (◯ A)
  ◯-map-id = ◯-rec-η (isModal-◯ _) (idfun _)

  ◯-map-∘ : (f : B → C) (g : A → B) → ◯-map (f ∘ g) ≡ ◯-map f ∘ ◯-map g
  ◯-map-∘ f g = lift-unique (isModal-◯ _) (η ∘ f ∘ g) (◯-map f ∘ ◯-map g)
    ( η ∘ f ∘ g
        ≡⟨ cong (_∘ g) (sym (◯-rec-β (isModal-◯ _) (η ∘ f))) ⟩
      ◯-map f ∘ η ∘ g
        ≡⟨ cong (◯-map f ∘_) (sym (◯-rec-β (isModal-◯ _) (η ∘ g))) ⟩
      ◯-map f ∘ ◯-map g ∘ η ∎)

  η-nat : (f : A → B) → ◯-map f ∘ η ≡ η ∘ f
  η-nat f = ◯-rec-β (isModal-◯ _) (η ∘ f)

  -- Lemma 1.22.
  ◯-map-η : (A : Type ℓ) → ◯-map η ≡ η {A = ◯ A}
  ◯-map-η A = ◯-rec-η (isModal-◯ _) η

  isEquiv-◯η : (A : Type ℓ) → isEquiv (◯-map (η {A = A}))
  isEquiv-◯η A = subst⁻ isEquiv (◯-map-η A) (isModalA→isEquivη (◯ A) (isModal-◯ A))

  -- Lemma 1.23.
  isModalX∧isEquiv-◯f→isEquiv-∘f : (X : Type ℓ) → isModal X → (f : A → B) → isEquiv (◯-map f) → isEquiv λ (g : B → X) → g ∘ f
  isModalX∧isEquiv-◯f→isEquiv-∘f {A = A} {B = B} X isModalX f isEquiv◯f = subst⁻ isEquiv cs (snd eq)
    where
      cs : _∘ f ≡ (_∘ η) ∘ (_∘ ◯-map f) ∘ ◯-rec isModalX
      cs =
        _∘ f
          ≡⟨ sym (cong (λ t → (_∘ f) ∘ t) (funExt λ g → ◯-rec-β isModalX g)) ⟩
        (_∘ f) ∘ (_∘ η) ∘ ◯-rec isModalX
          ≡⟨ (funExt λ g → funExt λ x → cong (◯-rec isModalX g) (sym (funExt⁻ (η-nat f) x))) ⟩
        (_∘ η) ∘ (_∘ ◯-map f) ∘ ◯-rec isModalX ∎

      eq : (B → X) ≃ (A → X)
      eq = invEquiv (_∘ η , universalProperty B .HasLift.up X isModalX)
        ∙ₑ preCompEquiv (_ , isEquiv◯f)
        ∙ₑ (_∘ η , universalProperty A .HasLift.up X isModalX)

  isEquiv-◯f∧isEquiv-∘f→isModalX : (X : Type ℓ) → ({A B : Type ℓ} (f : A → B) → isEquiv (◯-map f) → isEquiv (λ (g : B → X) → g ∘ f)) → isModal X
  isEquiv-◯f∧isEquiv-∘f→isModalX X h = retractIsModal X (lem .inv (idfun _)) (funExt⁻ (lem .rightInv (idfun _)))
    where
      open Iso

      lem : Iso (◯ X → X) (X → X) -- isEquiv (_∘ η)
      lem = equivToIso (_∘ η , h η (subst⁻ isEquiv (◯-map-η X) (isModalA→isEquivη (◯ X) (isModal-◯ X))))

  ηΣ : {P : A → Type ℓ} → Σ A P → ◯ (Σ[ a ∈ A ] ◯ P a)
  ηΣ (a , p) = η (a , η p)

  isEquiv-η-snd : (P : A → Type ℓ) → ◯ (Σ[ a ∈ A ] P a) ≡ ◯ (Σ[ a ∈ A ] ◯ P a)
  isEquiv-η-snd {A = A} P = cong HasLift.◯A (isPropHasLift isModal isPropIsModal (Σ A P) (universalProperty (Σ A P)) lift')
    where
      e : (B : Type ℓ) → isModal B → (◯ (Σ[ a ∈ A ] ◯ P a) → B) ≃ (Σ A P → B)
      e B isModalB =
        (◯ (Σ[ a ∈ A ] (◯ P a)) → B)
          ≃⟨ _∘ η , universalProperty _ .HasLift.up B isModalB ⟩
        (Σ[ a ∈ A ] (◯ P a) → B)
          ≃⟨ curryEquiv ⟩
        ((a : A) → ◯ P a → B)
          ≃⟨ equivΠCod (λ a → _∘ η , universalProperty _ .HasLift.up B isModalB) ⟩
        ((a : A) → P a → B)
          ≃⟨ invEquiv curryEquiv ⟩
        (Σ A P → B) ■

      lift' : HasLift isModal isPropIsModal (Σ A P)
      lift' = hasLift (◯ (Σ[ a ∈ A ] ◯ P a)) ηΣ (isModal-◯ _) (λ B isModalB → snd (e B isModalB))

  isModalUnit : isModal Unit*
  isModalUnit = retractIsModal Unit* (λ _ → tt*) (λ _ → refl)

  -- Lemma 1.25. (alternative proof)
  uniqueDepLift : {X : Type ℓ} {Y : X → Type ℓ} → isModal X → isModal (Σ X Y)
    → (h : A → Σ X Y) (f : ◯ A → X) (p : f ∘ η ≡ fst ∘ h)
    → isContr (Σ[ g ∈ ((z : ◯ A) → Y (f z)) ] transport (λ i → (a : A) → Y (p i a)) (g ∘ η) ≡ snd ∘ h)
  uniqueDepLift {X = X} {Y = Y} isModalX isModalΣ h f p =
      isContrΣ-2for3 (isContrLiftX h) (isOfHLevelRespectEquiv 0 (eq h) (isContrLiftΣXY h)) (f , p)
    where
      isContrLiftX : (h : A → Σ X Y) → isContr (Σ[ f ∈ (◯ A → X) ] f ∘ η ≡ fst ∘ h)
      isContrLiftX h = isModal→isContrLift isModalX (fst ∘ h)

      isContrLiftΣXY : (h : A → Σ X Y) → isContr (Σ[ h' ∈ (◯ A → Σ X Y) ] h' ∘ η ≡ h)
      isContrLiftΣXY h = isModal→isContrLift isModalΣ h

      -- we show that a lift of h : A → ΣXY is equivalent to a lift f : A → X and a lift depending on it
      eq : (h : A → Σ X Y) →
        (Σ[ h' ∈ (◯ A → Σ X Y) ] h' ∘ η ≡ h)
          ≃
        (Σ[ (f , p) ∈ (Σ[ f ∈ (◯ A → X) ] f ∘ η ≡ fst ∘ h) ] Σ[ g ∈ ((z : ◯ A) → Y (f z)) ] transport (λ i → (a : A) → Y (p i a)) (g ∘ η) ≡ snd ∘ h)
      eq {A = A} h =
        (Σ[ h' ∈ (◯ A → Σ X Y) ] h' ∘ η ≡ h)
          ≃⟨ isoToEquiv (iso
               (λ (h' , r) → (fst ∘ h' , snd ∘ h') , cong (fst ∘_) r , cong (snd ∘_) r)
               (λ ((f , g) , p , q) → (λ x → f x , g x) , λ i a → p i a , q i a)
               (λ _ → refl) (λ _ → refl)) ⟩
        (Σ[ (f , g) ∈ (Σ[ f ∈ (◯ A → X) ] ((z : ◯ A) → Y (f z))) ] Σ[ p ∈ f ∘ η ≡ fst ∘ h ] PathP (λ i → (a : A) → Y (p i a)) (g ∘ η) (snd ∘ h))
          ≃⟨ isoToEquiv (iso (λ ((f , g) , p , q) → (f , p) , g , q) (λ ((f , p) , g , q) → (f , g) , p , q) (λ _ → refl) (λ _ → refl)) ⟩
        (Σ[ (f , p) ∈ (Σ[ f ∈ (◯ A → X) ] f ∘ η ≡ fst ∘ h) ] Σ[ g ∈ ((z : ◯ A) → Y (f z)) ] PathP (λ i → (a : A) → Y (p i a)) (g ∘ η) (snd ∘ h))
          ≃⟨ Σ-cong-equiv-snd (λ (f , p) → Σ-cong-equiv-snd λ g → PathP≃Path (λ i → (a : A) → Y (p i a)) (g ∘ η) (snd ∘ h)) ⟩
        (Σ[ (f , p) ∈ (Σ[ f ∈ (◯ A → X) ] f ∘ η ≡ fst ∘ h) ] Σ[ g ∈ ((z : ◯ A) → Y (f z)) ] transport (λ i → (a : A) → Y (p i a)) (g ∘ η) ≡ snd ∘ h)  ■

      isContrΣ-2for3 : {P : A → Type ℓ} → isContr A → isContr (Σ A P) → (a : A) → isContr (P a)
      isContrΣ-2for3 p q a = isOfHLevelRespectEquiv 0 (Σ-contractFst (a , isContr→isProp p a)) q

  -- Y x is modal for all x : X of X and ΣXY are modal
  isModalΣSnd : {X : Type ℓ} {Y : X → Type ℓ} → isModal X → isModal (Σ X Y) → (x : X) → isModal (Y x)
  isModalΣSnd {X = X} {Y = Y} isModalX isModalΣ x = retractIsModal (Y x) (lem .fst) (funExt⁻ (sym (transportRefl _) ∙ lem .snd))
    where
      lem : Σ[ g ∈ (◯ (Y x) → Y x) ] transport refl (g ∘ η) ≡ idfun _
      lem = uniqueDepLift {A = Y x} isModalX isModalΣ (x ,_) (const x) refl .fst

  isModalA→isModal-≡ : (X : Type ℓ) → isModal X → (x y : X) → isModal (x ≡ y)
  isModalA→isModal-≡ X isModalX x y = isModalΣSnd {Y = x ≡_} isModalX (subst⁻ isModal (isContr→≡Unit* (isContrSingl x)) isModalUnit) y

  -- Lemma 1.26.
  isModalΠ : {A : Type ℓ} (P : A → Type ℓ) → ((a : A) → isModal (P a)) → isModal ((a : A) → P a)
  isModalΠ {A = A} P isModalP = retractIsModal ((x : A) → P x)
    (λ f x → ◯-rec (isModalP x) (_$ x) f)
    (λ f → funExt λ x → funExt⁻ (◯-rec-β (isModalP x) (_$ x)) f)

  isModal→ : (A B : Type ℓ) → isModal B → isModal (A → B)
  isModal→ A B isModalB = isModalΠ (const B) (const isModalB)

  -- We can immediately conclude that finite products are modal for Π types beeing modal
  isModal× : (A B : Type ℓ) → isModal A → isModal B → isModal (A × B)
  isModal× A B isModalA isModalB = subst⁻ isModal eq (isModalΠ _ isModalP)
    where
      A×B : Type _
      A×B = ((lift b) : Lift Bool) → if b then A else B

      isModalP : ((lift b) : Lift Bool) → isModal (if b then A else B)
      isModalP (lift false) = isModalB
      isModalP (lift true)  = isModalA

      f : A × B → A×B
      f (x , y) (lift false) = y
      f (x , y) (lift true)  = x

      g : A×B → A × B
      g p = p (lift true) , p (lift false)

      s : section f g
      s b = funExt λ where
        (lift false) → refl
        (lift true)  → refl

      eq : A × B ≡ A×B
      eq = ua (isoToEquiv (iso f g s λ _ → refl))

  -- Lemma 1.27
  ◯-preserves-× : (X Y : Type ℓ) → ◯ (X × Y) ≃ ◯ X × ◯ Y
  ◯-preserves-× X Y = ◯A≃◯'A isModal isPropIsModal (X × Y) (universalProperty (X × Y))
      (hasLift (◯ X × ◯ Y) (λ (x , y) → η x , η y) (isModal× (◯ X) (◯ Y) (isModal-◯ X) (isModal-◯ Y)) (λ Z isModalZ → eq Z isModalZ .snd))
    where
      eq : (Z : Type ℓ) → isModal Z → (◯ X × ◯ Y → Z) ≃ (X × Y → Z)
      eq Z isModalZ =
        (◯ X × ◯ Y → Z)
          ≃⟨ curryEquiv ⟩
        (◯ X → ◯ Y → Z)
          ≃⟨ _∘ η , universalProperty X .HasLift.up (◯ Y → Z) (isModal→ (◯ Y) Z isModalZ) ⟩
        (X → ◯ Y → Z)
          ≃⟨ equivΠCod (λ x → _∘ η , universalProperty Y .HasLift.up Z isModalZ) ⟩
        (X → Y → Z)
          ≃⟨ invEquiv curryEquiv ⟩
        (X × Y → Z) ■

  -- Lemma 1.28
  ◯-equiv : A ≃ B → ◯ A ≃ ◯ B
  ◯-equiv e = isoToEquiv (iso f g s r)
    where
      i = equivToIso e
      f = ◯-map (i .Iso.fun)
      g = ◯-map (i .Iso.inv)

      s : section f g
      s = funExt⁻ (sym (◯-map-∘ _ _) ∙ cong ◯-map (funExt (i .Iso.rightInv)) ∙ ◯-map-id)

      r : retract f g
      r = funExt⁻ (sym (◯-map-∘ _ _) ∙ cong ◯-map (funExt (i .Iso.leftInv)) ∙ ◯-map-id)

unquoteDecl IsReflectiveSubuniverseIsoΣ = declareRecordIsoΣ IsReflectiveSubuniverseIsoΣ (quote IsReflectiveSubuniverse)

isPropIsReflectiveSubuniverse : (M : Type ℓ → Type ℓ) → isProp (IsReflectiveSubuniverse M)
isPropIsReflectiveSubuniverse M = isOfHLevelRetractFromIso 1 IsReflectiveSubuniverseIsoΣ
  (isPropΣ (isPropΠ λ _ → isPropIsProp) λ _ → isPropΠ λ _ → isPropHasLift _ _ _)

ReflectiveSubuniverse : (ℓ : Level) → Type (ℓ-suc ℓ)
ReflectiveSubuniverse ℓ = Σ[ M ∈ (Type ℓ → Type ℓ) ] IsReflectiveSubuniverse M

-- Theorem 1.18.
ReflectiveSubuniverse≡ : (U U' : ReflectiveSubuniverse ℓ) → fst U ≡ fst U' → U ≡ U'
ReflectiveSubuniverse≡ U U' = Σ≡Prop isPropIsReflectiveSubuniverse
