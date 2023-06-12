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

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Pullback

open import Cubical.Homotopy.Base

open import Cubical.Reflection.RecordEquiv


module Cubical.Modalities.ReflectiveSubuniverse where

module Test where

private
  variable
    ℓ : Level

module _ (isModal : Type ℓ → Type ℓ) (isPropIsModal : (A : Type ℓ) → isProp (isModal A)) where
  record HasLift (A : Type ℓ) : Type (ℓ-suc ℓ) where
    constructor hasLift
    field
      ◯A : Type ℓ
      η : A → ◯A
      isModal-◯A : isModal ◯A
      up : (B : Type ℓ) → isModal B → isEquiv (λ (g : ◯A → B) → g ∘ η)

    module _ {B : Type ℓ} (isModalB : isModal B) where
      open Iso
  
      lift≃ : Iso (◯A → B) (A → B)
      lift≃ = equivToIso (_∘ η , up B isModalB)
  
      ◯-rec : (A → B) → (◯A → B)
      ◯-rec = lift≃ .inv
  
      ◯-rec-η : (f : ◯A → B) → ◯-rec (f ∘ η) ≡ f
      ◯-rec-η f = lift≃ .leftInv f
    
      ◯-rec-β : (f : A → B) → ◯-rec f ∘ η ≡ f
      ◯-rec-β f = lift≃ .rightInv f

    -- the lifted map is unique
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

    lift-unique : (f : A → B) (g : ◯ A → B) → f ≡ g ∘ η → ◯-rec f ≡ g
    lift-unique = HasLift.lift-unique (universalProperty _) p

    η-epi : (f g : ◯ A → B) → f ∘ η ≡ g ∘ η → f ≡ g
    η-epi f g p = sym (◯-rec-η f) ∙ cong ◯-rec p ∙ ◯-rec-η g

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

  -- Lemma 1.25. (THE PROOF IN THE PAPER USES HOMOTOPY PULLBACKS)
  isModalA→IsModal≡A : isModal A → (x y : A) → isModal (x ≡ y)
  isModalA→IsModal≡A {A = A} isModalA x y = retractIsModal (x ≡ y) f {!!} -- f (λ x → cong snd (funExt⁻ fη≡id ((tt , tt) , x)))
    where
      p : {y : A} → (λ (_ : ◯ (x ≡ y)) → x) ≡ (λ (_ : ◯ (x ≡ y)) → y)
      p {y = y} = η-epi isModalA (λ _ → x) (λ _ → y) (funExt (J (λ y _ → x ≡ y) refl))

      open UniversalProperty (λ (_ : Unit) → x) (λ (_ : Unit) → y) 

      factorMap : isContr _
      factorMap = ump (◯ (x ≡ y)) (λ _ → tt) (λ _ → tt) (funExt⁻ p)

      f : ◯ (x ≡ y) → x ≡ y
      f = snd ∘ fst (fst factorMap)

      γ : (λ (_ : Unit) → x) ▪ˡ (λ _ → refl) ▪ comm ▪ʳ (λ x → _ , f x) ▪ (λ (_ : Unit) → y) ▪ˡ (λ _ → refl) ∼ funExt⁻ p
      γ = snd (snd (snd (fst factorMap)))

      γ' : comm ▪ʳ (λ x → _ , f x) ∼ funExt⁻ p
      γ' x = rUnit _ ∙ lUnit _ ∙ γ x

      β : comm ▪ʳ (λ (_ , x) → _ , f (η x)) ∼ comm
      β (_ , z) =
        comm (_ , (f (η z)))
          ≡⟨ γ' (η z) ⟩
        funExt⁻ p (η z)
          ≡⟨ refl ⟩
        funExt⁻ (η-epi isModalA (λ _ → x) (λ _ → y) (funExt (J (λ y _ → x ≡ y) refl))) (η z)
          ≡⟨ refl ⟩
        {!!} ∙ {!!} ∙ {!!}
          ≡⟨ {!!} ⟩
        comm (_ , z) ∎

      fη≡id : _ ≡ idfun (Pullback A (λ (_ : Unit) → x) (λ (_ : Unit) → y))
      fη≡id = cong fst $ isContr→isProp (ump (Pullback A (λ (_ : Unit) → x) (λ (_ : Unit) → y)) pr₁ pr₂ comm)
        ((λ (_ , x) → (tt , tt) , f (η x)) , (λ _ → isPropUnit _ _) , (λ _ → isPropUnit _ _) , λ x → (sym (lUnit _) ∙ sym (rUnit _)) ∙ β x)
        (idfun _ , (λ _ → refl) , (λ _ → refl) , λ x → sym (lUnit _) ∙ sym (rUnit _)) -- TODO: move!

      -- f : {y : A} → ◯ (x ≡ y) → x ≡ y
      -- f z = J (λ y _ → x ≡ y) refl (funExt⁻ p z)

      -- fη≡id : (λ (_ , x) → (tt , tt) , f (η x)) ≡ idfun _
      -- fη≡id = cong fst $ isContr→isProp (ump (Pullback A (λ (_ : Unit) → x) (λ (_ : Unit) → y)) pr₁ pr₂ comm)
      --           ((λ (_ , x) → (tt , tt) , f (η x)) , (λ _ → isPropUnit _ _) , (λ _ → isPropUnit _ _) ,
      --             λ z → sym (lUnit _) ∙ sym (rUnit _) ∙
      --               let l : ((comm ▪ʳ λ (_ , y) → (tt , tt) , (f (η y))) z ≡ comm z) ; l = {!!} in l
      --               ) -- prop/set argument
      --           (idfun _ , (λ _ → refl) , (λ _ → refl) , λ x → sym (lUnit _) ∙ sym (rUnit _)) -- TODO: move!
      --   where open UniversalProperty (λ (_ : Unit) → x) (λ (_ : Unit) → y) 
        

      -- plem1 : funExt⁻ p (η refl) ≡ refl
      -- plem1 =
      --   funExt⁻ (η-mono isModalA (λ _ → x) (λ _ → x) (funExt (J (λ y _ → x ≡ y) refl))) (η refl)
      --     ≡⟨ refl ⟩
      --   funExt⁻ (sym (◯-rec-η isModalA (λ _ → x)) ∙ cong (◯-rec isModalA) (funExt (J (λ y _ → x ≡ y) refl)) ∙ ◯-rec-η isModalA (λ _ → x)) (η refl)
      --     ≡⟨ refl ⟩
      --   funExt⁻ (sym (◯-rec-η isModalA (λ _ → x))) (η refl)
      --     ∙ funExt⁻ (cong (◯-rec isModalA) (funExt (J (λ y _ → x ≡ y) refl))) (η refl)
      --     ∙ funExt⁻ (◯-rec-η isModalA (λ _ → x)) (η refl)
      --     ≡⟨ refl ⟩
      --   funExt⁻ (sym (◯-rec-η isModalA (λ _ → x))) (η refl)
      --     ∙ cong (λ t → ◯-rec isModalA t (η refl)) (funExt (J (λ y _ → x ≡ y) refl))
      --     ∙ funExt⁻ (◯-rec-η isModalA (λ _ → x)) (η refl)
      --     ≡⟨ {!!} ⟩
      --   funExt⁻ (sym (◯-rec-η isModalA (λ _ → x))) (η refl)
      --     ∙ refl
      --     ∙ funExt⁻ (◯-rec-η isModalA (λ _ → x)) (η (refl {x = x}))
      --     ≡⟨ {!!} ⟩
      --   refl ∎


      -- -- 2.3.11 should apply
      -- plem2 : Path (◯-rec isModalA (λ _ → x) (η refl) ≡ ◯-rec isModalA (λ _ → x) (η refl))
      --   (cong (λ t → ◯-rec isModalA t (η refl)) (funExt (J (λ y _ → x ≡ y) refl))) refl
      -- plem2 = let q = sym $ ◯-rec-β isModalA (λ _ → x) ≡$ refl in 
      --   congS (λ t → ◯-rec isModalA t (η refl)) (funExt (J (λ y _ → x ≡ y) refl))
      --     ≡⟨ sym (substSubst⁻ (λ x → x ≡ x) q (congS (λ t → ◯-rec isModalA t (η refl)) (funExt (J (λ y _ → x ≡ y) refl)))) ⟩
      --   subst (λ x → x ≡ x) q (subst (λ x → x ≡ x) (sym q) (congS (λ t → ◯-rec isModalA t (η refl)) (funExt (J (λ y _ → x ≡ y) refl))))

      --     ≡⟨ cong (subst (λ x → x ≡ x) q) {!!} ⟩
      --   {!!}
      --   --   ≡⟨ cong (subst (λ x → x ≡ x) q) (substInPaths (idfun _) (idfun _) (sym q)
      --   --             (congS (λ t → ◯-rec isModalA t (η refl)) (funExt (J (λ y _ → x ≡ y) refl)))) ⟩
      --   -- subst (λ x → x ≡ x) q (q ∙ congS (λ t → ◯-rec isModalA t (η refl)) (funExt (J (λ y _ → x ≡ y) refl)) ∙ sym q)

      --     ≡⟨ cong (subst (λ x → x ≡ x) q) {!!} ⟩
      --   subst (λ x → x ≡ x) q (congS (λ t → t refl) (funExt {A = x ≡ x} (J (λ y _ → x ≡ y) refl)))
      --     ≡⟨ refl ⟩
      --   subst (λ x → x ≡ x) q (J (λ y _ → x ≡ y) refl refl)
      --     ≡⟨ cong (subst (λ x → x ≡ x) q) (JRefl (λ y _ → x ≡ y) refl) ⟩
      --   subst (λ x → x ≡ x) q refl
      --     ≡⟨ substInPaths (idfun A) (idfun A) q refl ⟩
      --   sym q ∙ refl ∙ q
      --     ≡⟨ cong (sym q ∙_) (sym (lUnit q)) ⟩
      --   sym q ∙ q
      --     ≡⟨ lCancel q ⟩
      --   refl ∎

      -- fη≡id : f (η refl) ≡ refl
      -- fη≡id =
      --   J (λ y _ → x ≡ y) refl (funExt⁻ p (η refl))
      --     ≡⟨ cong (J (λ y _ → x ≡ y) refl) plem1 ⟩
      --   J (λ y _ → x ≡ y) refl refl
      --     ≡⟨ JRefl (λ y _ → x ≡ y) refl ⟩
      --   refl ∎


  -- EXERCISE,  MOVE
  isModal× : (A B : Type ℓ) → isModal A → isModal B → isModal (A × B)
  isModal× A B isModalA isModalB = retractIsModal (A × B) f inv
    where
      f : ◯ (A × B) → A × B
      f z = ◯-rec isModalA fst z , ◯-rec isModalB snd z

      inv : retract η f
      inv z =
        ◯-rec isModalA fst (η z) , ◯-rec isModalB snd (η z)
          ≡⟨ ≡-× (◯-rec-β isModalA fst ≡$ z) (◯-rec-β isModalB snd ≡$ z) ⟩
        (fst z , snd z) ∎

unquoteDecl IsReflectiveSubuniverseIsoΣ = declareRecordIsoΣ IsReflectiveSubuniverseIsoΣ (quote IsReflectiveSubuniverse)

IsPropIsReflectiveSubuniverse : (M : Type ℓ → Type ℓ) → isProp (IsReflectiveSubuniverse M)
IsPropIsReflectiveSubuniverse M = isOfHLevelRetractFromIso 1 IsReflectiveSubuniverseIsoΣ
  (isPropΣ (isPropΠ λ _ → isPropIsProp) λ _ → isPropΠ λ _ → isPropHasLift _ _ _)

ReflectiveSubuniverse : (ℓ : Level) → Type (ℓ-suc ℓ)
ReflectiveSubuniverse ℓ = Σ[ M ∈ (Type ℓ → Type ℓ) ] IsReflectiveSubuniverse M

-- Theorem 1.18.
ReflectiveSubuniverse≡ : (U U' : ReflectiveSubuniverse ℓ) → fst U ≡ fst U' → U ≡ U'
ReflectiveSubuniverse≡ U U' = Σ≡Prop IsPropIsReflectiveSubuniverse

