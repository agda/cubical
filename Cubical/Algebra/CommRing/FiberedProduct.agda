module Cubical.Algebra.CommRing.FiberedProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

private
  variable
    ℓ : Level

module _ (A B C : CommRing ℓ) (α : CommRingHom A C) (β : CommRingHom B C) where

  private
    module A = CommRingStr (snd A)
    module B = CommRingStr (snd B)
    module C = CommRingStr (snd C)
    module α = IsCommRingHom (snd α)
    module β = IsCommRingHom (snd β)

  open CommRingStr
  open IsCommRingHom

  fbT : Type ℓ
  fbT = Σ[ ab ∈ fst A × fst B ] (fst α (fst ab) ≡ fst β (snd ab))

  fbT≡ : {x y : fbT} → fst (fst x) ≡ fst (fst y) → snd (fst x) ≡ snd (fst y) → x ≡ y
  fbT≡ h1 h2 = Σ≡Prop (λ _ → is-set (snd C) _ _) λ i → (h1 i) , (h2 i)

  0fbT : fbT
  0fbT = (A.0r , B.0r) , α.pres0 ∙ sym β.pres0

  1fbT : fbT
  1fbT = (A.1r , B.1r) , α.pres1 ∙ sym β.pres1

  _+fbT_ : fbT → fbT → fbT
  ((a1 , b1) , hab1) +fbT ((a2 , b2) , hab2) =
    (a1 A.+ a2 , b1 B.+ b2) , α.pres+ a1 a2 ∙∙ (λ i → hab1 i C.+ hab2 i) ∙∙ sym (β.pres+ b1 b2)

  _·fbT_ : fbT → fbT → fbT
  ((a1 , b1) , hab1) ·fbT ((a2 , b2) , hab2) =
    (a1 A.· a2 , b1 B.· b2) , α.pres· a1 a2 ∙∙ (λ i → hab1 i C.· hab2 i) ∙∙ sym (β.pres· b1 b2)

  -fbT_ : fbT → fbT
  -fbT ((a , b) , hab) = (A.- a , B.- b) , α.pres- a ∙∙ cong C.-_ hab ∙∙ sym (β.pres- b)

  fiberedProduct : CommRing ℓ
  fst fiberedProduct = fbT
  0r (snd fiberedProduct) = 0fbT
  1r (snd fiberedProduct) = 1fbT
  _+_ (snd fiberedProduct) = _+fbT_
  _·_ (snd fiberedProduct) = _·fbT_
  -_ (snd fiberedProduct) = -fbT_
  isCommRing (snd fiberedProduct) =
    makeIsCommRing (isSetΣSndProp (isSet× (is-set (snd A)) (is-set (snd B))) λ x → is-set (snd C) _ _)
                   (λ _ _ _ → fbT≡ (A.+Assoc _ _ _) (B.+Assoc _ _ _))
                   (λ _ → fbT≡ (A.+IdR _) (B.+IdR _))
                   (λ _ → fbT≡ (A.+InvR _) (B.+InvR _))
                   (λ _ _ → fbT≡ (A.+Comm _ _) (B.+Comm _ _))
                   (λ _ _ _ → fbT≡ (A.·Assoc _ _ _) (B.·Assoc _ _ _))
                   (λ _ → fbT≡ (A.·IdR _) (B.·IdR _))
                   (λ _ _ _ → fbT≡ (A.·DistR+ _ _ _) (B.·DistR+ _ _ _))
                   (λ _ _ → fbT≡ (A.·Comm _ _) (B.·Comm _ _))

  fiberedProductPr₁ : CommRingHom fiberedProduct A
  fst fiberedProductPr₁ = fst ∘ fst
  snd fiberedProductPr₁ = makeIsCommRingHom refl (λ _ _ → refl) (λ _ _ → refl)

  fiberedProductPr₂ : CommRingHom fiberedProduct B
  fst fiberedProductPr₂ = snd ∘ fst
  snd fiberedProductPr₂ = makeIsCommRingHom refl (λ _ _ → refl) (λ _ _ → refl)

  fiberedProductPr₁₂Commutes : compCommRingHom fiberedProductPr₁ α
                             ≡ compCommRingHom fiberedProductPr₂ β
  fiberedProductPr₁₂Commutes = CommRingHom≡ (funExt (λ x → x .snd))

  fiberedProductUnivProp :
    (D : CommRing ℓ) (h : CommRingHom D A) (k : CommRingHom D B) →
    compCommRingHom h α ≡ compCommRingHom k β →
    ∃![ l ∈ CommRingHom D fiberedProduct ]
        (h ≡ compCommRingHom l fiberedProductPr₁)
      × (k ≡ compCommRingHom l fiberedProductPr₂)
  fiberedProductUnivProp D (h , hh) (k , hk) H =
    uniqueExists f (CommRingHom≡ refl , CommRingHom≡ refl)
                 (λ _ → isProp× (isSetCommRingHom _ _ _ _) (isSetCommRingHom _ _ _ _))
                 (λ { (g , _) (Hh , Hk) →
                    CommRingHom≡ (funExt (λ d → fbT≡ (funExt⁻ (cong fst Hh) d)
                                                 (funExt⁻ (cong fst Hk) d))) })
    where
    f : CommRingHom D fiberedProduct
    fst f d = (h d , k d) , funExt⁻ (cong fst H) d
    snd f = makeIsCommRingHom (fbT≡ (hh .pres1) (hk .pres1))
                          (λ _ _ → fbT≡ (hh .pres+ _ _) (hk .pres+ _ _))
                          (λ _ _ → fbT≡ (hh .pres· _ _) (hk .pres· _ _))
