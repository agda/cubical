{-# OPTIONS --safe #-}
{-

    This file defines 3 equivalent formulations of when a presheaf P is
    representable:

    1. When there is a natural isomorphism with some representable C [-, A ]

    2. When there is a terminal element of the category of elements of P

    3. When there is a universal element η ∈ P A, i.e., that composing with
       η is an equivalence between P B and C [ B , A ].

    The equivalence between 2 and 3 is mostly currying/symmetry of
    equations. The equivalence between 1 and 3 follows from the Yoneda
    lemma.

    3 is the most convenient to construct in applications and so is
    implemented with a custom record type UniversalElement and is
    generally preferable when formulating universal properties.

-}
module Cubical.Categories.Presheaf.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism hiding (compIso ; invIso)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Yoneda

private
  variable ℓ ℓ' ℓS ℓS' : Level

open Category
open Contravariant
open NatIso
open isIsoC

-- | A representation of a presheaf is an object whose image under the
-- | Yoneda embedding is isomorphic to P
-- | We define only the maximally universe polymorphic version, the
-- | Lifts don't appear in practice because we usually use universal
-- | elements instead
module _ {ℓo}{ℓh}{ℓp} (C : Category ℓo ℓh) (P : Presheaf C ℓp) where
  Representation : Type (ℓ-max (ℓ-max ℓo (ℓ-suc ℓh)) (ℓ-suc ℓp))
  Representation =
    Σ[ A ∈ C .ob ] PshIso C (C [-, A ]) P

  Representable : Type (ℓ-max (ℓ-max ℓo (ℓ-suc ℓh)) (ℓ-suc ℓp))
  Representable = ∥ Representation ∥₁

  Elements = ∫ᴾ_ {C = C} P

  TerminalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  TerminalElement = Terminal Elements

  hasTerminalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  hasTerminalElement = ∥ TerminalElement ∥₁

  isUniversal : (vertex : C .ob) (element : (P ⟅ vertex ⟆) .fst)
              → Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  isUniversal vertex element =
    ∀ A → isEquiv λ (f : C [ A , vertex ]) → element ∘ᴾ⟨ C , P ⟩ f

  isPropIsUniversal : ∀ vertex element → isProp (isUniversal vertex element)
  isPropIsUniversal vertex element = isPropΠ (λ _ → isPropIsEquiv _)

  record UniversalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp) where
    field
      vertex : C .ob
      element : (P ⟅ vertex ⟆) .fst
      universal : isUniversal vertex element

  unquoteDecl UniversalElementIsoΣ =
    declareRecordIsoΣ UniversalElementIsoΣ (quote UniversalElement)

  hasUniversalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  hasUniversalElement = ∥ UniversalElement ∥₁

  open UniversalElement

  -- | The equivalence between Representation and UniversalElement is
  -- | a corollary of the Yoneda lemma
  representationToUniversalElement : Representation → UniversalElement
  representationToUniversalElement repr .vertex = repr .fst
  representationToUniversalElement repr .element =
    Iso.fun (yonedaᴾ* {C = C} P (repr .fst)) (repr .snd .trans)
  representationToUniversalElement repr .universal A =
    transport (λ i → isEquiv (lem i)) (isoToIsEquiv anIso)
    where
    lem :
      Path (C [ A , repr .fst ] → _)
      (λ f → (repr .snd .trans ⟦ A ⟧) (lift f) .lower)
      (λ f → (Iso.inv (yonedaᴾ* {C = C} P (repr .fst))
             (Iso.fun (yonedaᴾ* P (repr .fst))
                      (repr .snd .trans)) ⟦ A ⟧)
             (lift f) .lower)
    lem = funExt (λ f i →
      (yonedaᴾ* {C = C} P (repr .fst)
        .Iso.leftInv (repr .snd .trans) (~ i) ⟦ A ⟧)
      (lift f) .lower)

    anIso : Iso (C [ A , repr .fst ]) (fst (Functor.F-ob P A))
    anIso .Iso.fun f = (repr .snd .trans ⟦ A ⟧) (lift f) .lower
    anIso .Iso.inv p = repr .snd .nIso A .inv (lift p) .lower
    anIso .Iso.rightInv b =
      cong lower (funExt⁻ (repr .snd .nIso A .sec) (lift b))
    anIso .Iso.leftInv a =
      cong lower (funExt⁻ (repr .snd .nIso A .ret) (lift a))

  universalElementToRepresentation : UniversalElement → Representation
  universalElementToRepresentation η .fst = η .vertex
  universalElementToRepresentation η .snd .trans =
    yonedaᴾ* {C = C} P (η .vertex) .Iso.inv (η .element)
  universalElementToRepresentation η .snd .nIso A .inv ϕ =
    lift (invIsEq (η .universal A) (ϕ .lower))
  universalElementToRepresentation η .snd .nIso A .sec = funExt (λ ϕ →
    cong lift (secIsEq (η .universal A) (ϕ .lower)))
  universalElementToRepresentation η .snd .nIso A .ret = funExt (λ f →
    cong lift (retIsEq (η .universal A) (f .lower)))

  Representation≅UniversalElement : Iso Representation UniversalElement
  Representation≅UniversalElement .Iso.fun = representationToUniversalElement
  Representation≅UniversalElement .Iso.inv = universalElementToRepresentation
  Representation≅UniversalElement .Iso.rightInv η =
    isoFunInjective UniversalElementIsoΣ _ _
      (ΣPathP (refl , (Σ≡Prop (λ _ → isPropIsUniversal _ _)
      (yonedaᴾ* {C = C} P (η .vertex) .Iso.rightInv (η .element)))))
  Representation≅UniversalElement .Iso.leftInv repr =
    ΣPathP (refl ,
    (NatIso≡ (cong NatTrans.N-ob
      (yonedaᴾ* {C = C} P (repr .fst) .Iso.leftInv (repr .snd .trans)))))

  isTerminalToIsUniversal : ∀ {η : Elementᴾ {C = C} P}
    → isTerminal Elements η → isUniversal (η .fst) (η .snd)
  isTerminalToIsUniversal {η} term A .equiv-proof ϕ .fst .fst =
    term (_ , ϕ) .fst .fst
  isTerminalToIsUniversal {η} term A .equiv-proof ϕ .fst .snd =
    term (_ , ϕ) .fst .snd
  isTerminalToIsUniversal {η} term A .equiv-proof ϕ .snd (f , commutes) =
    Σ≡Prop (λ _ → (P ⟅ A ⟆) .snd _ _)
           (cong fst (term (A , ϕ) .snd (f , commutes)))

  isUniversalToIsTerminal :
    ∀ (vertex : C .ob) (element : (P ⟅ vertex ⟆) .fst)
    → isUniversal vertex element
    → isTerminal Elements (vertex , element)
  isUniversalToIsTerminal vertex element universal ϕ .fst .fst =
    universal _ .equiv-proof (ϕ .snd) .fst .fst
  isUniversalToIsTerminal vertex element universal ϕ .fst .snd =
    universal _ .equiv-proof (ϕ .snd) .fst .snd
  isUniversalToIsTerminal vertex element universal ϕ .snd (f , commutes) =
    Σ≡Prop
      (λ _ → (P ⟅ _ ⟆) .snd _ _)
      (cong fst (universal _ .equiv-proof (ϕ .snd) .snd (f , commutes)))

  terminalElementToUniversalElement : TerminalElement → UniversalElement
  terminalElementToUniversalElement η .vertex = η .fst .fst
  terminalElementToUniversalElement η .element = η .fst .snd
  terminalElementToUniversalElement η .universal =
    isTerminalToIsUniversal (η .snd)

  universalElementToTerminalElement : UniversalElement → TerminalElement
  universalElementToTerminalElement η .fst .fst = η .vertex
  universalElementToTerminalElement η .fst .snd = η .element
  universalElementToTerminalElement η .snd =
    isUniversalToIsTerminal (η .vertex) (η .element) (η .universal)

  TerminalElement≅UniversalElement : Iso TerminalElement UniversalElement
  TerminalElement≅UniversalElement .Iso.fun = terminalElementToUniversalElement
  TerminalElement≅UniversalElement .Iso.inv = universalElementToTerminalElement
  TerminalElement≅UniversalElement .Iso.rightInv η =
    isoFunInjective UniversalElementIsoΣ _ _
    (ΣPathP (refl , (Σ≡Prop (λ _ → isPropIsUniversal _ _) refl)))
  TerminalElement≅UniversalElement .Iso.leftInv η =
    Σ≡Prop (isPropIsTerminal Elements) refl

  Representation≅TerminalElement : Iso Representation TerminalElement
  Representation≅TerminalElement =
    compIso
      Representation≅UniversalElement
      (invIso TerminalElement≅UniversalElement)

-- Isomorphism between presheaves of different levels
PshIso' : (C : Category ℓ ℓ')
         (P : Presheaf C ℓS)
         (Q : Presheaf C ℓS') → Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓS) ℓS')
PshIso' {ℓS = ℓS}{ℓS' = ℓS'} C P Q =
  CatIso (FUNCTOR (C ^op) (SET (ℓ-max ℓS ℓS')))
    (LiftF {ℓ = ℓS}{ℓ' = ℓS'} ∘F P)
    (LiftF {ℓ = ℓS'}{ℓ' = ℓS} ∘F Q)

IdPshIso : (C : Category ℓ ℓ') (P : Presheaf C ℓS) → PshIso' C P P
IdPshIso C P = idCatIso

𝓟o = Presheaf

𝓟* : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
𝓟* C ℓS = Functor C (SET ℓS)

module _ (C : Category ℓ ℓ') (c : C .ob) where
  open Category
  open UniversalElement

  selfUnivElt :  UniversalElement C (C [-, c ])
  selfUnivElt .vertex = c
  selfUnivElt .element = C .id
  selfUnivElt .universal A = isoToIsEquiv (iso _ (λ z → z)
    (C .⋆IdR)
    (C .⋆IdR))

  selfUnivEltᵒᵖ : UniversalElement (C ^op) (C [ c ,-])
  selfUnivEltᵒᵖ .vertex = c
  selfUnivEltᵒᵖ .element = C .id
  selfUnivEltᵒᵖ .universal _ = isoToIsEquiv (iso _ (λ z → z)
    (C .⋆IdL)
    (C .⋆IdL))

module _ {ℓo}{ℓh}{ℓp} (C : Category ℓo ℓh) (P : Presheaf C ℓp) where
  open UniversalElement

  UniversalElementOn : C .ob → Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  UniversalElementOn vertex =
    Σ[ element ∈ (P ⟅ vertex ⟆) .fst ] isUniversal C P vertex element

  UniversalElementToUniversalElementOn :
    (ue : UniversalElement C P) → UniversalElementOn (ue .vertex)
  UniversalElementToUniversalElementOn ue .fst = ue .element
  UniversalElementToUniversalElementOn ue .snd = ue .universal

module UniversalElementNotation {ℓo}{ℓh}
       {C : Category ℓo ℓh} {ℓp} {P : Presheaf C ℓp}
       (ue : UniversalElement C P)
       where
  open UniversalElement ue
  open NatTrans
  open NatIso
  REPR : Representation C P
  REPR = universalElementToRepresentation C P ue

  unIntroNT : NatTrans (LiftF {ℓ' = ℓp} ∘F (C [-, vertex ]))
                       (LiftF {ℓ' = ℓh} ∘F P)
  unIntroNT = REPR .snd .trans

  introNI : NatIso (LiftF {ℓ' = ℓh} ∘F P) (LiftF {ℓ' = ℓp} ∘F (C [-, vertex ]))
  introNI = symNatIso (REPR .snd)

  intro : ∀ {c} → ⟨ P ⟅ c ⟆ ⟩ → C [ c , vertex ]
  intro p = universal _ .equiv-proof p .fst .fst

  β : ∀ {c} → {p : ⟨ P ⟅ c ⟆ ⟩} → (element ∘ᴾ⟨ C , P ⟩ intro p) ≡ p
  β {p = p} = universal _ .equiv-proof p .fst .snd

  η : ∀ {c} → {f : C [ c , vertex ]} → f ≡ intro (element ∘ᴾ⟨ C , P ⟩ f)
  η {f = f} = cong fst (sym (universal _ .equiv-proof (element ∘ᴾ⟨ C , P ⟩ f)
    .snd (_ , refl)))

  weak-η : C .id ≡ intro element
  weak-η = η ∙ cong intro (∘ᴾId C P _)

  extensionality : ∀ {c} → {f f' : C [ c , vertex ]}
                 → (element ∘ᴾ⟨ C , P ⟩ f) ≡ (element ∘ᴾ⟨ C , P ⟩ f')
                 → f ≡ f'
  extensionality = isoFunInjective (equivToIso (_ , (universal _))) _ _

  intro-natural : ∀ {c' c} → {p : ⟨ P ⟅ c ⟆ ⟩}{f : C [ c' , c ]}
                → intro p ∘⟨ C ⟩ f ≡ intro (p ∘ᴾ⟨ C , P ⟩ f)
  intro-natural = extensionality
    ( (∘ᴾAssoc C P _ _ _
    ∙ cong (action C P _) β)
    ∙ sym β)

module _
  {C : Category ℓ ℓ'} (isUnivC : isUnivalent C) (P : Presheaf C ℓS) where
  open Contravariant
  isPropUniversalElement : isProp (UniversalElement C P)
  isPropUniversalElement = isOfHLevelRetractFromIso 1
    (invIso (TerminalElement≅UniversalElement C P))
    (isPropTerminal (∫ᴾ_ {C = C} P)
    (isUnivalentOp (isUnivalent∫ (isUnivalentOp isUnivC) P)))
