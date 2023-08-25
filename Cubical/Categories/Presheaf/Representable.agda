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

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Yoneda

private
  variable ℓ ℓ' : Level

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
