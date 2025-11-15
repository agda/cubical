{-

This file contains:

- Definition of functions of the equivalence between FreeGroup and the FundamentalGroup
- Definition of encode decode functions
- Proof that for all x : Bouquet A → p : base ≡ x → decode x (encode x p) ≡ p (no truncations)
- Proof of the truncated versions of encodeDecode and of right-homotopy
- Definition of truncated encode decode functions
- Proof of the truncated versions of decodeEncode and encodeDecode
- Proof that π₁Bouquet ≡ FreeGroup A

-}

module Cubical.HITs.Bouquet.FundamentalGroupProof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws renaming (assoc to pathAssoc)
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Morphism

open import Cubical.Data.Nat hiding (_·_ ; elim)
open import Cubical.Data.Fin.Inductive

open import Cubical.HITs.Bouquet.Discrete
open import Cubical.HITs.FreeGroup as FG hiding (winding ; elimProp)
open import Cubical.HITs.FreeGroupoid.Base as FGrp
open import Cubical.HITs.SetTruncation as ST hiding (rec2)
open import Cubical.HITs.PropositionalTruncation hiding (map ; elim) renaming (rec to propRec)
open import Cubical.HITs.Bouquet.Base
open import Cubical.HITs.Bouquet.Properties
open import Cubical.HITs.FreeGroupoid
open import Cubical.HITs.SphereBouquet.Base

open import Cubical.Algebra.Group

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level
    A : Type ℓ

-- Pointed versions of the non truncated types

ΩBouquet : {A : Type ℓ} → Pointed ℓ
ΩBouquet {A = A} = Ω (Bouquet∙ A)

FreeGroupoid∙ : {A : Type ℓ} → Pointed ℓ
FreeGroupoid∙ {A = A} = FreeGroupoid A , ε

-- Functions without using the truncated forms of types

looping : FreeGroupoid A → typ ΩBouquet
looping (η a)              = loop a
looping (g1 · g2)          = looping g1 ∙ looping g2
looping ε                  = refl
looping (inv g)            = sym (looping g)
looping (assoc g1 g2 g3 i) = pathAssoc (looping g1) (looping g2) (looping g3) i
looping (idr g i)          = rUnit (looping g) i
looping (idl g i)          = lUnit (looping g) i
looping (invr g i)         = rCancel (looping g) i
looping (invl g i)         = lCancel (looping g) i

looping∙ : FreeGroupoid∙ →∙ ΩBouquet {A = A}
looping∙ = looping , refl

code : {A : Type ℓ} → (Bouquet A) → Type ℓ
code {A = A} base = (FreeGroupoid A)
code (loop a i)   = pathsInU (η a) i

winding : typ ΩBouquet → FreeGroupoid A
winding l = subst code l ε

winding∙ : ΩBouquet →∙ FreeGroupoid∙ {A = A}
winding∙ = winding , refl

-- Functions using the truncated forms of types

π₁Bouquet : {A : Type ℓ} → Type ℓ
π₁Bouquet {A = A} = π 1 (Bouquet∙ A)

loopingT : ∥ FreeGroupoid A ∥₂ → π₁Bouquet
loopingT = map looping

windingT : π₁Bouquet → ∥ FreeGroupoid A ∥₂
windingT = map winding

-- Utility proofs

substPathsR : {C : Type ℓ}{y z : C} → (x : C) → (p : y ≡ z) → subst (λ y → x ≡ y) p ≡ λ q → q ∙ p
substPathsR {y = y} x p = funExt homotopy where
  homotopy : ∀ q → subst (λ y → x ≡ y) p q ≡ q ∙ p
  homotopy q = J P d p where
    P : ∀ z' → y ≡ z' → Type _
    P z' p' = subst (λ y → x ≡ y) p' q ≡ q ∙ p'
    d : P y refl
    d =
      subst (λ y → x ≡ y) refl q
      ≡⟨ substRefl {B = λ y → x ≡ y} q ⟩
      q
      ≡⟨ rUnit q ⟩
      q ∙ refl ∎

substFunctions : {B C : A → Type ℓ}{x y : A}
                  → (p : x ≡ y)
                  → (f : B x → C x)
                  → subst (λ z → (B z → C z)) p f ≡ subst C p ∘ f ∘ subst B (sym p)
substFunctions {B = B} {C = C} {x = x} p f =  J P d p where
  auxC : idfun (C x) ≡ subst C refl
  auxC = funExt (λ c → sym (substRefl {B = C} c))
  auxB : idfun (B x) ≡ subst B refl
  auxB = funExt (λ b → sym (substRefl {B = B} b))
  P : ∀ y' → x ≡ y' → Type _
  P y' p' = subst (λ z → (B z → C z)) p' f ≡ subst C p' ∘ f ∘ subst B (sym p')
  d : P x refl
  d =
    subst (λ z → (B z → C z)) refl f
    ≡⟨ substRefl {B = λ z → (B z → C z)} f ⟩
    f
    ≡⟨ cong (λ h → h ∘ f ∘ idfun (B x)) auxC ⟩
    subst C refl ∘ f ∘ idfun (B x)
    ≡⟨ cong (λ h → subst C refl ∘ f ∘ h) auxB ⟩
    subst C refl ∘ f ∘ subst B (sym refl) ∎

-- Definition of the encode - decode functions over the family of types Π(x : W A) → code x

encode : (x : Bouquet A) → base ≡ x → code x
encode x l = subst code l ε

decode : {A : Type ℓ}(x : Bouquet A) → code x → base ≡ x
decode {A = A} base       = looping
decode {A = A} (loop a i) = path i where
  pathover : PathP (λ i → (code (loop a i) → base ≡ (loop a i))) looping (subst (λ z → (code z → base ≡ z)) (loop a) looping)
  pathover = subst-filler (λ z → (code z → base ≡ z)) (loop a) looping
  aux : (a : A) → subst code (sym (loop a)) ≡ action (inv (η a))
  aux a = funExt homotopy where
    homotopy : ∀ (g : FreeGroupoid A) → subst code (sym (loop a)) g ≡ action (inv (η a)) g
    homotopy g =
      subst code (sym (loop a)) g
      ≡⟨ cong (λ x → transport x g) (sym (invPathsInUNaturality (η a))) ⟩
      transport (pathsInU (inv (η a))) g
      ≡⟨ uaβ  (equivs (inv (η a))) g ⟩
      action (inv (η a)) g ∎
  calculations : ∀ (a : A) → ∀ g → looping (g · (inv (η a))) ∙ loop a ≡ looping g
  calculations a g =
    looping (g · (inv (η a))) ∙ loop a
    ≡⟨ sym (pathAssoc (looping g) (sym (loop a)) (loop a)) ⟩
    looping g ∙ (sym (loop a) ∙ loop a)
    ≡⟨ cong (λ x → looping g ∙ x) (lCancel (loop a)) ⟩
    looping g ∙ refl
    ≡⟨ sym (rUnit (looping g)) ⟩
    looping g ∎
  path' : subst (λ z → (code z → base ≡ z)) (loop a) looping ≡ looping
  path' =
    subst (λ z → (code z → base ≡ z)) (loop a) looping
    ≡⟨ substFunctions {B = code} {C = λ z → base ≡ z} (loop a) looping ⟩
    subst (λ z → base ≡ z) (loop a) ∘ looping ∘ subst code (sym (loop a))
    ≡⟨ cong (λ x → x ∘ looping ∘ subst code (sym (loop a))) (substPathsR base (loop a)) ⟩
    (λ p → p ∙ loop a) ∘ looping ∘ subst code (sym (loop a))
    ≡⟨ cong (λ x → (λ p → p ∙ loop a) ∘ looping ∘ x) (aux a) ⟩
    (λ p → p ∙ loop a) ∘ looping ∘ action (inv (η a))
    ≡⟨ funExt (calculations a) ⟩
    looping ∎
  path'' : PathP (λ i → code ((loop a ∙ refl) i) → base ≡ ((loop a ∙ refl) i)) looping looping
  path'' = compPathP' {A = Bouquet A} {B = λ z → code z → base ≡ z} pathover path'
  p''≡p : PathP (λ i → code ((loop a ∙ refl) i) → base ≡ ((loop a ∙ refl) i)) looping looping ≡
          PathP (λ i → code (loop a i) → base ≡ (loop a i)) looping looping
  p''≡p = cong (λ x → PathP (λ i → code (x i) → base ≡ (x i)) looping looping) (sym (rUnit (loop a)))
  path : PathP (λ i → code (loop a i) → base ≡ (loop a i)) looping looping
  path = transport p''≡p path''

-- Non truncated Left Homotopy

decodeEncode : (x : Bouquet A) → (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode x p = J P d p where
  P : (x' : Bouquet A) → base ≡ x' → Type _
  P x' p' = decode x' (encode x' p') ≡ p'
  d : P base refl
  d =
    decode base (encode base refl)
    ≡⟨ cong (λ e' → looping e') (transportRefl ε) ⟩
    refl ∎

left-homotopy : ∀ (l : typ (ΩBouquet {A = A})) → looping (winding l) ≡ l
left-homotopy l = decodeEncode base l

-- Truncated proofs of right homotopy of winding/looping functions

truncatedPathEquality : (g : FreeGroupoid A) → ∥ cong code (looping g) ≡ ua (equivs g) ∥₁
truncatedPathEquality = elimProp
            Bprop
            (λ a → ∣ η-ind a ∣₁)
            (λ g1 g2 → λ ∣ind1∣₁ ∣ind2∣₁ → rec2 squash₁ (λ ind1 ind2 → ∣ ·-ind g1 g2 ind1 ind2 ∣₁) ∣ind1∣₁ ∣ind2∣₁)
            ∣ ε-ind ∣₁
            (λ g → λ ∣ind∣₁ → propRec squash₁ (λ ind → ∣ inv-ind g ind ∣₁) ∣ind∣₁) where
  B : ∀ g → Type _
  B g = cong code (looping g) ≡ ua (equivs g)
  Bprop : ∀ g → isProp ∥ B g ∥₁
  Bprop g = squash₁
  η-ind : ∀ a → B (η a)
  η-ind a = refl
  ·-ind : ∀ g1 g2 → B g1 → B g2 → B (g1 · g2)
  ·-ind g1 g2 ind1 ind2 =
    cong code (looping (g1 · g2))
    ≡⟨ cong (λ x → x ∙ cong code (looping g2)) ind1 ⟩
    pathsInU g1 ∙ cong code (looping g2)
    ≡⟨ cong (λ x → pathsInU g1 ∙ x) ind2 ⟩
    pathsInU g1 ∙ pathsInU g2
    ≡⟨ sym (multPathsInUNaturality g1 g2) ⟩
    pathsInU (g1 · g2) ∎
  ε-ind : B ε
  ε-ind =
    cong code (looping ε)
    ≡⟨ sym idPathsInUNaturality ⟩
    pathsInU ε ∎
  inv-ind : ∀ g → B g → B (inv g)
  inv-ind g ind =
    cong code (looping (inv g))
    ≡⟨ cong sym ind ⟩
    sym (pathsInU g)
    ≡⟨ sym (invPathsInUNaturality g) ⟩
    ua (equivs (inv g)) ∎

truncatedRight-homotopy : (g : FreeGroupoid A) → ∥ winding (looping g) ≡ g ∥₁
truncatedRight-homotopy g = propRec squash₁ recursion (truncatedPathEquality g) where
  recursion : cong code (looping g) ≡ ua (equivs g) → ∥ winding (looping g) ≡ g ∥₁
  recursion hyp = ∣ aux ∣₁ where
    aux : winding (looping g) ≡ g
    aux =
      winding (looping g)
      ≡⟨ cong (λ x → transport x ε) hyp ⟩
      transport (ua (equivs g)) ε
      ≡⟨ uaβ  (equivs g) ε ⟩
      ε · g
      ≡⟨ sym (idl g) ⟩
      g ∎

right-homotopyInTruncatedGroupoid : (g : FreeGroupoid A) → ∣ winding (looping g) ∣₂ ≡ ∣ g ∣₂
right-homotopyInTruncatedGroupoid g = Iso.inv PathIdTrunc₀Iso (truncatedRight-homotopy g)

-- Truncated encodeDecode over all fibrations

truncatedEncodeDecode : (x : Bouquet A) → (g : code x) → ∥ encode x (decode x g) ≡ g ∥₁
truncatedEncodeDecode base = truncatedRight-homotopy
truncatedEncodeDecode (loop a i) = isProp→PathP prop truncatedRight-homotopy truncatedRight-homotopy i where
  prop : ∀ i → isProp (∀ (g : code (loop a i)) → ∥ encode (loop a i) (decode (loop a i) g) ≡ g ∥₁)
  prop i f g = funExt pointwise where
    pointwise : (x : code (loop a i)) → PathP (λ _ → ∥ encode (loop a i) (decode (loop a i) x) ≡ x ∥₁) (f x) (g x)
    pointwise x = isProp→PathP (λ i → squash₁) (f x) (g x)

encodeDecodeInTruncatedGroupoid : (x : Bouquet A) → (g : code x) → ∣ encode x (decode x g) ∣₂ ≡ ∣ g ∣₂
encodeDecodeInTruncatedGroupoid x g = Iso.inv PathIdTrunc₀Iso (truncatedEncodeDecode x g)

-- Encode Decode over the truncated versions of the types

encodeT : (x : Bouquet A) → ∥ base ≡ x ∥₂ → ∥ code x ∥₂
encodeT x = map (encode x)

decodeT : (x : Bouquet A) → ∥ code x ∥₂ → ∥ base ≡ x ∥₂
decodeT x = map (decode x)

decodeEncodeT : (x : Bouquet A) → (p : ∥ base ≡ x ∥₂) → decodeT x (encodeT x p) ≡ p
decodeEncodeT x g = elim sethood induction g where
  sethood : (q : ∥ base ≡ x ∥₂) → isSet (decodeT x (encodeT x q) ≡ q)
  sethood q = isProp→isSet (squash₂ (decodeT x (encodeT x q)) q)
  induction : (l : base ≡ x) → ∣ decode x (encode x l) ∣₂ ≡ ∣ l ∣₂
  induction l = cong (λ l' → ∣ l' ∣₂) (decodeEncode x l)

encodeDecodeT : (x : Bouquet A) → (g : ∥ code x ∥₂) → encodeT x (decodeT x g) ≡ g
encodeDecodeT x g = elim sethood induction g where
  sethood : (z : ∥ code x ∥₂) → isSet (encodeT x (decodeT x z) ≡ z)
  sethood z = isProp→isSet (squash₂ (encodeT x (decodeT x z)) z)
  induction : (a : code x) → ∣ encode x (decode x a) ∣₂ ≡ ∣ a ∣₂
  induction a = encodeDecodeInTruncatedGroupoid x a

-- Final equivalences

TruncatedFamiliesIso : (x : Bouquet A) → Iso ∥ base ≡ x ∥₂ ∥ code x ∥₂
Iso.fun (TruncatedFamiliesIso x)      = encodeT x
Iso.inv (TruncatedFamiliesIso x)      = decodeT x
Iso.rightInv (TruncatedFamiliesIso x) = encodeDecodeT x
Iso.leftInv (TruncatedFamiliesIso x)  = decodeEncodeT x

TruncatedFamiliesEquiv : (x : Bouquet A) → ∥ base ≡ x ∥₂ ≃ ∥ code x ∥₂
TruncatedFamiliesEquiv x = isoToEquiv (TruncatedFamiliesIso x)

TruncatedFamilies≡ : (x : Bouquet A) → ∥ base ≡ x ∥₂ ≡ ∥ code x ∥₂
TruncatedFamilies≡ x = ua (TruncatedFamiliesEquiv x)

π₁Bouquet≡∥FreeGroupoid∥₂ : π₁Bouquet ≡ ∥ FreeGroupoid A ∥₂
π₁Bouquet≡∥FreeGroupoid∥₂ = TruncatedFamilies≡ base

π₁Bouquet≡FreeGroup : {A : Type ℓ} → π₁Bouquet ≡ FreeGroup A
π₁Bouquet≡FreeGroup {A = A} =
  π₁Bouquet
  ≡⟨ π₁Bouquet≡∥FreeGroupoid∥₂ ⟩
  ∥ FreeGroupoid A ∥₂
  ≡⟨ sym freeGroupTruncIdempotent ⟩
  FreeGroup A ∎

-- ΩBouquet(A) ≅ FinGroup A for A = Fin k
-- Todo: generalise to other discrete sets
Iso-ΩFinBouquet-FreeGroup : {n : ℕ}
  → Iso (fst (Ω (Bouquet∙ (Fin n)))) (FreeGroup (Fin n))
Iso-ΩFinBouquet-FreeGroup {n = n} =
  compIso
    (compIso (invIso (setTruncIdempotentIso (isOfHLevelPath' 2
      (isGroupoidBouquet (DiscreteFin {n} )) _ _)))
             (equivToIso (TruncatedFamiliesEquiv base)))
    (equivToIso (invEquiv freeGroupTruncIdempotent≃))

invIso-ΩFinBouquet-FreeGroupPresStr : {n : ℕ} (x y : FreeGroup (Fin n))
  → Iso.inv (Iso-ΩFinBouquet-FreeGroup {n}) (FG._·_ x y)
   ≡ Iso.inv (Iso-ΩFinBouquet-FreeGroup {n}) x
   ∙ Iso.inv (Iso-ΩFinBouquet-FreeGroup {n}) y
invIso-ΩFinBouquet-FreeGroupPresStr {n = n} x y =
  cong (F ∘ G) (lem1 x y) ∙ lem2 (H x) (H y)
  where
  F = Iso.fun (setTruncIdempotentIso
                (isOfHLevelPath' 2 (isGroupoidBouquet DiscreteFin) _ _))
  G = invEq (TruncatedFamiliesEquiv base)
  H = fst freeGroupTruncIdempotent≃

  lem2 : (x y : _) → F (G (ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) x y))
                    ≡ F (G x) ∙ F (G y)
  lem2 =
    ST.elim2 (λ _ _ → isOfHLevelPath 2
             (isOfHLevelPath' 2 (isGroupoidBouquet (DiscreteFin {n})) _ _) _ _)
             λ _ _ → refl

  lem1 : (x t : _) → H (x FG.· t)
                  ≡ ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) (H x) (H t)
  lem1 x t =
    cong H (cong₂ FG._·_ (sym (retEq freeGroupTruncIdempotent≃ x))
                         (sym (retEq freeGroupTruncIdempotent≃ t)))
         ∙ cong H (sym (lem3 (H x) (H t)))
         ∙ secEq (freeGroupTruncIdempotent≃ {A = Fin n}) _
    where
    lem3 : (x y : _)
      → invEq freeGroupTruncIdempotent≃
                 (ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) x y)
      ≡ invEq freeGroupTruncIdempotent≃ x FG.· invEq freeGroupTruncIdempotent≃ y
    lem3 = ST.elim2 (λ _ _ → isOfHLevelPath 2 trunc _ _) λ _ _ → refl

invIso-ΩFinBouquet-FreeGroupPresInv : {n : ℕ} (x : FreeGroup (Fin n))
  → Iso.inv (Iso-ΩFinBouquet-FreeGroup {n = n}) (FG.inv x)
   ≡ sym (Iso.inv (Iso-ΩFinBouquet-FreeGroup {n = n}) x)
invIso-ΩFinBouquet-FreeGroupPresInv {n = n} =
  morphLemmas.distrMinus FG._·_ _∙_
    (Iso.inv (Iso-ΩFinBouquet-FreeGroup {n = n}))
    invIso-ΩFinBouquet-FreeGroupPresStr ε refl inv sym
    (sym ∘ lUnit) (sym ∘ rUnit) FG.invl rCancel pathAssoc refl

CharacFinBouquetFunIso : {m k : ℕ}
  → Iso (Bouquet∙ (Fin m) →∙ Bouquet∙ (Fin k))
         (Fin m → FreeGroup (Fin k))
CharacFinBouquetFunIso {m = m} {k} =
  compIso (CharacBouquet∙Iso (Bouquet∙ (Fin k)))
          (codomainIso (Iso-ΩFinBouquet-FreeGroup {n = k}))

Iso-Bouquet→∙-SphereBouquet₁→∙ : {m k : ℕ}
 → Iso (Bouquet∙ (Fin m) →∙ Bouquet∙ (Fin k))
         (SphereBouquet∙ (suc zero) (Fin m) →∙ SphereBouquet∙ (suc zero) (Fin k))
Iso-Bouquet→∙-SphereBouquet₁→∙ =
 compIso (pre∘∙equiv (invEquiv∙ Bouquet≃∙SphereBouquet))
         (post∘∙equiv (invEquiv∙ Bouquet≃∙SphereBouquet))
