{-# OPTIONS --cubical --no-import-sorts --safe #-}
{-
Builds bismulation for the cumulative hierarchy and shows that it
is equivalent to equality though it lives in a lower universe.
-}

module Cubical.HITs.CumulativeHierarchy.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic as L hiding (_∈_; _⊆_; ⊆-refl)
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as P hiding (elim; elim2)
open import Cubical.HITs.Pushout as Pu
open import Cubical.HITs.SetQuotients as Q using (_/_; setQuotUniversal; eq/; squash/)

open import Cubical.HITs.CumulativeHierarchy.Base
import Cubical.HITs.PropositionalTruncation.Monad as PropMonad

private
  variable
    ℓ ℓ' : Level
    X Y : Type ℓ
    a b : V ℓ

infix 4 _≊_
infix 7 _∈ₛ_ _⊆_ _⊆ₛ_

------------
-- "bisimulation"
-----------

-- bisimulation is needed to define a quotient in the correct universe when
-- implementing the map : V ℓ → Σ[ X : Type ℓ ] (X → V ℓ)
-- Quotienting by Path (V ℓ) or via eqImage would lead to X : Type (ℓ-suc ℓ)

_∼_ : (s t : V ℓ) → hProp ℓ
_∼_ = elim2 eliminator where
  goalProp : (X : Type ℓ) (ix : X → V ℓ) (Y : Type ℓ) (iy : Y → V ℓ) (rec : X → Y → hProp ℓ) → hProp ℓ
  goalProp X ix Y iy rec = (∀[ a ∶ X ] ∃[ b ∶ Y ] rec a b) ⊓ (∀[ b ∶ Y ] ∃[ a ∶ X ] rec a b)

  ⇔-swap : X ⊓′ Y → Y ⊓′ X
  ⇔-swap (p , q) = (q , p)

  open PropMonad
  lemma : {X₁ X₂ Y : Type ℓ} {ix₁ : X₁ → V ℓ} {ix₂ : X₂ → V ℓ} (iy : Y → V ℓ) {rec₁ : X₁ → Y → hProp ℓ} {rec₂ : X₂ → Y → hProp ℓ}
        → (rec₁→₂ : (x₁ : X₁) → ∃[ x₂ ∈ X₂ ] Σ[ p ∈ (ix₂ x₂ ≡ ix₁ x₁) ] rec₂ x₂ ≡ rec₁ x₁)
        → (rec₂→₁ : (x₂ : X₂) → ∃[ x₁ ∈ X₁ ] Σ[ p ∈ (ix₁ x₁ ≡ ix₂ x₂) ] rec₁ x₁ ≡ rec₂ x₂)
        → [ goalProp X₁ ix₁ Y iy rec₁ ⇒ goalProp X₂ ix₂ Y iy rec₂ ]
  lemma _ rec₁→₂ rec₂→₁ (X₁→Y , Y→X₁) =
    (λ x₂ → do (x₁ , _ , xr₁) ← rec₂→₁ x₂
               (y , yr) ← X₁→Y x₁
               ∣ y , subst fst (λ i → xr₁ i y) yr ∣
    ) ,
    (λ y → do (x₁ , xr₁) ← Y→X₁ y
              (x₂ , _ , xr₂) ← rec₁→₂ x₁
              ∣ x₂ , subst fst (λ i → xr₂ (~ i) y) xr₁ ∣
    )

  open Elim2Set
  eliminator : Elim2Set (λ _ _ → isSetHProp)
  ElimSett2 eliminator = goalProp
  ElimEqSnd eliminator X ix Y₁ Y₂ iy₁ iy₂ eq rec₁ rec₂ rec₁→₂ rec₂→₁ =
    ⇔toPath (⇔-swap ∘ lemma ix rec₁→₂ rec₂→₁ ∘ ⇔-swap) (⇔-swap ∘ lemma ix rec₂→₁ rec₁→₂ ∘ ⇔-swap)
  ElimEqFst eliminator X₁ X₂ ix₁ ix₂ eq Y iy rec₁ rec₂ rec₁→₂ rec₂→₁ =
    ⇔toPath (lemma iy rec₁→₂ rec₂→₁) (lemma iy rec₂→₁ rec₁→₂)

_≊_ : (s t : V ℓ) → Type ℓ
s ≊ t = [ s ∼ t ]

∼refl : (a : V ℓ) → a ≊ a
∼refl = elimProp (λ a → isProp[] (a ∼ a)) (λ X ix rec → (λ x → ∣ x , rec x ∣) , (λ x → ∣ x , rec x ∣))

-- keep in mind that the left and right side here live in different universes
identityPrinciple : (a ≊ b) ≃ (a ≡ b)
identityPrinciple {a = a} {b = b} = isoToEquiv (iso from into (λ _ → setIsSet _ _ _ _) (λ _ → isProp[] (a ∼ b) _ _)) where
  open PropMonad

  eqImageXY : {X Y : Type ℓ} {ix : X → V ℓ} {iy : Y → V ℓ} → (∀ x y → [ ix x ∼ iy y ] → ix x ≡ iy y)
            → [ sett X ix ∼ sett Y iy ] → eqImage ix iy
  eqImageXY rec rel = (λ x → do (y , y∼x) ← fst rel x ; ∣ y , sym (rec _ _ y∼x) ∣)
                    , (λ y → do (x , x∼y) ← snd rel y ; ∣ x ,      rec _ _ x∼y  ∣)

  from : a ≊ b → a ≡ b
  from = elimProp propB (λ X ix rec → elimProp prop∼ λ Y iy _ → seteq X Y ix iy ∘ eqImageXY (λ x y → rec x (iy y))) a b where
    prop∼ : {a : V ℓ} → ∀ b → isProp (a ≊ b → a ≡ b)
    prop∼ {a = a} b = isPropΠ λ _ → setIsSet a b
    propB : (a : V ℓ) → isProp (∀ b → a ≊ b → a ≡ b)
    propB a = isPropΠ prop∼

  into : a ≡ b → a ≊ b
  into = J (λ b _ → a ≊ b) (∼refl a)

------------
-- Monic presentation of sets
-----------

-- like fiber, but in a lower universe
repFiber : (f : X → V ℓ) (b : V ℓ) → Type _
repFiber f b = Σ[ a ∈ _ ] f a ≊ b

repFiber≃fiber : (f : X → V ℓ) (b : V ℓ) → repFiber f b ≃ fiber f b
repFiber≃fiber f b = Σ-cong-equiv (idEquiv _) (λ _ → identityPrinciple)

-- projecting out a representing type together with the embedding
MonicPresentation : (a : V ℓ) → Type (ℓ-suc ℓ)
MonicPresentation {ℓ} a =  Σ[ X ∈ Type ℓ ] Σ[ ix ∈ (X → V ℓ) ] (isEmbedding ix) × (a ≡ sett X ix)

isPropMonicPresentation : (a : V ℓ) → isProp (MonicPresentation a)
isPropMonicPresentation a (X₁ , ix₁ , isEmb₁ , p) (X₂ , ix₂ , isEmb₂ , q) = λ i → (X₁≡X₂ i , ix₁≡ix₂ i , isEmbix i , a≡sett i) where
  fib1 : (x₁ : X₁) → fiber ix₂ (ix₁ x₁)
  fib1 x₁ = Σx₂ where
    x₁∈X₂ : [ ix₁ x₁ ∈ sett X₂ ix₂ ]
    x₁∈X₂ = subst (λ A → [ ix₁ x₁ ∈ A ]) (sym p ∙ q) ∣ x₁ , refl ∣
    Σx₂ : fiber ix₂ (ix₁ x₁)
    Σx₂ = P.rec (isEmbedding→hasPropFibers isEmb₂ (ix₁ x₁)) (λ (x₂ , p) → (x₂ , p)) x₁∈X₂
  hom1 : X₁ → X₂
  hom1 x₁ = fst (fib1 x₁)

  fib2 : (x₂ : X₂) → fiber ix₁ (ix₂ x₂)
  fib2 x₂ = Σx₁ where
    x₂∈X₁ : [ ix₂ x₂ ∈ sett X₁ ix₁ ]
    x₂∈X₁ = subst (λ A → [ ix₂ x₂ ∈ A ]) (sym q ∙ p) ∣ x₂ , refl ∣
    Σx₁ : fiber ix₁ (ix₂ x₂)
    Σx₁ = P.rec (isEmbedding→hasPropFibers isEmb₁ (ix₂ x₂)) (λ (x₁ , p) → (x₁ , p)) x₂∈X₁
  hom2 : X₂ → X₁
  hom2 x₂ = fst (fib2 x₂)

  X₁≃X₂ : X₁ ≃ X₂
  X₁≃X₂ = isoToEquiv (iso hom1 hom2 sec1 sec2) where
    sec1 : section hom1 hom2
    sec1 x = isEmb₂ (hom1 (hom2 x)) x .equiv-proof h2x≡x .fst .fst where
      h2x≡x : ix₂ (hom1 (hom2 x)) ≡ ix₂ x
      h2x≡x = fib1 (hom2 x) .snd ∙ fib2 x .snd
    sec2 : section hom2 hom1
    sec2 x = isEmb₁ (hom2 (hom1 x)) x .equiv-proof h1x≡x .fst .fst where
      h1x≡x : ix₁ (hom2 (hom1 x)) ≡ ix₁ x
      h1x≡x = fib2 (hom1 x) .snd ∙ fib1 x .snd

  X₁≡X₂ : X₁ ≡ X₂
  X₁≡X₂ = ua X₁≃X₂

  ix₁≡ix₂ : PathP (λ i → X₁≡X₂ i → _) ix₁ ix₂
  ix₁≡ix₂ = toPathP (
    transport refl ∘ ix₁ ∘ transport⁻ X₁≡X₂
      ≡[ i ]⟨ (λ x → transportRefl x i) ∘ ix₁ ∘ transportUaInv X₁≃X₂ (~ i) ⟩
    ix₁ ∘ transport (ua (invEquiv X₁≃X₂))
      ≡[ i ]⟨ ix₁ ∘ (λ x → uaβ (invEquiv X₁≃X₂) x i) ⟩
    ix₁ ∘ hom2
      ≡⟨ (λ i x → fib2 x .snd i) ⟩
    ix₂
      ∎ )

  isEmbix : PathP (λ i → isEmbedding (ix₁≡ix₂ i)) isEmb₁ isEmb₂
  isEmbix = isProp→PathP (λ i → isEmbeddingIsProp) isEmb₁ isEmb₂

  a≡sett : PathP (λ i → a ≡ sett (X₁≡X₂ i) (ix₁≡ix₂ i)) p q
  a≡sett = isProp→PathP (λ i → setIsSet a _) p q

sett-repr : (X : Type ℓ) (ix : X → V ℓ) → MonicPresentation (sett X ix)
sett-repr {ℓ} X ix = Rep , ixRep , isEmbIxRep , seteq X Rep ix ixRep eqImIxRep where
  Kernel : X → X → Type ℓ
  Kernel x y = ix x ≊ ix y
  Rep : Type ℓ
  Rep = X / Kernel
  ixRep : Rep → V ℓ
  ixRep = invEq (setQuotUniversal setIsSet) (ix , λ _ _ → equivFun identityPrinciple)
  isEmbIxRep : isEmbedding ixRep
  isEmbIxRep = hasPropFibers→isEmbedding propFibers where
    propFibers : ∀ y → (a b : Σ[ p ∈ Rep ] (ixRep p ≡ y)) → a ≡ b
    propFibers y (p₁ , m) (p₂ , n) = ΣPathP {B = λ _ p → ixRep p ≡ y} (base , isProp→PathP (λ _ → setIsSet _ _) _ _) where
      lemma : ∀ {p₁ p₂} → (p : ixRep Q.[ p₁ ] ≡ y) (q : ixRep Q.[ p₂ ] ≡ y) → Kernel p₁ p₂
      lemma m n = invEquiv identityPrinciple .fst (m ∙ sym n)
      propP₁ : ∀ p₁ → isProp ((ixRep p₁ ≡ y) → p₁ ≡ p₂)
      propP₁ p₁ = isPropΠ λ eq → squash/ p₁ p₂
      propP₂ : ∀ {p₁} p₂ → isProp ((ixRep p₂ ≡ y) → Q.[ p₁ ] ≡ p₂)
      propP₂ {p₁} p₂ = isPropΠ λ eq → squash/ Q.[ p₁ ] p₂
      base : p₁ ≡ p₂
      base = Q.elimProp propP₁ (λ p₁ m → Q.elimProp propP₂ (λ p₂ n → eq/ p₁ p₂ (lemma m n)) p₂ n) p₁ m

  eqImIxRep : eqImage ix ixRep
  eqImIxRep = (λ x → ∣ Q.[ x ] , refl ∣) , Q.elimProp (λ _ → P.squash) (λ b → ∣ b , refl ∣)

V-repr : (a : V ℓ) → MonicPresentation a
V-repr = elimProp isPropMonicPresentation λ X ix _ → sett-repr X ix

⟪_⟫ : (s : V ℓ) → Type ℓ
⟪ X ⟫ = V-repr X .fst

⟪_⟫↪ : (s : V ℓ) → ⟪ s ⟫ → V ℓ
⟪ X ⟫↪ = V-repr X .snd .fst

isEmb⟪_⟫↪ : (s : V ℓ) → isEmbedding ⟪ s ⟫↪
isEmb⟪ X ⟫↪ = V-repr X .snd .snd .fst

⟪_⟫-represents : (s : V ℓ) → s ≡ sett ⟪ s ⟫ ⟪ s ⟫↪
⟪ X ⟫-represents = V-repr X .snd .snd .snd

isPropRepFiber : (a b : V ℓ) → isProp (repFiber ⟪ a ⟫↪ b)
isPropRepFiber a b = embedIsProp (isEquiv→isEmbedding (repFiber≃fiber ⟪ a ⟫↪ b .snd))
                                 (isEmbedding→hasPropFibers isEmb⟪ a ⟫↪ b)

-- while ∈ is hProp (ℓ-suc ℓ), ∈ₛ is in ℓ
_∈ₛ_ : (a b : V ℓ) → hProp ℓ
a ∈ₛ b = repFiber ⟪ b ⟫↪ a , isPropRepFiber b a

∈-asFiber : {a b : V ℓ} → [ a ∈ b ] → fiber ⟪ b ⟫↪ a
∈-asFiber {a = a} {b = b} = subst (λ br → [ a ∈ br ] → fiber ⟪ b ⟫↪ a) (sym ⟪ b ⟫-represents) asRep where
  asRep : [ a ∈ sett ⟪ b ⟫ ⟪ b ⟫↪ ] → fiber ⟪ b ⟫↪ a
  asRep = P.propTruncIdempotent≃ (isEmbedding→hasPropFibers isEmb⟪ b ⟫↪ a) .fst
∈-fromFiber : {a b : V ℓ} → fiber ⟪ b ⟫↪ a → [ a ∈ b ]
∈-fromFiber {a = a} {b = b} = subst (λ br → [ a ∈ br ]) (sym ⟪ b ⟫-represents) ∘ ∣_∣

∈∈ₛ : {a b : V ℓ} → [ a ∈ b ⇔ a ∈ₛ b ]
∈∈ₛ {a = a} {b = b} = invEquiv (repFiber≃fiber ⟪ b ⟫↪ a) .fst ∘ ∈-asFiber {b = b} , ∈-fromFiber {b = b} ∘ repFiber≃fiber ⟪ b ⟫↪ a .fst

ix∈ₛ : {X : Type ℓ} {ix : X → V ℓ}
     → (x : X) → [ ix x ∈ₛ sett X ix ]
ix∈ₛ {X = X} {ix = ix} x = ∈∈ₛ {a = ix x} {b = sett X ix} .fst ∣ x , refl ∣

∈ₛ⟪_⟫↪_ : (a : V ℓ) (ix : ⟪ a ⟫) → [ ⟪ a ⟫↪ ix ∈ₛ a ]
∈ₛ⟪ a ⟫↪ ix = ix , ∼refl (⟪ a ⟫↪ ix)

-- also here, the left side is in level (ℓ-suc ℓ) while the right is in ℓ
presentation : (a : V ℓ) → (Σ[ v ∈ V ℓ ] [ v ∈ₛ a ]) ≃ ⟪ a ⟫
presentation a = isoToEquiv (iso into from (λ _ → refl) (λ s → Σ≡Prop (λ v → (v ∈ₛ a) .snd) (equivFun identityPrinciple (s .snd .snd)))) where
  into : Σ[ v ∈ V _ ] [ v ∈ₛ a ] → ⟪ a ⟫
  into = fst ∘ snd
  from : ⟪ a ⟫ → Σ[ v ∈ V _ ] [ v ∈ₛ a ]
  from ⟪a⟫ = ⟪ a ⟫↪ ⟪a⟫ , ∈ₛ⟪ a ⟫↪ ⟪a⟫

-- subset relation, once in level (ℓ-suc ℓ) and once in ℓ
_⊆_ : (a b : V ℓ) → hProp (ℓ-suc ℓ)
a ⊆ b = ∀[ x ] x ∈ₛ a ⇒ x ∈ₛ b

⊆-refl : (a : V ℓ) → [ a ⊆ a ]
⊆-refl a = λ _ xa → xa

_⊆ₛ_ : (a b : V ℓ) → hProp ℓ
a ⊆ₛ b = ∀[ x ] ⟪ a ⟫↪ x ∈ₛ b

⊆⇔⊆ₛ : (a b : V ℓ) → [ a ⊆ b ⇔ a ⊆ₛ b ]
⊆⇔⊆ₛ a b = (λ s → invEq curryEquiv s ∘ invEq (presentation a))
           , (λ s x xa → subst (λ x → [ x ∈ₛ b ]) (equivFun identityPrinciple (xa .snd)) (s (xa .fst)))

-- the homotopy definition of equality as an hProp, we know this is equivalent to bisimulation
infix 4 _≡ₕ_
_≡ₕ_ : (a b : V ℓ) → hProp (ℓ-suc ℓ)
_≡ₕ_ a b = (a ≡ b) , setIsSet a b

-- extensionality
extensionality : [ ∀[ a ∶ V ℓ ] ∀[ b ] (a ⊆ b) ⊓ (b ⊆ a) ⇒ (a ≡ₕ b) ]
extensionality {ℓ = ℓ} a b imeq = ⟪ a ⟫-represents ∙∙ settab ∙∙ sym ⟪ b ⟫-represents where
  abpth : Path (Embedding _ _) (⟪ a ⟫ , ⟪ a ⟫↪ , isEmb⟪ a ⟫↪) (⟪ b ⟫ , ⟪ b ⟫↪ , isEmb⟪ b ⟫↪)
  abpth = equivFun (EmbeddingIP _ _)
    ( (λ p → equivFun (repFiber≃fiber ⟪ b ⟫↪ p) ∘ imeq .fst p ∘ invEq (repFiber≃fiber ⟪ a ⟫↪ p))
    , (λ p → equivFun (repFiber≃fiber ⟪ a ⟫↪ p) ∘ imeq .snd p ∘ invEq (repFiber≃fiber ⟪ b ⟫↪ p))
    )
  settab : sett ⟪ a ⟫ ⟪ a ⟫↪ ≡ sett ⟪ b ⟫ ⟪ b ⟫↪
  settab i = sett (abpth i .fst) (abpth i .snd .fst)

extInverse : [ ∀[ a ∶ V ℓ ] ∀[ b ] (a ≡ₕ b) ⇒ (a ⊆ b) ⊓ (b ⊆ a) ]
extInverse a b a≡b = subst (λ b → [ (a ⊆ b) ⊓ (b ⊆ a) ]) a≡b (⊆-refl a , ⊆-refl a)

set≡-characterization : {a b : V ℓ} → (a ≡ₕ b) ≡ (a ⊆ b) ⊓ (b ⊆ a)
set≡-characterization = ⇔toPath (extInverse _ _) (extensionality _ _)
