{-

Shows that the universe of iterative sets is equivalent to the higher inductive-recursive cumulative
hierarchy defined in the HoTT Book.

-}
module Cubical.Data.IterativeSets.IsCumulativeHierarchy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.IterativeMultisets.Base
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration
open import Cubical.Functions.Image

open import Cubical.HITs.CumulativeHierarchy.Base as V
open import Cubical.HITs.Replacement as Rep
open import Cubical.HITs.PropositionalTruncation as Prop

private
  variable ℓ : Level

V→V⁰ : V ℓ → V⁰ {ℓ}
V→V⁰ = V.elim V→V⁰Elim
  where
  replace⊆ : {X Y : Type ℓ} (elX : X → V⁰) (elY : Y → V⁰)
    → ((x : X) → ∥ Σ[ y ∈ Y ] (elY y ≡ elX x) ∥₁)
    → (z : V⁰) → z ∈⁰ replacementV⁰ elX → z ∈⁰ replacementV⁰ elY
  replace⊆ elX elY X⊆Y z ([x] , p) =
    subst (_∈⁰ replacementV⁰ elY) p (lemma [x])
    where
    lemma : ∀ [x] → unrep V⁰UARel elX [x] ∈⁰ replacementV⁰ elY
    lemma =
      Rep.elimProp
        V⁰UARel
        elX
        (λ [x] → isProp∈⁰ {x = replacementV⁰ elY})
        (λ x →
          Prop.rec
            (isProp∈⁰ {x = replacementV⁰ elY} {z = elX x})
            (λ (y , elYy≡elXx) → (rep y) , elYy≡elXx)
            (X⊆Y x))

  V→V⁰Elim : ElimSet {ℓ} {Z = λ _ → V⁰ {ℓ}} (λ _ → isSetV⁰)
  V→V⁰Elim .ElimSet.ElimSett X _ xs = replacementV⁰ xs
  V→V⁰Elim .ElimSet.ElimEq X Y _ _ _ elX elY X⊆Y Y⊆X =
    ≃V⁰-≃-≡V⁰ .fst
      ( replace⊆ elX elY (Prop.map (λ ((y , _) , p) → (y , p)) ∘ X⊆Y)
      , replace⊆ elY elX (Prop.map (λ ((x , _) , p) → (x , p)) ∘ Y⊆X)
      )

V∞→V : V∞ {ℓ} → V ℓ
V∞→V (sup-∞ X elX) = sett X (V∞→V ∘ elX)

V⁰→V : V⁰ {ℓ} → V ℓ
V⁰→V = V∞→V ∘ fst

V⁰→V→V⁰' : (a : V∞ {ℓ}) (itsa : isIterativeSet a) → V→V⁰ (V∞→V a) ≡ (a , itsa)
V⁰→V→V⁰' (sup-∞ X elX∞) (isEmbeddingElX∞ , itselX∞) =
  Σ≡Prop isPropIsIterativeSet (cong (uncurry sup-∞) (step₁ ∙ step₂))
  where
  Rep = Replacement V⁰UARel

  elX⁰ : X → V⁰
  elX⁰ x = elX∞ x , itselX∞ x

  isEmbeddingElX⁰ : isEmbedding elX⁰
  isEmbeddingElX⁰ = lCancelEmbedding fst elX⁰ isEmbeddingElX∞ (V⁰↪V∞ .snd)

  X≃Rep : X ≃ Rep elX⁰
  X≃Rep = rep , isEquivEmbeddingOntoReplacement V⁰UARel (elX⁰ , isEmbeddingElX⁰)

  step₁ : Path (Fibration V∞ _) (_ , fst ∘ unrep _ (V→V⁰ ∘ V⁰→V ∘ elX⁰)) (_ , fst ∘ unrep _ elX⁰)
  step₁ = congS (λ f → (_ , fst ∘ unrep V⁰UARel f)) (funExt λ x → V⁰→V→V⁰' (elX∞ x) (itselX∞ x))

  step₂ : (Rep elX⁰ , (fst ∘ unrep _ _)) ≡ (X , elX∞)
  step₂ = sym (ΣPathP (ua X≃Rep , ua→ λ _ → refl))

V⁰→V→V⁰ : (a : V⁰ {ℓ}) → V→V⁰ (V⁰→V a) ≡ a
V⁰→V→V⁰ = uncurry V⁰→V→V⁰'

V→V⁰→V : (a : V ℓ) → V⁰→V (V→V⁰ a) ≡ a
V→V⁰→V = V.elimProp (λ _ → setIsSet _ _) (λ X elX rec → seteq _ _ _ _ (lem X elX rec))
  where
  lem : (X : Type ℓ) (elX : X → V ℓ) (rec : (x : X) → V⁰→V (V→V⁰ (elX x)) ≡ elX x)
    → eqImage (V⁰→V ∘ unrep V⁰UARel (V→V⁰ ∘ elX)) elX
  lem X elX rec .fst [x] =
    Prop.map
      (λ (x , p) → x , sym (rec x) ∙ cong (V⁰→V ∘ unrep _ _) p)
      (isSurjectiveRep V⁰UARel (V→V⁰ ∘ elX) [x])
  lem X elX rec .snd x =
    ∣ rep x , rec x ∣₁

VIsoV⁰ : Iso (V ℓ) (V⁰ {ℓ})
VIsoV⁰ .Iso.fun = V→V⁰
VIsoV⁰ .Iso.inv = V⁰→V
VIsoV⁰ .Iso.sec = V⁰→V→V⁰
VIsoV⁰ .Iso.ret = V→V⁰→V

V≃V⁰ : V ℓ ≃ V⁰ {ℓ}
V≃V⁰ = isoToEquiv VIsoV⁰

V≡V⁰ : V ℓ ≡ V⁰ {ℓ}
V≡V⁰ = ua V≃V⁰
