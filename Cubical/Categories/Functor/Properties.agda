{-# OPTIONS --safe #-}

module Cubical.Categories.Functor.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc; cong-∙)
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor.Base


private
  variable
    ℓ ℓ' ℓ'' : Level
    B C D E : Category ℓ ℓ'

open Category
open Functor

F-assoc : {F : Functor B C} {G : Functor C D} {H : Functor D E}
        → H ∘F (G ∘F F) ≡ (H ∘F G) ∘F F
F-assoc = Functor≡ (λ _ → refl) (λ _ → refl)


-- Results about functors

module _ {F : Functor C D} where

  -- the identity is the identity
  F-lUnit : F ∘F 𝟙⟨ C ⟩ ≡ F
  F-lUnit i .F-ob x = F ⟅ x ⟆
  F-lUnit i .F-hom f = F ⟪ f ⟫
  F-lUnit i .F-id {x} = lUnit (F .F-id) (~ i)
  F-lUnit i .F-seq f g = lUnit (F .F-seq f g) (~ i)

  F-rUnit : 𝟙⟨ D ⟩ ∘F F  ≡ F
  F-rUnit i .F-ob x = F ⟅ x ⟆
  F-rUnit i .F-hom f = F ⟪ f ⟫
  F-rUnit i .F-id {x} = rUnit (F .F-id) (~ i)
  F-rUnit i .F-seq f g = rUnit (F .F-seq f g) (~ i)

  -- functors preserve commutative diagrams (specificallysqures here)
  preserveCommF : ∀ {x y z w} {f : C [ x , y ]} {g : C [ y , w ]} {h : C [ x , z ]} {k : C [ z , w ]}
                → f ⋆⟨ C ⟩ g ≡ h ⋆⟨ C ⟩ k
                → (F ⟪ f ⟫) ⋆⟨ D ⟩ (F ⟪ g ⟫) ≡ (F ⟪ h ⟫) ⋆⟨ D ⟩ (F ⟪ k ⟫)
  preserveCommF {f = f} {g = g} {h = h} {k = k} eq
    = (F ⟪ f ⟫) ⋆⟨ D ⟩ (F ⟪ g ⟫)
    ≡⟨ sym (F .F-seq _ _) ⟩
      F ⟪ f ⋆⟨ C ⟩ g ⟫
    ≡⟨ cong (F ⟪_⟫) eq ⟩
      F ⟪ h ⋆⟨ C ⟩ k ⟫
    ≡⟨ F .F-seq _ _ ⟩
      (F ⟪ h ⟫) ⋆⟨ D ⟩ (F ⟪ k ⟫)
    ∎

  -- functors preserve isomorphisms
  preserveIsosF : ∀ {x y} → CatIso C x y → CatIso D (F ⟅ x ⟆) (F ⟅ y ⟆)
  preserveIsosF {x} {y} (f , isiso f⁻¹ sec' ret') =
    catiso
      g g⁻¹
      -- sec
      ( (g⁻¹ ⋆⟨ D ⟩ g)
      ≡⟨ sym (F .F-seq f⁻¹ f) ⟩
        F ⟪ f⁻¹ ⋆⟨ C ⟩ f ⟫
      ≡⟨ cong (F .F-hom) sec' ⟩
        F ⟪ C .id ⟫
      ≡⟨ F .F-id ⟩
        D .id
      ∎ )
      -- ret
      ( (g ⋆⟨ D ⟩ g⁻¹)
        ≡⟨ sym (F .F-seq f f⁻¹) ⟩
      F ⟪ f ⋆⟨ C ⟩ f⁻¹ ⟫
        ≡⟨ cong (F .F-hom) ret' ⟩
      F ⟪ C .id ⟫
      ≡⟨ F .F-id ⟩
        D .id
      ∎ )

      where
        x' : D .ob
        x' = F ⟅ x ⟆
        y' : D .ob
        y' = F ⟅ y ⟆

        g : D [ x' , y' ]
        g = F ⟪ f ⟫
        g⁻¹ : D [ y' , x' ]
        g⁻¹ = F ⟪ f⁻¹ ⟫

  -- hacky lemma helping with type inferences
  functorCongP : {x y v w : ob C} {p : x ≡ y} {q : v ≡ w} {f : C [ x , v ]} {g : C [ y , w ]}
               → PathP (λ i → C [ p i , q i ]) f g
               → PathP (λ i → D [ F .F-ob (p i) , F. F-ob (q i) ]) (F .F-hom f) (F .F-hom g)
  functorCongP r i = F .F-hom (r i)

isSetFunctor : isSet (D .ob) → isSet (Functor C D)
isSetFunctor {D = D} {C = C} isSet-D-ob F G p q = w
  where
    w : _
    F-ob (w i i₁) = isSetΠ (λ _ → isSet-D-ob) _ _ (cong F-ob p) (cong F-ob q) i i₁
    F-hom (w i i₁) z =
     isSet→SquareP
       (λ i i₁ → D .isSetHom {(F-ob (w i i₁) _)} {(F-ob (w i i₁) _)})
        (λ i₁ → F-hom (p i₁) z) (λ i₁ → F-hom (q i₁) z) refl refl i i₁

    F-id (w i i₁) =
       isSet→SquareP
       (λ i i₁ → isProp→isSet (D .isSetHom (F-hom (w i i₁) _) (D .id)))
       (λ i₁ → F-id (p i₁)) (λ i₁ → F-id (q i₁)) refl refl i i₁

    F-seq (w i i₁) _ _ =
     isSet→SquareP
       (λ i i₁ → isProp→isSet (D .isSetHom (F-hom (w i i₁) _) ((F-hom (w i i₁) _) ⋆⟨ D ⟩ (F-hom (w i i₁) _))))
       (λ i₁ → F-seq (p i₁) _ _) (λ i₁ → F-seq (q i₁) _ _) refl refl i i₁


-- Conservative Functor,
-- namely if a morphism f is mapped to an isomorphism,
-- the morphism f is itself isomorphism.

isConservative : (F : Functor C D) → Type _
isConservative {C = C} {D = D} F = {x y : C .ob}{f : C [ x , y ]} → isIso D (F .F-hom f) → isIso C f


-- Fully-faithfulness of functors

module _ {F : Functor C D} where

  isFullyFaithful→Full : isFullyFaithful F → isFull F
  isFullyFaithful→Full fullfaith x y = isEquiv→isSurjection (fullfaith x y)

  isFullyFaithful→Faithful : isFullyFaithful F → isFaithful F
  isFullyFaithful→Faithful fullfaith x y = isEmbedding→Inj (isEquiv→isEmbedding (fullfaith x y))

  isFull+Faithful→isFullyFaithful : isFull F → isFaithful F → isFullyFaithful F
  isFull+Faithful→isFullyFaithful full faith x y = isEmbedding×isSurjection→isEquiv
    (injEmbedding (D .isSetHom) (faith x y _ _) , full x y)


  -- Fully-faithful functor is conservative

  open isIso

  isFullyFaithful→Conservative : isFullyFaithful F → isConservative F
  isFullyFaithful→Conservative fullfaith {x = x} {y = y} {f = f} isoFf = w
    where
    w : isIso C f
    w .inv = invIsEq (fullfaith _ _) (isoFf .inv)
    w .sec = isFullyFaithful→Faithful fullfaith _ _ _ _
        (F .F-seq _ _
      ∙ (λ i → secIsEq (fullfaith _ _) (isoFf .inv) i ⋆⟨ D ⟩ F .F-hom f)
      ∙ isoFf .sec
      ∙ sym (F .F-id))
    w .ret = isFullyFaithful→Faithful fullfaith _ _ _ _
        (F .F-seq _ _
      ∙ (λ i → F .F-hom f ⋆⟨ D ⟩ secIsEq (fullfaith _ _) (isoFf .inv) i)
      ∙ isoFf .ret
      ∙ sym (F .F-id))

  -- Lifting isomorphism upwards a fully faithful functor

  module _ (fullfaith : isFullyFaithful F) where

    liftIso : {x y : C .ob} → CatIso D (F .F-ob x) (F .F-ob y) → CatIso C x y
    liftIso f .fst = invEq (_ , fullfaith _ _) (f .fst)
    liftIso f .snd = isFullyFaithful→Conservative fullfaith (subst (isIso D) (sym (secEq (_ , fullfaith _ _) (f .fst))) (f .snd))

    liftIso≡ : {x y : C .ob} → (f : CatIso D (F .F-ob x) (F .F-ob y)) → F-Iso {F = F} (liftIso f) ≡ f
    liftIso≡ f = CatIso≡ _ _ (secEq (_ , fullfaith _ _) (f .fst))


-- Functors inducing surjection on objects is essentially surjective

isSurj-ob→isSurj : {F : Functor C D} → isSurjection (F .F-ob) → isEssentiallySurj F
isSurj-ob→isSurj surj y = Prop.map (λ (x , p) → x , pathToIso p) (surj y)


-- Fully-faithful functors induce equivalence on isomorphisms

isFullyFaithful→isEquivF-Iso : {F : Functor C D}
  → isFullyFaithful F → ∀ x y → isEquiv (F-Iso {F = F} {x = x} {y = y})
isFullyFaithful→isEquivF-Iso {F = F} fullfaith x y =
  Σ-cong-equiv-prop (_ , fullfaith x y) isPropIsIso isPropIsIso _
    (λ f → isFullyFaithful→Conservative {F = F} fullfaith {f = f}) .snd


-- Functors involving univalent categories

module _
  (isUnivD : isUnivalent D)
  where

  open isUnivalent isUnivD

  -- Essentially surjective functor with univalent target induces surjection on objects

  isSurj→isSurj-ob : {F : Functor C D} → isEssentiallySurj F → isSurjection (F .F-ob)
  isSurj→isSurj-ob surj y = Prop.map (λ (x , f) → x , CatIsoToPath f) (surj y)


module _
  (isUnivC : isUnivalent C)
  (isUnivD : isUnivalent D)
  {F : Functor C D}
  where

  open isUnivalent

  -- Fully-faithful functor between univalent target induces embedding on objects

  isFullyFaithful→isEmbd-ob : isFullyFaithful F → isEmbedding (F .F-ob)
  isFullyFaithful→isEmbd-ob fullfaith x y =
    isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (_ , isUnivD .univ _ _)
      (subst isEquiv (F-pathToIso-∘ {F = F})
      (compEquiv (_ , isUnivC .univ _ _)
        (_ , isFullyFaithful→isEquivF-Iso {F = F} fullfaith x y) .snd))
