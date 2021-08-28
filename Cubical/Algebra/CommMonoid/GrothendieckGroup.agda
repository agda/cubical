{-
Module in which the Grothendieck Group ("Groupification") of a commutative monoid is defined.
-}
module Cubical.Algebra.CommMonoid.GrothendieckGroup where

open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.CommMonoid.CommMonoidProd

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties

open import Cubical.Relation.Binary.Base


private
  variable
    ℓ ℓ' : Level


module _ (M : CommMonoid ℓ) where

  open BinaryRelation
  open CommMonoidStr (snd M)

  M² : CommMonoid _
  M² = CommMonoidProd M M

  open CommMonoidStr (snd M²)
    renaming (ε to εM²; _·_ to _·²_; assoc to assoc²; rid to rid²; comm to comm²)

  R : ⟨ M² ⟩  → ⟨ M² ⟩ → Type _
  R (a₁ , b₁) (a₂ , b₂) =  Σ ⟨ M ⟩ (λ k → k · (a₁ · b₂) ≡ k · (b₁ · a₂))

  M²/R : Type _
  M²/R = ⟨ M² ⟩ / R

  0/R : M²/R
  0/R = [ εM² ]

  private
    _+/_ : M²/R → M²/R → M²/R
    x +/ y = setQuotBinOp isReflR _·²_ isCongR x y
      where
      isReflR : isRefl R
      isReflR (a , b) = ε , cong (ε ·_) (comm a b)

      isCongR : ∀ u u' v v' → R u u' → R v v' → R (u ·² v) (u' ·² v')
      isCongR (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) (a₄ , b₄) (k , p) (s , q) = k · s , proof
        where
        proof =
          (k · s) · (a₁ · a₃) · (b₂ · b₄)   ≡⟨ lemma ⟩
          (k · (a₁ · b₂)) · (s · (a₃ · b₄)) ≡⟨ cong₂ _·_ p q ⟩
          (k · (b₁ · a₂)) · (s · (b₃ · a₄)) ≡⟨ sym lemma ⟩
          (k · s) · (b₁ · b₃) · (a₂ · a₄)   ∎
            where
            ass : ∀ {x y z} → x · (y · z) ≡ (x · y) · z
            ass = assoc _ _ _

            rExp : ∀ {x y z} → x ≡ y → x · z ≡ y · z
            rExp r = cong₂ _·_ r refl

            lExp : ∀ {x y z} → x ≡ y → z · x ≡ z · y
            lExp r = cong₂ _·_ refl r

            lemma : ∀ {k s a b c d} → (k · s) · (a · b) · (c · d) ≡ (k · (a · c)) · (s · (b · d))
            lemma = sym ass ∙ lExp (
                                   ass ∙ ass ∙ rExp (
                                       comm _ _ ∙ ass ∙ ass ∙ rExp (
                                            comm _ _ ∙ ass
                                       ) ∙ sym ass
                                   ) ∙ sym ass ∙ lExp (sym ass)
                              ) ∙ ass

    -/_ : M²/R → M²/R
    -/_ = setQuotUnaryOp swap h
      where
      swap : ⟨ M² ⟩  → ⟨ M² ⟩
      swap = λ (a , b) → b , a

      h : ∀ u v → R u v → R (swap u) (swap v)
      h _ _ (k , p) = k , sym p

    assoc/R : (x y z : M²/R) → x +/ ( y +/ z) ≡ (x +/ y) +/ z
    assoc/R = elimProp3 (λ x y z → squash/ _ _) (λ u v w → cong [_] (assoc² _ _ _))

    rid/R : (x : M²/R) → x +/ 0/R ≡ x
    rid/R = elimProp (λ x → squash/ _ _) (λ u → cong [_] (rid² u))

    rinv/R : (x : M²/R) → x +/ (-/ x) ≡ 0/R
    rinv/R = elimProp (λ x → squash/ _ _)
                      (λ (a , b) →  eq/ _ _ (ε , cong (λ x → ε · x · ε) (comm _ _)))

    comm/R : (x y : M²/R) → x +/ y ≡ y +/ x
    comm/R = elimProp2 (λ x y → squash/ _ _) (λ u v → cong [_] (comm² _ _))

  asAbGroup : AbGroup ℓ
  asAbGroup = makeAbGroup 0/R _+/_ -/_ squash/ assoc/R rid/R rinv/R comm/R

Groupification : CommMonoid ℓ → AbGroup ℓ
Groupification M = asAbGroup M




-- might be a better idea to move this into AbGroup.Base, but that file doesn't import CommMonoid.Base (yet?)
AbGroup→CommMonoid : AbGroup ℓ → CommMonoid ℓ
AbGroup→CommMonoid (A , abgroupstr  _ _ _ G) =
  A , commmonoidstr _ _ (iscommmonoid (IsAbGroup.isMonoid G) (IsAbGroup.comm G))


module UniversalProperty (M : CommMonoid ℓ) where
  open CommMonoidStr ⦃...⦄
  private
    instance
      _ = M
      _ = snd M

  module _ {A : AbGroup ℓ} (φ : CommMonoidHom M (AbGroup→CommMonoid A)) where
    open IsCommMonoidHom
    open IsGroupHom

    open AbGroupStr (snd A)
      renaming (rid to ridA; invr to invrA; comm to commA; assoc to assocA)

    open GroupTheory (AbGroup→Group A)
    private
      --instance
        --_ = A
        --_ = snd A
      module φ = IsCommMonoidHom (snd φ)
      f = fst φ

    universalHom : CommMonoidHom M (AbGroup→CommMonoid (Groupification M))
    fst universalHom = λ m → [ m , ε ]
    pres· (snd universalHom) = λ _ _ → eq/ _ _ (ε , cong (ε ·_)
                                                         (comm _ _ ∙ cong₂ _·_ (rid ε) refl))
    pres-ε (snd universalHom) = refl

    private
      i = fst universalHom
    
    inducedHom : AbGroupHom (Groupification M) A
    fst inducedHom = elim (λ x → isSetAbGroup A) g proof
        where
        g = λ (a , b) → f a - f b
        proof : (u v : ⟨ M² M ⟩) (r : R M u v) → g u ≡ g v
        proof _ _ (k , p) = lemma (lemma₂ p)
            where         
            lemma₂ : ∀ {k a b c d} → k · (a · d) ≡ k · (b · c) → f a + f d ≡ f b + f c
            lemma₂ {k} {a} {b} {c} {d} p =
              f a + f d   ≡⟨ sym (φ.pres· _ _) ⟩
              f (a · d)   ≡⟨ ·CancelL _ (sym (φ.pres· _ _) ∙ (cong f p) ∙ φ.pres· _ _) ⟩
              f (b · c)   ≡⟨ φ.pres· _ _ ⟩
              f b + f c   ∎

            lemma : ∀ {a b c d} → f a + f d ≡ f b + f c → f a - f b ≡ f c - f d
            lemma {a} {b} {c} {d} p =
              f a - f b ≡⟨ {!!} ⟩
              f c - f d ∎

    pres· (snd inducedHom) = elimProp2 (λ _ _ → isSetAbGroup A _ _) proof
      where
        rExp : ∀ {x y z} → x ≡ y → x + z ≡ y + z
        rExp r = cong₂ _+_ r refl

        lExp : ∀ {x y z} → x ≡ y → z + x ≡ z + y
        lExp r = cong₂ _+_ refl r

        proof : ((a , b) (c , d) : ⟨ M² M ⟩) → (f (a · c)) - (f (b · d)) ≡ (f a - f b) + (f c - f d)
        proof (a , b) (c , d) =
          f (a · c) - f (b · d)     ≡⟨ cong₂ _-_ (φ.pres· _ _) (φ.pres· _ _) ⟩
          (f a + f c) - (f b + f d) ≡⟨ lExp (invDistr _ _ ∙ commA _ _) ∙ assocA _ _ _ ⟩
          ((f a + f c) - f b) - f d ≡⟨ rExp (sym (assocA _ _ _) ∙ lExp (commA _ _) ∙ assocA _ _ _) ∙ sym (assocA _ _ _) ⟩
          (f a - f b) + (f c - f d) ∎

    pres1 (snd inducedHom)   = invrA (f ε)
    presinv (snd inducedHom) = elimProp (λ _ → isSetAbGroup A _ _)
                                        (λ _ → sym (invDistr _ _ ∙ cong₂ _-_ (invInv _) refl))

{-
            M ------φ------> A
             \               Λ
              \             /
       universalHom    ∃! inducedHom
                \         /
                 V       /
             Groupification M
-}

    solution : (m : ⟨ M ⟩) → (fst inducedHom) (i m) ≡ f m
    solution m = cong ((f m)+_) ((cong (-_) φ.pres-ε) ∙ inv1g) ∙ ridA _ 

    private
      module G = AbGroupStr (snd (Groupification M)) using (_+_; _-_)
      
    unique : (ψ : AbGroupHom (Groupification M) A)
             → (ψIsSolution : (m : ⟨ M ⟩) → ψ .fst (i m) ≡ f m)
             → (u : ⟨ M² M ⟩) → ψ .fst [ u ] ≡ inducedHom .fst [ u ]
    unique ψ ψIsSolution (a , b) =
       ψ .fst [ a , b ]                    ≡⟨ cong (ψ .fst)
                                                   (eq/ _ _ (ε , cong (ε ·_)
                                                                      (assoc _ _ _ ∙ comm _ _))) ⟩
       ψ .fst ([ a , ε ] G.- [ b , ε ])    ≡⟨ (snd ψ).pres· _ _ ∙ cong₂ _+_ refl ((snd ψ).presinv _) ⟩
       ψ .fst [ a , ε ] - ψ .fst [ b , ε ] ≡⟨ cong₂ _-_ (ψIsSolution a) (ψIsSolution b) ⟩
       f a - f b                           ∎
