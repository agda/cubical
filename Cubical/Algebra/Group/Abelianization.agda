{-

This file contains:
    - the abelianization of groups

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Abelianization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.AbGroup.Base

private
  variable
    ℓ : Level

module _ (G : Group ℓ) where
  open GroupStr (snd G)
  open GroupTheory G

  data Abelianization : Type ℓ where
    η : (g : fst G) → Abelianization
    comm : (a b c : fst G) → η (a · (b · c)) ≡ η (a · (c · b))
    isset : (x y : Abelianization) → (p q : x ≡ y) → p ≡ q

  -- proofabelian : (a b : fst G) → η (a · b) ≡ η (b · a)
  -- proofabelian a b = {! comm .1g a b  !} -- Diese Codezeilen haben einen Bug erzeugt, wenn man das Loch refinen möchte

  {-
  Abelianization2 : Type ℓ
  Abelianization2 = (fst G) / λ g h → Σ[ a ∈ (fst G) ] 
                                      Σ[ b ∈ (fst G) ] 
                                      Σ[ c ∈ (fst G) ] (g ≡ (a · (b · c))) × (h ≡ (a · (c · b)))
  -}

  elimProp : {B : Abelianization → Type ℓ}
        → (Bprop : (x : Abelianization) → isProp (B x))
        → (f : (g : fst G) → B (η g))
        → (x : Abelianization)
        → B x
  elimProp Bprop f (η g) = f g
  elimProp {B = B} Bprop f (comm a b c i) = isProp→PathP (λ i → Bprop (comm a b c i)) (f (a · (b · c))) (f (a · (c · b))) i
  elimProp Bprop f (isset x y p q i j) = isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (Bprop x)) (g x) (g y) (cong g p) (cong g q) (isset x y p q) i j 
                                        where
                                        g = elimProp Bprop f

  elimProp2 : {C : Abelianization → Abelianization → Type ℓ}
        → (Cprop : (x y : Abelianization) → isProp (C x y))
        → (f : (a b : fst G) → C (η a) (η b))
        → (x y : Abelianization)
        → C x y
  elimProp2 Cprop f = elimProp (λ x → isPropΠ (λ y → Cprop x y))
                                       (λ x → elimProp (λ y → Cprop (η x) y) (f x))

  elimProp3 : {D : Abelianization → Abelianization → Abelianization → Type ℓ}
        → (Dprop : (x y z : Abelianization) → isProp (D x y z))
        → ((a b c : fst G) → D (η a) (η b) (η c))
        → (x y z : Abelianization)
        → D x y z
  elimProp3 Dprop f = elimProp (λ x → isPropΠ2 (λ y z → Dprop x y z))
                               (λ x → elimProp2 (λ y z → Dprop (η x) y z) (f x))

  elimContr : {B : Abelianization → Type ℓ}
        → (Bcontr : ∀ (a : fst G) → isContr (B (η a)))
        → (x : Abelianization)
        → B x
  elimContr Bcontr = elimProp (elimProp (λ _ → isPropIsProp) λ _ → isContr→isProp (Bcontr _))
                              λ _ → Bcontr _ .fst

  elimContr2 : {C : Abelianization → Abelianization → Type ℓ}
        → (Ccontr : ∀ (a b : fst G) → isContr (C (η a) (η b)))
        → (x y : Abelianization)
        → C x y
  elimContr2 Ccontr = elimContr λ _ → isOfHLevelΠ 0
                     (elimContr λ _ → inhProp→isContr (Ccontr _ _) isPropIsContr)

  rec : {M : Type ℓ}
        (Mset : isSet M)
        (f : fst G → M)
        (fcomm : (a b c : fst G) → f (a · (b · c)) ≡ f (a · (c · b)))
      → Abelianization → M
  rec Mset f fcomm (η g) = f g
  rec Mset f fcomm (comm a b c i) = fcomm a b c i
  rec Mset f fcomm (isset a b p q i j) = Mset (g a) (g b) (cong g p) (cong g q) i j
    where
    g = rec Mset f fcomm

  rec2 : {M : Type ℓ}
        (Mset : isSet M)
        (f : fst G → fst G → M)
        (fcomml : (a b c d : fst G) → f (a · (b · c)) d ≡ f (a · (c · b)) d)
        (fcommr : (a b c d : fst G) → f a (b · (c · d)) ≡ f a (b · (d · c)))
      → Abelianization → Abelianization → M
  rec2 Mset f fcomml fcommr = rec (isSetΠ (λ _ → Mset)) (λ g → rec Mset (λ h → f g h) (fcommr g)) λ a b c → funExt (elimProp (λ _ → Mset _ _) (λ d → fcomml a b c d))


-- Definition der Gruppenstruktur auf der Abelisierung
  _·Ab_ : Abelianization → Abelianization → Abelianization
  _·Ab_ = rec2 isset (λ x y → η (x · y))
                      ((λ a b c d → η ((a · (b · c)) · d) ≡⟨ cong (λ x → (η (x · d))) (assoc _ _ _) ⟩
                                    η (((a · b) · c) · d) ≡⟨ cong η (sym (assoc (a · b) c d)) ⟩
                                    η ((a · b) · (c · d)) ≡⟨ comm (a · b) c d ⟩
                                    η ((a · b) · (d · c)) ≡⟨ cong η (sym (assoc _ _ _)) ⟩
                                    η (a · (b · (d · c))) ≡⟨ cong (λ x → (η (a · x))) (assoc _ _ _) ⟩
                                    η (a · ((b · d) · c)) ≡⟨ comm a (b · d) c ⟩
                                    η (a · (c · (b · d))) ≡⟨ cong (λ x → (η (a · x))) (assoc _ _ _) ⟩
                                    η (a · ((c · b) · d)) ≡⟨ cong η (assoc a (c · b) d) ⟩
                                    η ((a · (c · b)) · d) ∎))
                      (λ a b c d → (η (a · (b · (c · d))) ≡⟨ cong η (assoc _ _ _) ⟩ 
                                    η ((a · b) · (c · d)) ≡⟨ comm (a · b) c d ⟩ 
                                    η ((a · b) · (d · c)) ≡⟨ cong η (sym (assoc _ _ _)) ⟩ 
                                    η (a · (b · (d · c))) ∎))

  1Ab : Abelianization
  1Ab = η 1g

  invAb : Abelianization → Abelianization
  invAb = rec isset ((λ x → η (inv x))) (λ a b c → η (inv (a · (b · c)))                    ≡⟨ cong η (invDistr a (b · c)) ⟩
                                                   η ((inv (b · c)) · (inv a))              ≡⟨ cong (λ x → η (x · (inv a))) (invDistr b c) ⟩
                                                   η (((inv c) · (inv b)) · (inv a))        ≡⟨ cong η ((sym (lid (((inv c) · (inv b)) · (inv a))))) ⟩
                                                   η (1g · (((inv c) · (inv b)) · (inv a))) ≡⟨ comm 1g ((inv c) · (inv b)) (inv a) ⟩
                                                   η (1g · ((inv a) · ((inv c) · (inv b)))) ≡⟨ cong η (lid ((inv a) · ((inv c) · (inv b)))) ⟩
                                                   η ((inv a) · ((inv c) · (inv b)))        ≡⟨ comm (inv a) (inv c) (inv b) ⟩
                                                   η ((inv a) · ((inv b) · (inv c)))        ≡⟨ cong η ((sym (lid ((inv a) · ((inv b) · (inv c)))))) ⟩
                                                   η (1g · ((inv a) · ((inv b) · (inv c)))) ≡⟨ comm 1g (inv a) ((inv b) · (inv c)) ⟩
                                                   η (1g · (((inv b) · (inv c)) · (inv a))) ≡⟨ cong η (lid (((inv b) · (inv c)) · (inv a))) ⟩
                                                   η (((inv b) · (inv c)) · (inv a))        ≡⟨ cong (λ x → η (x · (inv a))) (sym (invDistr c b)) ⟩
                                                   η ((inv (c · b)) · (inv a))              ≡⟨ cong η (sym (invDistr a (c · b))) ⟩
                                                   η (inv (a · (c · b))) ∎)

  assocAb : (x y z : Abelianization) → x ·Ab (y ·Ab z) ≡ (x ·Ab y) ·Ab z
  assocAb = elimProp3 (λ x y z → isset (x ·Ab (y ·Ab z)) ((x ·Ab y) ·Ab z)) (λ x y z → cong η (assoc x y z))

  ridAb : (x : Abelianization) → x ·Ab 1Ab ≡ x
  ridAb = elimProp (λ x → isset (x ·Ab 1Ab) x) (λ x → cong η (rid x))

  rinvAb : (x : Abelianization) → x ·Ab (invAb x) ≡ 1Ab
  rinvAb = elimProp (λ x → isset (x ·Ab (invAb x)) 1Ab) (λ x → (η x) ·Ab (invAb (η x)) ≡⟨ refl ⟩
                                                               (η x) ·Ab (η (inv x))   ≡⟨ refl ⟩
                                                               η (x · (inv x))         ≡⟨ cong η (fst (inverse x)) ⟩
                                                               η 1g                    ≡⟨ refl ⟩
                                                               1Ab ∎)

  commAb : (x y : Abelianization) → x ·Ab y ≡ y ·Ab x
  commAb = elimProp2 (λ x y → isset (x ·Ab y) (y ·Ab x)) (λ x y → (η x) ·Ab (η y)  ≡⟨ refl ⟩
                                                                  η (x · y)        ≡⟨ cong η (sym (lid (x · y))) ⟩
                                                                  η (1g · (x · y)) ≡⟨ comm 1g x y ⟩
                                                                  η (1g · (y · x)) ≡⟨ cong η (lid (y · x)) ⟩
                                                                  η (y · x)        ≡⟨ refl ⟩
                                                                  (η y) ·Ab (η x) ∎)

  proofAbelianGroup : AbGroup ℓ
  proofAbelianGroup = makeAbGroup 1Ab _·Ab_ invAb isset assocAb ridAb rinvAb commAb

  {-
  universalPropertyAb : (H : AbGroup ℓ)
                      → (f : fst G → fst H)
                      → Abelianization → fst H
  universalPropertyAb H f = elimProp (λ x → {!   !}) (λ x → f x)
 
  universalProperty2Ab : (H : AbGroup ℓ)
                       → (f : fst G → fst H)
                       → (pseudoUniversalPropertyAb : Abelianization → fst H)
                       → pseudoUniversalPropertyAb ≡ (universalPropertyAb H f)
  universalProperty2Ab H f pseudoUniversalPropertyAb = {!   !}
  -}