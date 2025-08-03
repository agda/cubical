module Cubical.Algebra.AbGroup.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.ZAction

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Fin.Inductive

private variable
  ℓ ℓ' : Level

module AbGroupTheory (A : AbGroup ℓ) where
  open GroupTheory (AbGroup→Group A)
  open AbGroupStr (snd A)

  comm-4 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  comm-4 a b c d =
                 (a + b) + (c + d)  ≡⟨ +Assoc (a + b) c d ⟩
                 ((a + b) + c) + d  ≡⟨ cong (λ X → X + d) (sym (+Assoc a b c)) ⟩
                 (a + (b + c)) + d  ≡⟨ cong (λ X → (a + X) + d) (+Comm b c) ⟩
                 (a + (c + b)) + d  ≡⟨ cong (λ X → X + d) (+Assoc a c b) ⟩
                 ((a + c) + b) + d  ≡⟨ sym (+Assoc (a + c) b d) ⟩
                 (a + c) + (b + d)  ∎

  implicitInverse : ∀ {a b} → a + b ≡ 0g → b ≡ - a
  implicitInverse b+a≡0 = invUniqueR b+a≡0

addGroupHom : (A : AbGroup ℓ) (B : AbGroup ℓ') (ϕ ψ : AbGroupHom A B) → AbGroupHom A B
fst (addGroupHom A B ϕ ψ) x = AbGroupStr._+_ (snd B) (ϕ .fst x) (ψ .fst x)
snd (addGroupHom A B ϕ ψ) = makeIsGroupHom
  λ x y → cong₂ (AbGroupStr._+_ (snd B))
                 (IsGroupHom.pres· (snd ϕ) x y)
                 (IsGroupHom.pres· (snd ψ) x y)
        ∙ AbGroupTheory.comm-4 B (fst ϕ x) (fst ϕ y) (fst ψ x) (fst ψ y)

negGroupHom : (A : AbGroup ℓ) (B : AbGroup ℓ') (ϕ : AbGroupHom A B) → AbGroupHom A B
fst (negGroupHom A B ϕ) x = AbGroupStr.-_ (snd B) (ϕ .fst x)
snd (negGroupHom A B ϕ) =
  makeIsGroupHom λ x y
    → sym (IsGroupHom.presinv (snd ϕ) (AbGroupStr._+_ (snd A) x y))
     ∙ cong (fst ϕ) (GroupTheory.invDistr (AbGroup→Group A) x y
                  ∙ AbGroupStr.+Comm (snd A) _ _)
     ∙ IsGroupHom.pres· (snd ϕ) _ _
     ∙ cong₂ (AbGroupStr._+_ (snd B))
             (IsGroupHom.presinv (snd ϕ) x)
             (IsGroupHom.presinv (snd ϕ) y)

subtrGroupHom : (A : AbGroup ℓ) (B : AbGroup ℓ') (ϕ ψ : AbGroupHom A B) → AbGroupHom A B
subtrGroupHom A B ϕ ψ = addGroupHom A B ϕ (negGroupHom A B ψ)

-- Abelian groups quotiented by image of a map
_/Im_ : {H : Group ℓ} (G : AbGroup ℓ) (ϕ : GroupHom H (AbGroup→Group G)) → AbGroup ℓ
G /Im ϕ =
  Group→AbGroup (G /' ϕ)
    (elimProp2 (λ _ _ → squash/ _ _) λ a b → cong [_] (AbGroupStr.+Comm (snd G) _ _))
  where
  _/'_ : {H : Group ℓ} (G : AbGroup ℓ) (ϕ : GroupHom H (AbGroup→Group G)) → Group ℓ
  G /' ϕ = AbGroup→Group G
          / (imSubgroup ϕ , isNormalIm ϕ λ _ _ → AbGroupStr.+Comm (snd G) _ _)


-- ℤ-multiplication defines a homomorphism for abelian groups
private module _ (G : AbGroup ℓ) where
  ℤ·isHom-pos : (n : ℕ) (x y : fst G)
    → (pos n ℤ[ (AbGroup→Group G) ]· (AbGroupStr._+_ (snd G) x y))
     ≡ AbGroupStr._+_ (snd G) ((pos n) ℤ[ (AbGroup→Group G) ]· x)
                              ((pos n) ℤ[ (AbGroup→Group G) ]· y)
  ℤ·isHom-pos zero x y =
    sym (AbGroupStr.+IdR (snd G) (AbGroupStr.0g (snd G)))
  ℤ·isHom-pos (suc n) x y =
    cong₂ (AbGroupStr._+_ (snd G))
          refl
          (ℤ·isHom-pos n x y)
    ∙ AbGroupTheory.comm-4 G _ _ _ _

  ℤ·isHom-neg : (n : ℕ) (x y : fst G)
    → (negsuc n ℤ[ (AbGroup→Group G) ]· (AbGroupStr._+_ (snd G) x y))
     ≡ AbGroupStr._+_ (snd G) ((negsuc n) ℤ[ (AbGroup→Group G) ]· x)
                              ((negsuc n) ℤ[ (AbGroup→Group G) ]· y)
  ℤ·isHom-neg zero x y =
    GroupTheory.invDistr (AbGroup→Group G) _ _
    ∙ AbGroupStr.+Comm (snd G) _ _
  ℤ·isHom-neg (suc n) x y =
    cong₂ (AbGroupStr._+_ (snd G))
          (GroupTheory.invDistr (AbGroup→Group G) _ _
            ∙ AbGroupStr.+Comm (snd G) _ _)
          (ℤ·isHom-neg n x y)
    ∙ AbGroupTheory.comm-4 G _ _ _ _

ℤ·isHom : (n : ℤ) (G : AbGroup ℓ) (x y : fst G)
  → (n ℤ[ (AbGroup→Group G) ]· (AbGroupStr._+_ (snd G) x y))
   ≡ AbGroupStr._+_ (snd G) (n ℤ[ (AbGroup→Group G) ]· x)
                            (n ℤ[ (AbGroup→Group G) ]· y)
ℤ·isHom (pos n) G = ℤ·isHom-pos G n
ℤ·isHom (negsuc n) G = ℤ·isHom-neg G n

-- left multiplication as a group homomorphism
multₗHom : (G : AbGroup ℓ) (n : ℤ) → AbGroupHom G G
fst (multₗHom G n) g = n ℤ[ (AbGroup→Group G) ]· g
snd (multₗHom G n) = makeIsGroupHom (ℤ·isHom n G)

-- Abelian groups quotiented by a natural number
_/^_ : (G : AbGroup ℓ) (n : ℕ) → AbGroup ℓ
G /^ n = G /Im multₗHom G (pos n)

-- Torsion subgrous
_[_]ₜ : (G : AbGroup ℓ) (n : ℕ) → AbGroup ℓ
G [ n ]ₜ =
  Group→AbGroup (Subgroup→Group (AbGroup→Group G)
    (kerSubgroup (multₗHom G (pos n))))
    λ {(x , p) (y , q) → Σ≡Prop (λ _ → isPropIsInKer (multₗHom G (pos n)) _)
      (AbGroupStr.+Comm (snd G) _ _)}

-- finite sums commute with negations
sumFinG-neg : (n : ℕ) {A : AbGroup ℓ}
  → (f : Fin n → fst A)
  → sumFinGroup (AbGroup→Group A) {n} (λ x → AbGroupStr.-_ (snd A) (f x))
   ≡ AbGroupStr.-_ (snd A) (sumFinGroup (AbGroup→Group A) {n} f)
sumFinG-neg zero {A} f = sym (GroupTheory.inv1g (AbGroup→Group A))
sumFinG-neg (suc n) {A} f =
  cong₂ compA refl (sumFinG-neg n {A = A} (f ∘ injectSuc))
  ∙∙ AbGroupStr.+Comm (snd A) _ _
  ∙∙ sym (GroupTheory.invDistr (AbGroup→Group A) _ _)
  where
  -A = AbGroupStr.-_ (snd A)
  0A = AbGroupStr.0g (snd A)
  compA = AbGroupStr._+_ (snd A)
