-- The SIP applied to groups
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.GroupPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

private
  variable
    ℓ ℓ' ℓ'' : Level

open Iso
open GroupStr
open IsGroupHom

𝒮ᴰ-Group : DUARel (𝒮-Univ ℓ) GroupStr ℓ
𝒮ᴰ-Group =
  𝒮ᴰ-Record (𝒮-Univ _) IsGroupEquiv
    (fields:
      data[ _·_ ∣ autoDUARel _ _ ∣ pres· ]
      data[ 1g ∣ autoDUARel _ _ ∣ pres1 ]
      data[ inv ∣ autoDUARel _ _ ∣ presinv ]
      prop[ isGroup ∣ (λ _ _ → isPropIsGroup _ _ _) ])
  where
  open GroupStr
  open IsGroupHom

GroupPath : (M N : Group ℓ) → GroupEquiv M N ≃ (M ≡ N)
GroupPath = ∫ 𝒮ᴰ-Group .UARel.ua

-- TODO: Induced structure results are temporarily inconvenient while we transition between algebra
-- representations
module _ (G : Group ℓ) {A : Type ℓ} (m : A → A → A)
  (e : ⟨ G ⟩ ≃ A)
  (p· : ∀ x y → e .fst (G .snd ._·_ x y) ≡ m (e .fst x) (e .fst y))
  where

  private
    module G = GroupStr (G .snd)

    FamilyΣ : Σ[ B ∈ Type ℓ ] (B → B → B) → Type ℓ
    FamilyΣ (B , n) =
      Σ[ e ∈ B ]
      Σ[ i ∈ (B → B) ]
      IsGroup e n i

    inducedΣ : FamilyΣ (A , m)
    inducedΣ =
      subst FamilyΣ
        (UARel.≅→≡ (autoUARel (Σ[ B ∈ Type ℓ ] (B → B → B))) (e , p·))
        (G.1g , G.inv , G.isGroup)

  InducedGroup : Group ℓ
  InducedGroup .fst = A
  InducedGroup .snd ._·_ = m
  InducedGroup .snd .1g = inducedΣ .fst
  InducedGroup .snd .inv = inducedΣ .snd .fst
  InducedGroup .snd .isGroup = inducedΣ .snd .snd

  InducedGroupPath : G ≡ InducedGroup
  InducedGroupPath = GroupPath _ _ .fst (e , makeIsGroupHom p·)

uaGroup : {G H : Group ℓ} → GroupEquiv G H → G ≡ H
uaGroup {G = G} {H = H} = equivFun (GroupPath G H)

-- Group-ua functoriality
Group≡ : (G H : Group ℓ) → (
  Σ[ p ∈ ⟨ G ⟩ ≡ ⟨ H ⟩ ]
  Σ[ q ∈ PathP (λ i → p i) (1g (snd G)) (1g (snd H)) ]
  Σ[ r ∈ PathP (λ i → p i → p i → p i) (_·_ (snd G)) (_·_ (snd H)) ]
  Σ[ s ∈ PathP (λ i → p i → p i) (inv (snd G)) (inv (snd H)) ]
  PathP (λ i → IsGroup (q i) (r i) (s i)) (isGroup (snd G)) (isGroup (snd H)))
  ≃ (G ≡ H)
Group≡ G H = isoToEquiv theIso
  where
  theIso : Iso _ _
  fun theIso (p , q , r , s , t) i = p i , groupstr (q i) (r i) (s i) (t i)
  inv theIso x = cong ⟨_⟩ x , cong (1g ∘ snd) x , cong (_·_ ∘ snd) x , cong (inv ∘ snd) x , cong (isGroup ∘ snd) x
  rightInv theIso _ = refl
  leftInv theIso _ = refl

caracGroup≡ : {G H : Group ℓ} (p q : G ≡ H) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
caracGroup≡ {G = G} {H = H} p q P =
  sym (transportTransport⁻ (ua (Group≡ G H)) p)
                                   ∙∙ cong (transport (ua (Group≡ G H))) helper
                                   ∙∙ transportTransport⁻ (ua (Group≡ G H)) q
    where
    helper : transport (sym (ua (Group≡ G H))) p ≡ transport (sym (ua (Group≡ G H))) q
    helper = Σ≡Prop
               (λ _ → isPropΣ
                         (isOfHLevelPathP' 1 (is-set (snd H)) _ _)
                         λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd H)) _ _)
                         λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set (snd H)) _ _)
                         λ _ → isOfHLevelPathP 1 (isPropIsGroup _ _ _) _ _)
               (transportRefl (cong ⟨_⟩ p) ∙ P ∙ sym (transportRefl (cong ⟨_⟩ q)))

uaGroupId : (G : Group ℓ) → uaGroup (idGroupEquiv {G = G}) ≡ refl
uaGroupId G = caracGroup≡ _ _ uaIdEquiv

uaCompGroupEquiv : {F G H : Group ℓ} (f : GroupEquiv F G) (g : GroupEquiv G H)
                 → uaGroup (compGroupEquiv f g) ≡ uaGroup f ∙ uaGroup g
uaCompGroupEquiv f g = caracGroup≡ _ _ (
  cong ⟨_⟩ (uaGroup (compGroupEquiv f g))
    ≡⟨ uaCompEquiv _ _ ⟩
  cong ⟨_⟩ (uaGroup f) ∙ cong ⟨_⟩ (uaGroup g)
    ≡⟨ sym (cong-∙ ⟨_⟩ (uaGroup f) (uaGroup g)) ⟩
  cong ⟨_⟩ (uaGroup f ∙ uaGroup g) ∎)

open import Cubical.Algebra.Group.Instances.Int renaming (ℤ to ℤGroup)
open import Cubical.Data.Int renaming (_·_ to _*_ ; _+_ to _+ℤ_ ; _-_ to _-ℤ_)
open import Cubical.Data.Nat
open import Cubical.Data.List

_ℤ[_]·_ : ∀ {ℓ} → ℤ → (G : Group ℓ) → fst G → fst G
pos zero ℤ[ G' ]· g = GroupStr.1g (snd G')
pos (suc n) ℤ[ G' ]· g = GroupStr._·_ (snd G') g (pos n ℤ[ G' ]· g)
negsuc zero ℤ[ G' ]· g = GroupStr.inv (snd G') g
negsuc (suc n) ℤ[ G' ]· g =
  GroupStr._·_ (snd G') (GroupStr.inv (snd G') g) (negsuc n ℤ[ G' ]· g)

gen₁-by : ∀ {ℓ} (G : Group ℓ)
  → (g : fst G)
  → Type _
gen₁-by G g = (h : fst G)
          → Σ[ a ∈ ℤ ] h ≡ (a ℤ[ G ]· g)

gen₂-by : ∀ {ℓ} (G : Group ℓ)
  → (g₁ g₂ : fst G)
  → Type _
gen₂-by G g₁ g₂ =
      (h : fst G)
   → Σ[ a ∈ ℤ × ℤ ] h
    ≡ GroupStr._·_ (snd G)
                   ((fst a) ℤ[ G ]· g₁)
                   ((snd a) ℤ[ G ]· g₂)

hompres· : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'}
         → (ϕ : GroupHom G H)
         → (x : fst G) (z : ℤ)
         → fst ϕ (z ℤ[ G ]· x) ≡ (z ℤ[ H ]· fst ϕ x)
hompres· (ϕ , ϕhom) x (pos zero) = IsGroupHom.pres1 ϕhom
hompres· {H = H} (ϕ , ϕhom) x (pos (suc n)) =
    IsGroupHom.pres· ϕhom _ _
  ∙ cong (GroupStr._·_ (snd H) (ϕ x)) (hompres· (ϕ , ϕhom) x (pos n))
hompres· (ϕ , ϕhom) x (negsuc zero) = IsGroupHom.presinv ϕhom _
hompres· {H = H} (ϕ , ϕhom) x (negsuc (suc n)) =
    IsGroupHom.pres· ϕhom _ _
  ∙ cong₂ (GroupStr._·_ (snd H)) (IsGroupHom.presinv ϕhom x)
                                 ((hompres· (ϕ , ϕhom) x (negsuc n)))

Iso-pres-gen₁ : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ')
  → (g : fst G)
  → gen₁-by G g
  → (e : GroupIso G H)
  → gen₁-by H (Iso.fun (fst e) g)
Iso-pres-gen₁ G H g genG is h =
    (fst (genG (Iso.inv (fst is) h)))
  , (sym (Iso.rightInv (fst is) h)
    ∙∙ cong (Iso.fun (fst is)) (snd (genG (Iso.inv (fst is) h)))
    ∙∙ (hompres· (_ , snd is) g (fst (genG (Iso.inv (fst is) h)))))

Iso-pres-gen₂ : ∀ {ℓ ℓ'} (G : Group ℓ) (H : Group ℓ')
  → (g₁ g₂ : fst G)
  → gen₂-by G g₁ g₂
  → (e : GroupIso G H)
  → gen₂-by H (Iso.fun (fst e) g₁) (Iso.fun (fst e) g₂)
fst (Iso-pres-gen₂ G H g₁ g₂ genG is h) = genG (Iso.inv (fst is) h) .fst
snd (Iso-pres-gen₂ G H g₁ g₂ genG is h) =
     sym (Iso.rightInv (fst is) h)
  ∙∙ cong (fun (fst is)) (snd (genG (Iso.inv (fst is) h)))
  ∙∙ (IsGroupHom.pres· (snd is) _ _
  ∙ cong₂ (GroupStr._·_ (snd H))
          (hompres· (_ , snd is) g₁ (fst (fst (genG (inv (fst is) h)))))
          (hompres· (_ , snd is) g₂ (snd (fst (genG (inv (fst is) h))))))

rUnitℤ· : ∀ {ℓ} (G : Group ℓ) → (x : ℤ) → (x ℤ[ G ]· GroupStr.1g (snd G))
                                                     ≡ GroupStr.1g (snd G)
rUnitℤ· G (pos zero) = refl
rUnitℤ· G (pos (suc n)) =
    cong (GroupStr._·_ (snd G) (GroupStr.1g (snd G)))
      (rUnitℤ· G (pos n))
  ∙ GroupStr.lid (snd G) (GroupStr.1g (snd G))
rUnitℤ· G (negsuc zero) = GroupTheory.inv1g G
rUnitℤ· G (negsuc (suc n)) =
    cong₂ (GroupStr._·_ (snd G)) (GroupTheory.inv1g G) (rUnitℤ· G (negsuc n))
  ∙ GroupStr.lid (snd G) (GroupStr.1g (snd G))

rUnitℤ·ℤ : (x : ℤ) → (x ℤ[ ℤGroup ]· 1) ≡ x
rUnitℤ·ℤ (pos zero) = refl
rUnitℤ·ℤ (pos (suc n)) = cong (pos 1 +ℤ_) (rUnitℤ·ℤ (pos n)) ∙ sym (pos+ 1 n)
rUnitℤ·ℤ (negsuc zero) = refl
rUnitℤ·ℤ (negsuc (suc n)) = cong (-1 +ℤ_) (rUnitℤ·ℤ (negsuc n)) ∙ +Comm (negsuc 0) (negsuc n)

private
  precommℤ : ∀ {ℓ} (G : Group ℓ) → (g : fst G) (y : ℤ) → (snd G GroupStr.· (y ℤ[ G ]· g)) g
                                                         ≡ (sucℤ y ℤ[ G ]· g)
  precommℤ G g (pos zero) = GroupStr.lid (snd G) g
                         ∙ sym (GroupStr.rid (snd G) g)
  precommℤ G g (pos (suc n)) =
       sym (GroupStr.assoc (snd G) _ _ _)
     ∙ cong ((snd G GroupStr.· g)) (precommℤ G g (pos n))
  precommℤ G g (negsuc zero) =
    GroupStr.invl (snd G) g
  precommℤ G g (negsuc (suc n)) =
    sym (GroupStr.assoc (snd G) _ _ _)
    ∙ cong ((snd G GroupStr.· GroupStr.inv (snd G) g)) (precommℤ G g (negsuc n))
    ∙ negsucLem n
    where
    negsucLem : (n : ℕ) → (snd G GroupStr.· GroupStr.inv (snd G) g)
      (sucℤ (negsuc n) ℤ[ G ]· g)
      ≡ (sucℤ (negsuc (suc n)) ℤ[ G ]· g)
    negsucLem zero = (GroupStr.rid (snd G) _)
    negsucLem (suc n) = refl

distrℤ· : ∀ {ℓ} (G : Group ℓ) → (g : fst G) (x y : ℤ)
       → ((x +ℤ y) ℤ[ G ]· g)
         ≡ GroupStr._·_ (snd G) (x ℤ[ G ]· g) (y ℤ[ G ]· g)
distrℤ· G' g (pos zero) y = cong (_ℤ[ G' ]· g) (+Comm 0 y)
                          ∙ sym (GroupStr.lid (snd G') _)
distrℤ· G' g (pos (suc n)) (pos n₁) =
    cong (_ℤ[ G' ]· g) (sym (pos+ (suc n) n₁))
  ∙ cong (GroupStr._·_ (snd G') g) (cong (_ℤ[ G' ]· g) (pos+ n n₁) ∙ distrℤ· G' g (pos n) (pos n₁))
  ∙ GroupStr.assoc (snd G') _ _ _
distrℤ· G' g (pos (suc n)) (negsuc zero) =
    distrℤ· G' g (pos n) 0
  ∙ ((GroupStr.rid (snd G') (pos n ℤ[ G' ]· g) ∙ sym (GroupStr.lid (snd G') (pos n ℤ[ G' ]· g)))
  ∙ cong (λ x → GroupStr._·_ (snd G') x (pos n ℤ[ G' ]· g))
         (sym (GroupStr.invl (snd G') g)) ∙ sym (GroupStr.assoc (snd G') _ _ _))
  ∙ (GroupStr.assoc (snd G') _ _ _)
  ∙ cong (λ x → GroupStr._·_ (snd G')  x (pos n ℤ[ G' ]· g)) (GroupStr.invl (snd G') g)
  ∙ GroupStr.lid (snd G') _
  ∙ sym (GroupStr.rid (snd G') _)
  ∙ (cong (GroupStr._·_ (snd G') (pos n ℤ[ G' ]· g)) (sym (GroupStr.invr (snd G') g))
  ∙ GroupStr.assoc (snd G') _ _ _)
  ∙ cong (λ x → GroupStr._·_ (snd G')  x (GroupStr.inv (snd G') g))
         (precommℤ G' g (pos n))
distrℤ· G' g (pos (suc n)) (negsuc (suc n₁)) =
     cong (_ℤ[ G' ]· g) (predℤ+negsuc n₁ (pos (suc n)))
  ∙∙ distrℤ· G' g (pos n) (negsuc n₁)
  ∙∙ (cong (λ x → GroupStr._·_ (snd G') x (negsuc n₁ ℤ[ G' ]· g))
           ((sym (GroupStr.rid (snd G') (pos n ℤ[ G' ]· g))
           ∙ cong (GroupStr._·_ (snd G') (pos n ℤ[ G' ]· g)) (sym (GroupStr.invr (snd G') g)))
         ∙∙ GroupStr.assoc (snd G') _ _ _
         ∙∙ cong (λ x → GroupStr._·_ (snd G') x (GroupStr.inv (snd G') g)) (precommℤ G' g (pos n) ))
    ∙ sym (GroupStr.assoc (snd G') _ _ _))
distrℤ· G' g (negsuc zero) y =
    cong (_ℤ[ G' ]· g) (+Comm -1 y) ∙ lol1 y
  module _ where
  lol1 : (y : ℤ) → (predℤ y ℤ[ G' ]· g) ≡ (snd G' GroupStr.· GroupStr.inv (snd G') g) (y ℤ[ G' ]· g)
  lol1 (pos zero) = sym (GroupStr.rid (snd G') _)
  lol1 (pos (suc n)) =
       sym (GroupStr.lid (snd G') ((pos n ℤ[ G' ]· g)))
    ∙∙ cong (λ x → GroupStr._·_ (snd G') x (pos n ℤ[ G' ]· g)) (sym (GroupStr.invl (snd G') g))
    ∙∙ sym (GroupStr.assoc (snd G') _ _ _)
  lol1 (negsuc n) = refl
distrℤ· G' g (negsuc (suc n)) y =
     cong (_ℤ[ G' ]· g) (+Comm (negsuc (suc n)) y)
  ∙∙ lol1 G' g 0 (y +negsuc n)
  ∙∙ cong (snd G' GroupStr.· GroupStr.inv (snd G') g)
          (cong (_ℤ[ G' ]· g) (+Comm y (negsuc n)) ∙ distrℤ· G' g (negsuc n) y)
   ∙ (GroupStr.assoc (snd G') _ _ _)

minus≡0- : (x : ℤ) → - x ≡ (0 -ℤ x)
minus≡0- x = sym (GroupStr.lid (snd ℤGroup) (- x))

GroupHomℤ→ℤpres- : (e : GroupHom ℤGroup ℤGroup) → (a : ℤ) → fst e (- a) ≡ - fst e a
GroupHomℤ→ℤpres- e a = cong (fst e) (minus≡0- a) ∙∙ IsGroupHom.presinv (snd e) a ∙∙ sym (minus≡0- _)

ℤ·≡· : (a b : ℤ) → a * b ≡ (a ℤ[ ℤGroup ]· b)
ℤ·≡· (pos zero) b = refl
ℤ·≡· (pos (suc n)) b = cong (b +ℤ_) (ℤ·≡· (pos n) b)
ℤ·≡· (negsuc zero) b = minus≡0- b
ℤ·≡· (negsuc (suc n)) b = cong₂ _+ℤ_ (minus≡0- b) (ℤ·≡· (negsuc n) b)

GroupHomℤ→ℤPres· : (e : GroupHom ℤGroup ℤGroup) → (a b : ℤ) → fst e (a * b) ≡ a * fst e b
GroupHomℤ→ℤPres· e a b = cong (fst e) (ℤ·≡· a b) ∙∙ hompres· e b a ∙∙ sym (ℤ·≡· a (fst e b))
