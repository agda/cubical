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

-- module _ {ℓ : Level} {G' : Group ℓ} where
--   private
--     G = fst G'

--     _+G_ = GroupStr._·_ (snd G')
--     -G = GroupStr.inv (snd G')
--     1G = GroupStr.1g (snd G')

--   _ℤ·_ : ℤ → G → G
--   pos zero ℤ· g = 1G
--   pos (suc n) ℤ· g = g +G (pos n ℤ· g)
--   negsuc zero ℤ· g = -G g
--   negsuc (suc n) ℤ· g = -G g +G (negsuc n ℤ· g)

--   rUnitℤ : (g : G) → 1 ℤ· g ≡ g
--   rUnitℤ = {!!}

-- copyList : {!length!}
-- copyList = {!!}
-- open import Cubical.Data.Empty renaming (rec to ⊥-rec)
-- module _ {ℓ : Level} (G' : Group ℓ) where
--   private
--     G = fst G'

--     _+G_ = GroupStr._·_ (snd G')
--     -G = GroupStr.inv (snd G')
--     1G = GroupStr.1g (snd G')
--   sum : List (ℤ × G) → G
--   sum [] = 1G
--   sum (x ∷ x₁) = (_ℤ·_ {G' = G'} (fst x) (snd x)) +G sum x₁

--   sum'help : (l1 : List ℤ) (l2 : List G) (n m : ℕ)
--           → (n ≡ m)
--           → length l1 ≡ n
--           → length l2 ≡ m
--           → G
--   sum'help [] [] n m p q r = 1G
--   sum'help [] (x ∷ l2) n m p q r =
--     ⊥-rec (snotz (r ∙∙ sym p ∙∙ sym q))
--   sum'help (x ∷ l1) [] n m p q r =
--     ⊥-rec (snotz (q ∙∙ p ∙∙ sym r))
--   sum'help (x ∷ l1) (x₁ ∷ l2) n m p q r =
--     _ℤ·_ {G' = G'} x x₁ +G sum'help l1 l2 _ _ (cong predℕ p) (cong predℕ q) (cong predℕ r)

--   sum' : (l1 : List ℤ) (l2 : List G) → length l1 ≡ length l2
--       → G
--   sum' l1 l2 p = sum'help l1 l2 _ _ p refl refl

--   isFinGen : Type _
--   isFinGen =
--     Σ[ l ∈ List G ]
--      ((g : G) → Σ[ l2 ∈ List ℤ ]
--                   Σ[ p ∈ (length l2 ≡ length l) ]
--                     sum' l2 l p ≡ g)

-- isFinGenℤ : isFinGen ℤGroup
-- isFinGenℤ = (1 ∷ [])
--           , λ g → (g ∷ []) , refl , help g
--   where
--   help : (g : ℤ) → sum' ℤGroup (g ∷ []) (pos 1 ∷ []) (λ _ → 1) ≡ g
--   help (pos zero) = refl
--   help (pos (suc n)) = cong (pos 1 +ℤ_) (help (pos n)) ∙ +Comm (pos 1) (pos n)
--   help (negsuc zero) = refl
--   help (negsuc (suc n)) = cong (negsuc 0 +ℤ_) (help (negsuc n)) ∙ +Comm (negsuc 0) (negsuc n)

-- open import Cubical.Algebra.Group.DirProd
-- isFinGenℤ×ℤ : isFinGen (DirProd ℤGroup ℤGroup)
-- fst isFinGenℤ×ℤ = (1 , 0) ∷ (0 , 1) ∷ []
-- fst (snd isFinGenℤ×ℤ (x , y)) = x ∷ y ∷ []
-- fst (snd (snd isFinGenℤ×ℤ (x , y))) = refl
-- snd (snd (snd isFinGenℤ×ℤ (x , y))) =
--   ΣPathP ((λ i → fst ((distrLem 1 0 x) i) +ℤ fst (distrLem 0 1 y i))
--        ∙ (λ i → (·Comm x 1 i) +ℤ (·Comm y 0 i))
--        , (λ i → snd ((distrLem 1 0 x) i) +ℤ snd (distrLem 0 1 y i))
--        ∙ (λ i → (·Comm x 0 i) +ℤ (·Comm y 1 i))
--        ∙ sym (+Comm y 0))
--   where
--   ll : (x : ℤ) → - x ≡ 0 -ℤ x
--   ll (pos zero) = refl
--   ll (pos (suc zero)) = refl
--   ll (pos (suc (suc n))) =
--     cong predℤ (ll (pos (suc n)))
--   ll (negsuc zero) = refl
--   ll (negsuc (suc n)) = cong sucℤ (ll (negsuc n))

--   ℤ×ℤ = DirProd ℤGroup ℤGroup
--   _+''_ = GroupStr._·_ (snd ℤ×ℤ)
--   distrLem : (x y : ℤ) (z : ℤ)
--            → Path (ℤ × ℤ) (_ℤ·_ {G' = DirProd ℤGroup ℤGroup} z (x , y)) (z * x , z * y)
--   distrLem x y (pos zero) = refl
--   distrLem x y (pos (suc n)) = cong ((x , y) +''_) (distrLem x y (pos n))
--   distrLem x y (negsuc zero) = ΣPathP (sym (ll x) , sym (ll y)) 
--   distrLem x y (negsuc (suc n)) =
--       cong₂ _+''_ (ΣPathP (sym (ll x) , sym (ll y))) (distrLem x y (negsuc n))

-- maini : ∀ {ℓ} {G : Type ℓ}
--      → {!GroupIso!}
-- maini = {!!}
