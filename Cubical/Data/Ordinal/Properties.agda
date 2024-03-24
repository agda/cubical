{-

This file contains:

- Properties of ordinals

-}
{-# OPTIONS --safe #-}
module Cubical.Data.Ordinal.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Embedding

open import Cubical.Data.Ordinal.Base
open import Cubical.Data.Empty as ⊥ using (⊥ ; ⊥* ; isProp⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ hiding (rec ; elim ; map)
open import Cubical.Data.Unit

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Extensionality
open import Cubical.Relation.Binary.Order.Woset
open import Cubical.Relation.Binary.Order.Woset.Simulation
open import Cubical.Relation.Binary.Order

private
  variable
    ℓ : Level

propOrd : (P : Type ℓ) → isProp P → Ord {ℓ}
propOrd {ℓ} P prop = P , (wosetstr _<_ (iswoset set prp well weak trans))
  where
    open BinaryRelation
    _<_ : P → P → Type ℓ
    a < b = ⊥*{ℓ}

    set : isSet P
    set = isProp→isSet prop

    prp : isPropValued _<_
    prp _ _ = isProp⊥*

    well : WellFounded _<_
    well _ = acc (λ _ → ⊥.elim*)

    weak : isWeaklyExtensional _<_
    weak = ≺×→≡→isWeaklyExtensional _<_ set prp λ x y _ → prop x y

    trans : isTrans _<_
    trans _ _ _ = ⊥.elim*

𝟘 𝟙 : Ord {ℓ}
𝟘 {ℓ} = propOrd (⊥* {ℓ}) (isProp⊥*)
𝟙 {ℓ} = propOrd (Unit* {ℓ}) (isPropUnit*)

isLeast𝟘 : ∀{ℓ} → isLeast (isPoset→isPreorder isPoset≼) ((Ord {ℓ}) , (id↪ (Ord {ℓ}))) (𝟘 {ℓ})
isLeast𝟘 _ = ⊥.elim* , (⊥.elim* , ⊥.elim*)

-- The successor of 𝟘 is 𝟙
suc𝟘 : suc (𝟘 {ℓ}) ≡ 𝟙 {ℓ}
suc𝟘 = equivFun (WosetPath _ _) (eq , makeIsWosetEquiv eq eqsuc λ _ _ → ⊥.elim*)
  where
    eq : ⟨ 𝟘 ⟩ ⊎ Unit* ≃ ⟨ 𝟙 ⟩
    eq = ⊎-IdL-⊥*-≃

    eqsuc : _
    eqsuc (inr x) (inr y) = ⊥.elim*

+IdR : (α : Ord {ℓ}) → α + 𝟘 {ℓ} ≡ α
+IdR α = equivFun (WosetPath _ _) (eq , (makeIsWosetEquiv eq eqα λ _ _ x≺y → x≺y))
  where
    eq : ⟨ α ⟩ ⊎ ⟨ 𝟘 ⟩ ≃ ⟨ α ⟩
    eq = ⊎-IdR-⊥*-≃

    eqα : _
    eqα (inl x) (inl y) x≺y = x≺y

+IdL : (α : Ord {ℓ}) → 𝟘 {ℓ} + α ≡ α
+IdL α = equivFun (WosetPath _ _) (eq , (makeIsWosetEquiv eq eqα λ _ _ x≺y → x≺y))
  where
    eq : ⟨ 𝟘 ⟩ ⊎ ⟨ α ⟩ ≃ ⟨ α ⟩
    eq = ⊎-IdL-⊥*-≃

    eqα : (x y : ⟨ 𝟘 ⟩ ⊎ ⟨ α ⟩)
        → ((𝟘 + α) .snd WosetStr.≺ x) y
        → (α .snd WosetStr.≺ equivFun eq x) (equivFun eq y)
    eqα (inr x) (inr y) x≺y = x≺y

-- The successor is just addition by 𝟙
suc≡+𝟙 : (α : Ord {ℓ}) → suc α ≡ α + 𝟙 {ℓ}
suc≡+𝟙 α = equivFun (WosetPath _ _) (eq , (makeIsWosetEquiv eq eqsucα eqα+𝟙))
  where
    eq : ⟨ suc α ⟩ ≃ ⟨ α ⟩ ⊎ ⟨ 𝟙 ⟩
    eq = idEquiv ⟨ suc α ⟩

    eqsucα : _
    eqsucα (inl x) (inl y) x≺y = x≺y
    eqsucα (inl x) (inr y) _ = tt*
    eqsucα (inr x) (inl y) = ⊥.elim*
    eqsucα (inr x) (inr y) = ⊥.elim*

    eqα+𝟙 : _
    eqα+𝟙 (inl x) (inl y) x≺y = x≺y
    eqα+𝟙 (inl x) (inr y) _ = tt*
    eqα+𝟙 (inr x) (inl y) = ⊥.elim*
    eqα+𝟙 (inr x) (inr y) = ⊥.elim*

-- Successor is strictly increasing, though we can't prove it's the smallest ordinal greater than its predecessor
suc≺ : (α : Ord {ℓ}) → α ≺ suc α
suc≺ α = (inr tt*) , (eq , makeIsWosetEquiv eq eqsucα eqαsuc)
  where
    fun : ⟨ suc α ↓ inr tt* ⟩ → ⟨ α ⟩
    fun (inl a , _) = a

    iseq : isEquiv fun
    fst (fst (equiv-proof iseq a)) = (inl a) , tt*
    snd (fst (equiv-proof iseq a)) = refl
    snd (equiv-proof iseq a) ((inl x , _) , x≡a)
      = Σ≡Prop (λ _ → IsWoset.is-set (WosetStr.isWoset (str α)) _ _)
                (Σ≡Prop lem (cong inl (sym x≡a)))
      where lem : (y : ⟨ suc α ⟩) → isProp _
            lem (inl y) = isPropUnit*
            lem (inr _) = ⊥.elim*
    eq : ⟨ suc α ↓ inr tt* ⟩ ≃ ⟨ α ⟩
    eq = fun , iseq

    eqsucα : _
    eqsucα (inl x , _) (inl y , _) x<y = x<y

    eqαsuc : _
    eqαsuc x y x≺y = x≺y

·IdR : (α : Ord {ℓ}) → α · 𝟙 {ℓ} ≡ α
·IdR α = equivFun (WosetPath _ _) (eq , makeIsWosetEquiv eq eqα𝟙 eqα)
  where
    eq : ⟨ α ⟩ × ⟨ 𝟙 ⟩ ≃ ⟨ α ⟩
    eq = isoToEquiv rUnit*×Iso

    eqα𝟙 : _
    eqα𝟙 (x , _) (y , _) (inl tt≺tt) = ⊥.rec (IsStrictPoset.is-irrefl
                                                (isWoset→isStrictPoset
                                                   (WosetStr.isWoset (str 𝟙)))
                                               tt* tt≺tt)
    eqα𝟙 (x , _) (y , _) (inr (_ , x≺y)) = x≺y

    eqα : _
    eqα x y x≺y = inr ((isPropUnit* _ _) , x≺y)

·IdL : (α : Ord {ℓ}) → 𝟙 {ℓ} · α ≡ α
·IdL α = equivFun (WosetPath _ _) (eq , makeIsWosetEquiv eq eq𝟙α eqα)
  where
    eq : ⟨ 𝟙 ⟩ × ⟨ α ⟩ ≃ ⟨ α ⟩
    eq = isoToEquiv lUnit*×Iso

    eq𝟙α : _
    eq𝟙α (_ , x) (_ , y) (inr (_ , tt≺tt)) = ⊥.rec
                                               (IsStrictPoset.is-irrefl
                                                (isWoset→isStrictPoset
                                                  (WosetStr.isWoset (str 𝟙)))
                                                tt* tt≺tt)
    eq𝟙α (_ , x) (_ , y) (inl x≺y) = x≺y

    eqα : _
    eqα x y x≺y = inl x≺y

·AnnihilR : (α : Ord {ℓ}) → α · 𝟘 {ℓ} ≡ 𝟘 {ℓ}
·AnnihilR α = equivFun (WosetPath _ _)
                       (eq , makeIsWosetEquiv eq (λ b _ _ → ⊥.elim* (b .snd)) ⊥.elim*)
  where
    eq : ⟨ α ⟩ × ⟨ 𝟘 ⟩ ≃ ⟨ 𝟘 ⟩
    eq = (⊥.elim* ∘ snd) , (record { equiv-proof = ⊥.elim* })

·AnnihilL : (α : Ord {ℓ}) → 𝟘 {ℓ} · α ≡ 𝟘 {ℓ}
·AnnihilL α = equivFun (WosetPath _ _)
                       (eq , makeIsWosetEquiv eq (λ b _ _ → ⊥.elim* (b .fst)) ⊥.elim*)
  where
    eq : ⟨ 𝟘 ⟩ × ⟨ α ⟩ ≃ ⟨ 𝟘 ⟩
    eq = (⊥.elim* ∘ fst) , (record { equiv-proof = ⊥.elim*  })

+Assoc : (α β γ : Ord {ℓ}) → (α + β) + γ ≡ α + (β + γ)
+Assoc α β γ = equivFun (WosetPath _ _) (eq , makeIsWosetEquiv eq eq→ eq←)
  where
    eq : (⟨ α ⟩ ⊎ ⟨ β ⟩) ⊎ ⟨ γ ⟩ ≃ ⟨ α ⟩ ⊎ (⟨ β ⟩ ⊎ ⟨ γ ⟩)
    eq = ⊎-assoc-≃

    eq→ : _
    eq→ (inl (inl x)) (inl (inl y)) x≺y = x≺y
    eq→ (inl (inl x)) (inl (inr y)) x≺y = tt*
    eq→ (inl (inr x)) (inl (inl y)) = ⊥.elim*
    eq→ (inl (inr x)) (inl (inr y)) x≺y = x≺y
    eq→ (inl (inl x)) (inr y) x≺y = tt*
    eq→ (inl (inr x)) (inr y) x≺y = tt*
    eq→ (inr x) (inl (inl y)) = ⊥.elim*
    eq→ (inr x) (inl (inr y)) = ⊥.elim*
    eq→ (inr x) (inr y) x≺y = x≺y

    eq← : _
    eq← (inl x) (inl y) x≺y = x≺y
    eq← (inl x) (inr (inl y)) x≺y = tt*
    eq← (inl x) (inr (inr y)) x≺y = tt*
    eq← (inr (inl x)) (inl y) = ⊥.elim*
    eq← (inr (inr x)) (inl y) = ⊥.elim*
    eq← (inr (inl x)) (inr (inl y)) x≺y = x≺y
    eq← (inr (inl x)) (inr (inr y)) x≺y = tt*
    eq← (inr (inr x)) (inr (inl y)) = ⊥.elim*
    eq← (inr (inr x)) (inr (inr y)) x≺y = x≺y

·Assoc : (α β γ : Ord {ℓ}) → (α · β) · γ ≡ α · (β · γ)
·Assoc α β γ = equivFun (WosetPath _ _) (eq , makeIsWosetEquiv eq eq→ eq←)
  where
    eq : (⟨ α ⟩ × ⟨ β ⟩) × ⟨ γ ⟩ ≃ ⟨ α ⟩ × (⟨ β ⟩ × ⟨ γ ⟩)
    eq = Σ-assoc-≃

    eq→ : _
    eq→ ((xa , xb) , xc) ((ya , yb) , yc) (inl xc≺yc)
      = inl (inl xc≺yc)
    eq→ ((xa , xb) , xc) ((ya , yb) , yc) (inr (xc≡yc , inl xb≺yb))
      = inl (inr (xc≡yc , xb≺yb))
    eq→ ((xa , xb) , xc) ((ya , yb) , yc) (inr (xc≡yc , inr (xb≡yb , xa≺ya)))
      = inr ((≡-× xb≡yb xc≡yc) , xa≺ya)

    eq← : _
    eq← (xa , xb , xc) (ya , yb , yc) (inl (inl xc≺yc))
      = inl xc≺yc
    eq← (xa , xb , xc) (ya , yb , yc) (inl (inr (xc≡yc , xb≺yb)))
      = inr (xc≡yc , (inl xb≺yb))
    eq← (xa , xb , xc) (ya , yb , yc) (inr (xbxc≡ybyc , xa≺ya))
      = inr ((PathPΣ xbxc≡ybyc .snd) , (inr ((PathPΣ xbxc≡ybyc .fst) , xa≺ya)))

≺-o+ : {β γ : Ord {ℓ}} → (α : Ord {ℓ}) → β ≺ γ → (α + β) ≺ (α + γ)
≺-o+ {ℓ} {β} {γ} α (g , γ↓g≃β , wEq) = inr g , eq , makeIsWosetEquiv eq eq→ eq←
  where
    fun : ⟨ (α + γ) ↓ inr g ⟩ → ⟨ α + β ⟩
    fun (inl x , _) = inl x
    fun (inr x , p) = inr (equivFun γ↓g≃β (x , p))

    inv : ⟨ α + β ⟩ → ⟨ (α + γ) ↓ inr g ⟩
    inv (inl x) = inl x , tt*
    inv (inr x) = inr (invEq γ↓g≃β x .fst) , invEq γ↓g≃β x .snd

    is : Iso ⟨ (α + γ) ↓ inr g ⟩ ⟨ α + β ⟩
    Iso.fun is = fun
    Iso.inv is = inv
    Iso.rightInv is (inl x) = refl
    Iso.rightInv is (inr x) = cong inr (secEq γ↓g≃β x)
    Iso.leftInv  is (inl x , _) = ΣPathP (refl , (isPropUnit* _ _))
    Iso.leftInv  is (inr x , x≺g)
      = ΣPathP (cong inr (PathPΣ (retEq γ↓g≃β (x , x≺g)) .fst)
                        , PathPΣ (retEq γ↓g≃β (x , x≺g)) .snd)

    eq : _
    eq = isoToEquiv is

    eq→ : _
    eq→ (inl x , _) (inl y , _) x≺y = x≺y
    eq→ (inl x , _) (inr y , _) _ = tt*
    eq→ (inr x , x≺g) (inl y , y≺g) = ⊥.elim*
    eq→ (inr x , x≺g) (inr y , y≺g) x≺y
      = equivFun (IsWosetEquiv.pres≺ wEq (x , x≺g) (y , y≺g)) x≺y

    eq← : _
    eq← (inl x) (inl y) x≺y = x≺y
    eq← (inl x) (inr y) _ = tt*
    eq← (inr x) (inl y) = ⊥.elim*
    eq← (inr x) (inr y) x≺y = equivFun (IsWosetEquiv.pres≺⁻ wEq x y) x≺y

·DistR+ : (α β γ : Ord {ℓ}) → α · (β + γ) ≡ (α · β) + (α · γ)
·DistR+ α β γ = equivFun (WosetPath _ _) (eq , makeIsWosetEquiv eq eq→ eq←)
  where
    eq : ⟨ α ⟩ × (⟨ β ⟩ ⊎ ⟨ γ ⟩) ≃ (⟨ α ⟩ × ⟨ β ⟩) ⊎ (⟨ α ⟩ × ⟨ γ ⟩)
    eq = isoToEquiv ×DistR⊎Iso

    eq→ : _
    eq→ (xa , inl xb) (ya , inl yb) (inl xg≺yg) = inl xg≺yg
    eq→ (xa , inl xb) (ya , inl yb) (inr (xb≡yb , xa≺ya))
      = inr (isEmbedding→Inj isEmbedding-inl xb yb xb≡yb , xa≺ya)
    eq→ (xa , inl xb) (ya , inr yg) (inl x≺y) = x≺y
    eq→ (xa , inl xb) (ya , inr yg) (inr (xb≡yg , _)) = ⊥.rec* (⊎Path.encode _ _ xb≡yg)
    eq→ (xa , inr xg) (ya , inl yb) (inr (xg≡yb , _)) = ⊥.rec* (⊎Path.encode _ _ xg≡yb)
    eq→ (xa , inr xg) (ya , inr yg) (inl xg≺yg) = inl xg≺yg
    eq→ (xa , inr xg) (ya , inr yg) (inr (xg≡yg , xa≺ya))
      = inr (isEmbedding→Inj isEmbedding-inr xg yg xg≡yg , xa≺ya)

    eq← : _
    eq← (inl (xa , xb)) (inl (ya , yb)) (inl xb≺yb) = inl xb≺yb
    eq← (inl (xa , xb)) (inl (ya , yb)) (inr (xb≡yb , xa≺ya))
      = inr (cong inl xb≡yb , xa≺ya)
    eq← (inl (xa , xb)) (inr (ya , yg)) _ = inl tt*
    eq← (inr x) (inl (ya , yb)) = ⊥.elim*
    eq← (inr xg) (inr yg) (inl xg≺yg) = inl xg≺yg
    eq← (inr (xa , xg)) (inr (ya , yg)) (inr (xg≡yg , xa≺ya))
      = inr (cong inr xg≡yg , xa≺ya)
