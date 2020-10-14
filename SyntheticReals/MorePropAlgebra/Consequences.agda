{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.MorePropAlgebra.Consequences where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Function.Base using (_∋_; _$_)
open import Cubical.Foundations.Logic renaming
  ( inl to inlᵖ
  ; inr to inrᵖ
  ; _⇒_ to infixr 0 _⇒_                  -- shifting by -6
  ; _⇔_ to infixr -2 _⇔_                 --
  ; ∃[]-syntax to infix  -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix  -4 ∃[∶]-syntax --
  ; ∀[∶]-syntax to infix  -4 ∀[∶]-syntax --
  ; ∀[]-syntax to infix  -4 ∀[]-syntax   --
  )
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣
open import Cubical.HITs.PropositionalTruncation.Properties using (propTruncIsProp) renaming (elim to ∣∣-elim)

open import SyntheticReals.Utils
open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Definitions renaming
  ( _ᵗ⇒_ to infixr 0 _ᵗ⇒_
  ; ∀ᵖ[∶]-syntax to infix -4 ∀ᵖ[∶]-syntax
  ; ∀ᵖ〚∶〛-syntax to infix -4 ∀ᵖ〚∶〛-syntax
  ; ∀ᵖ!〚∶〛-syntax to infix -4 ∀ᵖ!〚∶〛-syntax
  ; ∀〚∶〛-syntax to infix -4 ∀〚∶〛-syntax
  )
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions

-- NOTE: hProps need to be explicit arguments (that is not a necessity, but we need to give them completely and not just their witnesses)
-- NOTE: I think one can make all `isProp` implementations `abstract` to save some compilation time
--         because we have `isPropIsProp` anyways
--       but for the logic part, it depends on how coslty
--         ⊔-elim, ⊥-elim, ⇒∶_⇐∶_, isoToPath, hProp≡, etc.
--       are and whether they could actually reduce some terms

module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ')
  (let _<_ = R)
  (let _≤_ = R)
  (let _#_ = R)
  where
  -- abstract
  irrefl+trans⇒asym    : [ isIrrefl  R ] → [ isTrans  R ] → [ isAsym  R ]
  irrefl+trans⇒asym'   : [ isIrrefl  R ] → [ isTrans  R ] → [ isAsym' R ]

  <-cotrans⇒≤-trans    : [ isCotrans _<_ ] → [ isTrans (λ x y → ¬(y < x)) ]
  connex⇒refl          : [ isConnex  _≤_ ] → [ isRefl _≤_ ]

  isIrrefl⇔isIrrefl'   :                              [ isIrrefl  _<_ ⇔ isIrrefl'  _<_ ]
  isIrrefl'⇔isIrrefl'' : (<-asym : [ isAsym  _<_ ]) → [ isIrrefl' _<_ ⇔ isIrrefl'' _<_ ]

  isAsym⇔isAsym'       :                              [ isAsym     R  ⇔ isAsym'                                    R           ]
  isTight⇔isTight'     :                              [ isTight    R  ⇔ isTight'                                   R           ]
  isTight'⇔isTight''   :                              [ isTight'   R  ⇔ isTight''                                  R           ]
  isTight'⇔isTight'''  :                              [ isTight'  _<_ ⇔ isTight''' (λ x y →                (x < y) ⊔  (y < x)) ]
  isTight''⇔isTight''' : (<-asym : [ isAsym  _<_ ]) → [ isTight'' _<_ ⇔ isTight''' (λ x y → [ <-asym x y ] (x < y) ⊎ᵖ (y < x)) ]
  isTight⇔isAntisym    :                              [ isTight   _<_ ⇔ isAntisym  (λ x y →                   ¬ (y < x))       ]

  strictlinearorder⇒strictpartialorder : [ isStrictLinearOrder _<_                   ⇒ isStrictPartialOrder _<_ ]
  linearorder⇒partialorder             : [ isLinearOrder       _≤_                   ⇒ isPartialOrder       _≤_ ]

  irrefl+trans⇒asym isIrrefl isTrans a b a<b b<a = isIrrefl _ (isTrans _ _ _ a<b b<a)

  irrefl+trans⇒asym' isIrrefl isTrans a b (a<b , b<a) = isIrrefl _ (isTrans _ _ _ a<b b<a)

  <-cotrans⇒≤-trans <-cotrans a b c ¬b<a ¬c<b c<a = ⊔-elim (c < b) (b < a) (λ _ → ⊥)
                                                     (λ c<b → ¬c<b c<b)
                                                     (λ b<a → ¬b<a b<a)
                                                     (<-cotrans _ _ c<a b)

  connex⇒refl is-connex a = case is-connex a a as a ≤ a ⊔ a ≤ a ⇒ a ≤ a of λ{ (inl p) → p ; (inr p) → p }

  isIrrefl⇔isIrrefl' .fst <-irrefl  a b a<b⊔b<a a≡b =
    substₚ (λ b → a < b ⊔ b < a ⇒ ⊥) a≡b
    (λ p → case p as R a a ⊔ R a a ⇒ ⊥ of λ{ (inl p) → <-irrefl _ p ; (inr p) → <-irrefl _ p })
    a<b⊔b<a
  isIrrefl⇔isIrrefl' .snd <-irrefl' x x<x = <-irrefl' x x (inlᵖ x<x) ∣ refl ∣

  isIrrefl'⇔isIrrefl'' <-asym .fst <-irrefl' a b (inl a<b) = <-irrefl'  a b (inlᵖ a<b)
  isIrrefl'⇔isIrrefl'' <-asym .fst <-irrefl' a b (inr b<a) = <-irrefl'  a b (inrᵖ b<a)
  isIrrefl'⇔isIrrefl'' <-asym .snd <-irrefl'' a b a<b⊎b<a = case a<b⊎b<a as a < b ⊔ b < a ⇒ ¬ a ≡ₚ b of λ
                                               { (inl a<b) → <-irrefl'' a b (inl a<b)
                                               ; (inr b<a) → <-irrefl'' a b (inr b<a) }

  isAsym⇔isAsym' .fst <-asym a b (a<b , b<a) = <-asym a b a<b b<a
  isAsym⇔isAsym' .snd <-asym a b = fst (¬-⊓-distrib (a < b) (b < a) (<-asym a b))

  isTight⇔isTight' .fst <-tightᵖ  a b ¬ᵗ[a<b⊔b<a]     = let (¬ᵗ[a<b] , ¬ᵗ[b<a]) = deMorgan₂ (a < b) (b < a) ¬ᵗ[a<b⊔b<a] in <-tightᵖ a b ¬ᵗ[a<b] ¬ᵗ[b<a]
  isTight⇔isTight' .snd <-tightᵖ' a b ¬ᵗ[a<b] ¬ᵗ[b<a] = <-tightᵖ' a b (deMorgan₂-back (a < b) (b < a) (¬ᵗ[a<b] , ¬ᵗ[b<a]))

  isTight'⇔isTight'' .fst <-tightᵖ'  a b ¬ᵗ[a<b⊎b<a] = <-tightᵖ'  a b (pathTo⇒ (∥¬A∥≡¬∥A∥ _) ∣ ¬ᵗ[a<b⊎b<a] ∣)
  isTight'⇔isTight'' .snd <-tightᵖ'' a b ¬ᵗ[a<b⊔b<a] = <-tightᵖ'' a b (λ [a<b⊎b<a] → ¬ᵗ[a<b⊔b<a] (⊎⇒⊔ (a < b) (b < a) [a<b⊎b<a]))

  isTight'⇔isTight''' .fst x = x
  isTight'⇔isTight''' .snd x = x

  isTight''⇔isTight''' <-asym .fst x = x
  isTight''⇔isTight''' <-asym .snd x = x

  isTight⇔isAntisym .fst <-tight   a b a≤b b≤a = <-tight   a b b≤a a≤b
  isTight⇔isAntisym .snd ≤-antisym a b b≤a a≤b = ≤-antisym a b a≤b b≤a

  strictlinearorder⇒strictpartialorder is-StrictLinearOrder = isstrictpartialorder is-irrefl is-trans is-cotrans where
    is-irrefl = IsStrictLinearOrder.is-irrefl is-StrictLinearOrder
    is-trans  = IsStrictLinearOrder.is-trans  is-StrictLinearOrder
    is-tricho = IsStrictLinearOrder.is-tricho is-StrictLinearOrder
    is-asym   = irrefl+trans⇒asym is-irrefl is-trans
    is-cotrans : [ isCotrans _<_ ]
    is-cotrans a b a<b x with is-tricho a x | is-tricho x b
    ... | inl (inl a<x) | q = inlᵖ a<x
    ... | inl (inr x<a) | inl (inl x<b) = inrᵖ x<b
    ... | inl (inr x<a) | inl (inr b<x) = ⊥-elim $ is-irrefl x (is-trans x b x (is-trans x a b x<a a<b) b<x)
    ... | inl (inr x<a) | inr      x≡b  = ⊥-elim $ is-asym a b a<b (substₚ (λ p → p < a) x≡b x<a)
    ... | inr      a≡x  | inl (inl x<b) = inrᵖ x<b
    ... | inr      a≡x  | inl (inr b<x) = ⊥-elim $ is-asym b x b<x (substₚ (λ p → p < b) a≡x a<b)
    ... | inr      a≡x  | inr      x≡b  = ⊥-elim $ is-irrefl b (substₚ (λ p → p < b) x≡b $ substₚ (λ p → p < b) a≡x a<b)

  linearorder⇒partialorder is-LinearOrder =
    let (islinearorder is-connex is-antisym is-trans) = is-LinearOrder
    in ispartialorder (connex⇒refl is-connex) is-antisym is-trans

  -- consequences on sets
  module _ (is-set : isSet A) where
    -- abstract
    isIrreflˢ''⇔isIrrefl''  : (is-asym : [ isAsym R ])    → [ isIrreflˢ'' R is-set ⇔ isIrrefl'' R ]
    isAntisymˢ⇔isAntisym    :                               [ isAntisymˢ  R is-set ⇔ isAntisym  R ]
    isAntisymˢ'⇔isAntisym'  :                               [ isAntisymˢ' R is-set ⇔ isAntisym' R ]
    isTightˢ⇔isTight        :                               [ isTightˢ    R is-set ⇔ isTight    R ]
    isTightˢ'⇔isTight'      :                               [ isTightˢ'   R is-set ⇔ isTight'   R ]
    isTightˢ''⇔isTight''    :                               [ isTightˢ''  R is-set ⇔ isTight''  R ]
    isTightˢ'''⇔isTight'''  :                               [ isTightˢ''' R is-set ⇔ isTight''' R ]
    isTightˢ'''⇔isAntisymˢ  : (is-asym : [ isAsym R ])    → [ isTightˢ''' (λ x y → [ is-asym x y ] (x < y) ⊎ᵖ (y < x)) is-set
                                                            ⇔ isAntisymˢ  (λ x y →                    ¬ (y < x)      ) is-set ]

    isTrichotomousˢ⇔isTrichotomous : (is-irrefl : [ isIrrefl'' R ]) → (is-irreflˢ : [ isIrreflˢ'' R is-set ]) → (is-asym : [ isAsym R ]) → [ isTrichotomousˢ R is-set is-irreflˢ is-asym ⇔ isTrichotomous R is-irrefl is-asym ]

    -- tricho⇒cotrans                       : (is-irrefl : [ isIrrefl'' R ]) → (is-asym : [ isAsym R ])
    --                                      → [ isTrichotomous      _<_ is-irrefl is-asym ⇒ isCotrans            _<_ ]

    isIrreflˢ''⇔isIrrefl'' <-asym .fst <-irreflˢ'' a b a<b a≡b = <-irreflˢ'' a b a<b (∣∣-elim (λ c → is-set a b) (λ x → x) a≡b)
    isIrreflˢ''⇔isIrrefl'' <-asym .snd <-irrefl''  a b a<b a≡b = <-irrefl''  a b a<b ∣ a≡b ∣

    isAntisymˢ⇔isAntisym .fst ≤-antisymˢ a b a≤b b≤a = ∣ ≤-antisymˢ a b a≤b b≤a ∣
    isAntisymˢ⇔isAntisym .snd ≤-antisym  a b a≤b b≤a = ∣∣-elim (λ c → is-set a b) (λ x → x) (≤-antisym  a b a≤b b≤a)

    isAntisymˢ'⇔isAntisym' .fst ≤-antisymˢ' a b a≤b ¬ᵗa≡b = ≤-antisymˢ' a b a≤b (λ  z  → ¬ᵗa≡b ∣ z ∣)
    isAntisymˢ'⇔isAntisym' .snd ≤-antisym'  a b a≤b ¬ᵗa≡b = ≤-antisym'  a b a≤b (λ ∣z∣ → ∣∣-elim {P = λ _ → ⊥⊥} (λ _ → isProp⊥) ¬ᵗa≡b ∣z∣)

    isTightˢ⇔isTight .fst <-tightˢ a b a<b b<a = ∣ <-tightˢ a b a<b b<a ∣
    isTightˢ⇔isTight .snd <-tightᵖ a b a<b b<a = ∣∣-elim (λ c → is-set a b) (λ x → x) (<-tightᵖ a b a<b b<a)

    isTightˢ'⇔isTight' .fst <-tightˢ' a b ¬ᵗ[a<b⊔b<a] = ∣ <-tightˢ' a b ¬ᵗ[a<b⊔b<a] ∣
    isTightˢ'⇔isTight' .snd <-tightᵖ' a b ¬ᵗ[a<b⊔b<a] = ∣∣-elim (λ c → is-set a b) (λ x → x) (<-tightᵖ' a b ¬ᵗ[a<b⊔b<a])

    isTightˢ''⇔isTight'' .fst <-tightˢ'' a b ¬ᵗ[a<b⊎b<a] = ∣ <-tightˢ'' a b ¬ᵗ[a<b⊎b<a] ∣
    isTightˢ''⇔isTight'' .snd <-tightᵖ'' a b ¬ᵗ[a<b⊎b<a] = ∣∣-elim (λ c → is-set a b) (λ x → x) (<-tightᵖ'' a b ¬ᵗ[a<b⊎b<a])

    isTightˢ'''⇔isTight''' .fst #-tightˢ''' a b ¬ᵗ[a#b] = ∣ #-tightˢ''' a b ¬ᵗ[a#b] ∣
    isTightˢ'''⇔isTight''' .snd #-tightᵖ''' a b ¬ᵗ[a#b] = ∣∣-elim (λ c → is-set a b) (λ x → x) (#-tightᵖ''' a b ¬ᵗ[a#b])

    isTightˢ'''⇔isAntisymˢ <-asym .fst #-tight a b a≤b b≤a = #-tight a b (deMorgan₂-back' (b≤a , a≤b))
    isTightˢ'''⇔isAntisymˢ <-asym .snd ≤-antisym a b ¬ᵗa#b = let (b≤a , a≤b) = deMorgan₂' ¬ᵗa#b in ≤-antisym a b a≤b b≤a

    isTrichotomousˢ⇔isTrichotomous <-irreflˢ <-irrefl <-asym .fst <-trichoˢ a b with <-trichoˢ a b
    ... | inl a<b⊎b<a = inl a<b⊎b<a
    ... | inr a≡b     = inr ∣ a≡b ∣
    isTrichotomousˢ⇔isTrichotomous <-irreflˢ <-irrefl <-asym .snd <-tricho  a b with <-tricho a b
    ... | inl a<b⊎b<a = inl a<b⊎b<a
    ... | inr a≡b     = inr (∣∣-elim (λ c → is-set a b) (λ x → x) a≡b)

-- for these pathes, `A` and `hProp.fst` need to be in the same universe to omit ugly lifting into `ℓ-max ℓ ℓ'`
--   although this would be possible to have (with lifting)
module _ {ℓ : Level} {A : Type ℓ} (_≤_ : hPropRel A A ℓ)
  (let R   = _≤_)
  (let _<_ = R) -- different semantics
  (let _≤_ = R) --
  (let _#_ = R) --
  where
  -- equivalence of "not apart" and "equal"
  [¬ᵗ#]⇔[≡]  : hProp ℓ
  [¬ᵗ#]⇔[≡]  = ∀[ a ] ∀[ b ] ¬ (a # b) ⇔ a ≡ₚ b
  [¬ᵗ#]⇔[≡]ᵗ : Type (ℓ-suc ℓ)
  [¬ᵗ#]⇔[≡]ᵗ = ∀ a b → (¬ᵗ [ a # b ]) ≡ (a ≡ b)

  -- double negation elimination over _≡_
  dne-over-≡ᵗ : Type (ℓ-suc ℓ)
  dne-over-≡ᵗ = ∀(a b : A) → (¬ᵗ ¬ᵗ (a ≡ b)) ≡ (a ≡ b)

  abstract
    irrefl+tight⇒[¬ᵗ#]⇔[≡] : [ isIrrefl  _#_ ] → [ isTight''' _#_ ] → [ [¬ᵗ#]⇔[≡] ]
    irrefl+tight⇒[¬ᵗ#]⇔[≡] #-irrefl #-tight a b .fst ¬ᵗ[a#b] = #-tight a b ¬ᵗ[a#b]
    irrefl+tight⇒[¬ᵗ#]⇔[≡] #-irrefl #-tight a b .snd a≡b a#b = #-irrefl b (substₚ (λ x → x # b) a≡b a#b)

    [¬ᵗ#]≡[≡]⇒dne-over-≡ : [¬ᵗ#]⇔[≡]ᵗ → dne-over-≡ᵗ
    [¬ᵗ#]≡[≡]⇒dne-over-≡ [¬ᵗ#]≡[≡] a b =
      (    ¬ᵗ ¬ᵗ ( a ≡ b ) ≡⟨ (λ i → ¬ᵗ ¬ᵗ [¬ᵗ#]≡[≡] a b (~ i)) ⟩
        ¬ᵗ ¬ᵗ ¬ᵗ [ a # b ] ≡⟨ ¬¬-involutiveᵗ [ a # b ] ⟩
              ¬ᵗ [ a # b ] ≡⟨ [¬ᵗ#]≡[≡] a b ⟩
                   a ≡ b   ∎)

  -- consequences on sets
  module _ (is-set : isSet A) where
    -- equivalence of "not apart" and "equal" on sets
    [¬ᵗ#]⇔[≡ˢ] = ∀[ a ] ∀[ b ]             ¬ (a # b) ⇔ [ is-set ] a ≡ˢ b

    -- double negation elimination over _≡_ on sets
    dne-over-≡ˢ  = ∀[ a ] ∀[ b ] ¬ ¬ ([ is-set ] a ≡ˢ b) ⇔ [ is-set ] a ≡ˢ b

    irrefl+tight⇒[¬ᵗ#]⇔[≡ˢ]   : [ isIrrefl  _#_ ] → [ isTightˢ''' _#_ is-set ] → [ [¬ᵗ#]⇔[≡ˢ] ]
    [¬ᵗ#]⇔[≡ˢ]⇒dne-over-≡ˢ    : [ [¬ᵗ#]⇔[≡ˢ] ]                                 → [ dne-over-≡ˢ ]
    irrefl+tight⇒dne-over-≡ˢ  : [ isIrrefl  _#_ ] → [ isTightˢ''' _#_ is-set ] → [ dne-over-≡ˢ ]
    irrefl+tight⇒[¬ᵗ#]≡[≡ˢ]   : [ isIrrefl  _#_ ] → [ isTightˢ''' _#_ is-set ] → ∀ a b → (¬ᵗ [ a # b ]) ≡ (a ≡ b)
    irrefl+tight⇒dne-over-≡ˢᵗ : [ isIrrefl  _#_ ] → [ isTightˢ''' _#_ is-set ] → ∀(a b : A) → (¬ᵗ ¬ᵗ (a ≡ b)) ≡ (a ≡ b)

    -- x ≤ y  ≡ ¬(y < x)
    -- x <' y ≡ ¬(y ≤ x) ≡ ¬¬(x < y)
    -- ¬¬(x < y) ⇔ (x < y) ??
    -- x ≤ y ⇔ ∀[ ε ] (y < ε) ⇒ (x < ε)

    -- https://en.wikipedia.org/wiki/Total_order
    -- We can work the other way and start by choosing < as a transitive trichotomous binary relation; then a total order ≤ can be defined in two equivalent ways:
    -- https://en.wikipedia.org/wiki/Weak_ordering#Strict_weak_orderings

    -- IsStrictLinearOrder _<_ ⇒ IsLinearOrder _≤_

    irrefl+tight⇒[¬ᵗ#]⇔[≡ˢ] #-irrefl #-tight a b .fst ¬ᵗ[a#b] = #-tight a b ¬ᵗ[a#b]
    irrefl+tight⇒[¬ᵗ#]⇔[≡ˢ] #-irrefl #-tight a b .snd a≡b a#b = #-irrefl b (subst (λ x → [ x # b ]) a≡b a#b)

    irrefl+tight⇒[¬ᵗ#]≡[≡ˢ] #-irrefl #-tight a b = isoToPath γ where
      γ : Iso _ _
      γ .Iso.fun      ¬ᵗ[a#b] = #-tight a b ¬ᵗ[a#b]
      γ .Iso.inv      a≡b a#b = #-irrefl b (subst (λ x → [ x # b ]) a≡b a#b)
      γ .Iso.rightInv f       = is-set a b _ f
      γ .Iso.leftInv  g       = isProp[] (¬ (a #  b)) _ g

    [¬ᵗ#]⇔[≡ˢ]⇒dne-over-≡ˢ [¬ᵗ#]⇔[≡ˢ] a b = snd ( -- this first proof works better with `_≡⟨_⟩_`
      -- ( ¬ ¬ ([ is-set ]     a ≡ˢ b)) ⇔⟨ (map-× (subst (λ p → fst p → snd p) (cong₂ _,_ {! ¬¬-introᵗ (a ≡ b)  !} {!   !})) {!   !} $ swap $ [¬ᵗ#]⇔[≡ˢ] a b) ⟩
      ( ¬ ¬ ([ is-set ]     a ≡ˢ b)) ⇔⟨ (map-× (λ z z₁ z₂ → z₂ (λ z₃ → z₁ (λ z₄ → z z₄ z₃))) (λ z z₁ z₂ → z₂ (z (λ z₃ → z₁ (λ z₄ → z₄ z₃)))) $ swap $ [¬ᵗ#]⇔[≡ˢ] a b) ⟩ -- how did Agsy find this out??
      ( ¬              ¬ ¬ (a #  b)) ⇔⟨ ¬¬-involutive (a # b) ⟩
      ( ¬                  (a #  b)) ⇔⟨ [¬ᵗ#]⇔[≡ˢ] a b ⟩
      (      [ is-set ]     a ≡ˢ b ) ∎ᵖ)

    irrefl+tight⇒dne-over-≡ˢ  #-irrefl #-tight = [¬ᵗ#]⇔[≡ˢ]⇒dne-over-≡ˢ (irrefl+tight⇒[¬ᵗ#]⇔[≡ˢ] #-irrefl #-tight)

    irrefl+tight⇒dne-over-≡ˢᵗ #-irrefl #-tight = [¬ᵗ#]≡[≡]⇒dne-over-≡   (irrefl+tight⇒[¬ᵗ#]≡[≡ˢ] #-irrefl #-tight)

module _ {ℓ : Level} {A : Type ℓ}  (is-set : isSet A) where

  nzinvˢ''+comm⇒invnzˢ : (0f 1f : A) (_·_ : A → A → A) → ∀{ℓ'} → (_#_ : hPropRel A A ℓ')
                       → [ isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_ ⊓ isCommutativeˢ _·_ is-set
                         ⇒ isInverseNonzeroˢ   is-set 0f 1f _·_ _#_ ]
  nzinvˢ''+comm⇒invnzˢ 0f 1f _·_ _#_ (is-nzinv , ·-comm) x y x·y≡1 .fst = fst (is-nzinv x) ∣ y ,              x·y≡1 ∣
  nzinvˢ''+comm⇒invnzˢ 0f 1f _·_ _#_ (is-nzinv , ·-comm) x y x·y≡1 .snd = fst (is-nzinv y) ∣ x , ·-comm y x ∙ x·y≡1 ∣

module _ {ℓ ℓ'} {X : Type ℓ} {_<_ : hPropRel X X ℓ'} (<-SPO : [ isStrictPartialOrder  _<_ ])
  (let _#'_ : hPropRel X X ℓ'
       x #' y = (x < y) ⊔ (y < x)
       _≤'_ : hPropRel X X ℓ'
       x ≤' y = ¬ (y < x)
       (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
  ) where
  abstract
    -- Lemma 4.1.7.
    -- Given a strict partial order < on a set X:
    -- 1. we have an apartness relation defined by
    --    x # y := (x < y) ∨ (y < x), and

    #'-isApartnessRel : [ isApartnessRel _#'_ ]
    #'-isApartnessRel .IsApartnessRel.is-irrefl a a#a =
      case a#a as a < a ⊔ a < a ⇒ ⊥ of λ where
        (inl a<a) → <-irrefl _ a<a
        (inr a<a) → <-irrefl _ a<a
    #'-isApartnessRel .IsApartnessRel.is-sym     a b p = pathTo⇒ (⊔-comm (a < b) (b < a)) p
    #'-isApartnessRel .IsApartnessRel.is-cotrans a b p =
      case p as a < b ⊔ b < a ⇒ ∀[ x ] (a #' x) ⊔ (x #' b) of λ where
        (inl a<b) x → case (<-cotrans _ _ a<b x) as a < x ⊔ x < b ⇒ (a #' x) ⊔ (x #' b) of λ where
          (inl a<x) → inlᵖ (inlᵖ a<x)
          (inr x<b) → inrᵖ (inlᵖ x<b)
        (inr b<a) x → case (<-cotrans _ _ b<a x) as b < x ⊔ x < a ⇒ (a #' x) ⊔ (x #' b) of λ where
          (inl b<x) → inrᵖ (inrᵖ b<x)
          (inr x<a) → inlᵖ (inrᵖ x<a)

    -- 2. we have a preorder defined by
    --    x ≤ y := ¬ᵗ(y < x).

    ≤'-isPreorder : [ isPreorder _≤'_ ]
    ≤'-isPreorder .IsPreorder.is-refl = <-irrefl
    ≤'-isPreorder .IsPreorder.is-trans a b c ¬ᵗb<a ¬ᵗc<b c<a =
         ⊔-elim (c < b) (b < a) (λ _ → ⊥)
         (λ c<b → ¬ᵗc<b c<b)
         (λ b<a → ¬ᵗb<a b<a)
         (<-cotrans _ _ c<a b)

module _ {ℓ ℓ'} {X : Type ℓ} {_<_ : hPropRel X X ℓ'} (<-SPO : [ isStrictPartialOrder  _<_ ]) (<-asym : [ isAsym _<_ ])
  (let _#''_ : hPropRel X X ℓ'
       x #'' y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)
       _≤'_ : hPropRel X X ℓ'
       x ≤' y = ¬ (y < x)
       (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
  ) where
  abstract
    #''-isApartnessRel : [ isApartnessRel _#''_ ]
    #''-isApartnessRel .IsApartnessRel.is-irrefl a (inl a<a) = <-irrefl _ a<a
    #''-isApartnessRel .IsApartnessRel.is-irrefl a (inr a<a) = <-irrefl _ a<a
    #''-isApartnessRel .IsApartnessRel.is-sym     a b p = ⊎-swap p
    #''-isApartnessRel .IsApartnessRel.is-cotrans a b (inl a<b) x =
      case (<-cotrans _ _ a<b x) as a < x ⊔ x < b ⇒ (a #'' x) ⊔ (x #'' b) of λ where
        (inl a<x) → inlᵖ (inl a<x)
        (inr x<b) → inrᵖ (inl x<b)
    #''-isApartnessRel .IsApartnessRel.is-cotrans a b (inr b<a) x =
      case (<-cotrans _ _ b<a x) as b < x ⊔ x < a ⇒ (a #'' x) ⊔ (x #'' b) of λ where
        (inl b<x) → inrᵖ (inr b<x)
        (inr x<a) → inlᵖ (inr x<a)

module _ {ℓ ℓ'} {X : Type ℓ} {_<_ : hPropRel X X ℓ'} (<-SLO : [ isStrictLinearOrder  _<_ ])
  (let _≤'_ : hPropRel X X ℓ'
       x ≤' y = ¬ (y < x)
       (isstrictlinearorder <-irrefl <-trans <-tricho) = <-SLO

  ) where
  private
    <-cotrans : [ isCotrans _<_ ]
    <-cotrans = IsStrictPartialOrder.is-cotrans (strictlinearorder⇒strictpartialorder _<_ <-SLO)

  abstract
    ≤'-isLinearOrder : [ isLinearOrder _≤'_ ]
    IsLinearOrder.is-connex  ≤'-isLinearOrder a b with <-tricho a b
    ... | inl (inl a<b) = inlᵖ λ b<a → <-irrefl a $ <-trans a b a a<b b<a
    ... | inl (inr b<a) = inrᵖ λ a<b → <-irrefl a $ <-trans a b a a<b b<a
    ... | inr      a≡b  = inlᵖ λ b<a → <-irrefl b (substₚ (λ p → b < p) a≡b b<a)
    IsLinearOrder.is-antisym ≤'-isLinearOrder a b a≤b b≤a with <-tricho a b
    ... | inl (inl a<b) = ⊥-elim (b≤a a<b)
    ... | inl (inr b<a) = ⊥-elim (a≤b b<a)
    ... | inr      a≡b  = a≡b
    IsLinearOrder.is-trans   ≤'-isLinearOrder a b c a≤b b≤c c<a =
      let γ : [ ¬ (b < a ⊔ c < b) ]
          γ = deMorgan₂-back (b < a) (c < b) (a≤b , b≤c)
          κ : [ b < a ⊔ c < b ]
          κ = pathTo⇐ (⊔-comm (b < a) (c < b)) $ <-cotrans c a c<a b
      in γ κ
