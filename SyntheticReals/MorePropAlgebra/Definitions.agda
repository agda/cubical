{-# OPTIONS --cubical --no-import-sorts  #-}

module SyntheticReals.MorePropAlgebra.Definitions where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣)
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

open import SyntheticReals.Utils
open import SyntheticReals.MoreLogic.Definitions renaming
  ( _ᵗ⇒_ to infixr 0 _ᵗ⇒_
  ; ∀ᵖ[∶]-syntax to infix -4 ∀ᵖ[∶]-syntax
  ; ∀ᵖ〚∶〛-syntax to infix -4 ∀ᵖ〚∶〛-syntax
  ; ∀ᵖ!〚∶〛-syntax to infix -4 ∀ᵖ!〚∶〛-syntax
  ; ∀〚∶〛-syntax to infix -4 ∀〚∶〛-syntax
  ; Σᵖ[]-syntax   to infix -4 Σᵖ[]-syntax
  ; Σᵖ[∶]-syntax  to infix -4 Σᵖ[∶]-syntax
  )

-- hProps of relations
module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') where

  isRefl      =                      ∀[ a ]    R a a
  isIrrefl    =                      ∀[ a ] ¬ (R a a)
  isIrrefl'   =                      ∀[ a ] ∀[ b ] (  R a b   ⊔   R b a  )  ⇒ ¬(          a ≡ₚ b)
  isIrrefl''  =                      ∀[ a ] ∀[ b ] ([ R a b ] ⊎ [ R b a ]) ᵗ⇒ ¬(          a ≡ₚ b)
  isIrreflˢ'' = λ(isset : isSet A) → ∀[ a ] ∀[ b ] ([ R a b ] ⊎ [ R b a ]) ᵗ⇒ ¬([ isset ] a ≡ˢ b)

  isTrans     =                      ∀[ a ] ∀[ b ] ∀[ x ] R a b ⇒         R b x ⇒ R a x
  isCotrans   =                      ∀[ a ] ∀[ b ]        R a b ⇒ (∀[ x ] R a x ⊔ R x b)

  isConnex    =                      ∀[ a ] ∀[ b ]                        R a b ⊔ R b a

  -- isTrichotomous = λ(<-irrefl ∶ [ isIrrefl' _<_ ]) → λ(<-asym : isAsym _<_) ∀[ a ] ∀[ b ] [ <-irrefl ]
  -- [ P ] → ¬ᵗ [ Q ]
  -- a ≡ b ⊎ (a < b ⊎ b < a)
  -- (a < b ⊎ b < a) ⇒ (¬ a ≡ b) -- also irrefl
  -- isTight

  -- two variants of asymmetry
  --
  --   IsAsym  R = ∀ a b → [     R a b   ⇒ ¬ R b a ]
  --   IsAsym' R = ∀ a b → [ ¬ (R a b   ⊓    R b a) ]
  --
  -- which are equivalent
  --
  --   isAsymᵖ≡'  :  isAsym  R ≡ isAsym'  R
  --
  -- but it seems that this one is not equivalent:
  --
  --   ∀ a b → [ (¬ R b a) ⇒ R a b ]

  isSym       =                      ∀[ a ] ∀[ b ]    R a b ⇒   R b a
  isAsym      =                      ∀[ a ] ∀[ b ]    R a b ⇒ ¬ R b a
  isAsym'     =                      ∀[ a ] ∀[ b ] ¬ (R a b ⊓   R b a)
  isAsym''    =                      ∀[ a ] ∀[ b ] ¬  R a b ⇒   R b a  -- not equivalent! (weaker)

  isTrichotomous  :                     (<-irrefl : [ isIrrefl''        ]) → (<-asym : [ isAsym ]) → hProp _
  isTrichotomousˢ : (isset : isSet A) → (<-irrefl : [ isIrreflˢ'' isset ]) → (<-asym : [ isAsym ]) → hProp _

  isTrichotomous        isirrefl isasym = ∀[ a ] ∀[ b ] ([ isirrefl a b ] ([ isasym a b ] R a b ⊎ᵖ R b a ) ⊎ᵖ (          a ≡ₚ b))
  isTrichotomousˢ isset isirrefl isasym = ∀[ a ] ∀[ b ] ([ isirrefl a b ] ([ isasym a b ] R a b ⊎ᵖ R b a ) ⊎ᵖ ([ isset ] a ≡ˢ b))

  isAntisym   =                      ∀[ a ] ∀[ b ]    R a b ⇒             R b a   ⇒            a ≡ₚ b
  isAntisymˢ  = λ(isset : isSet A) → ∀[ a ] ∀[ b ]    R a b ⇒             R b a   ⇒ ([ isset ] a ≡ˢ b)
  isAntisym'  =                      ∀[ a ] ∀[ b ]    R a b ⇒ ¬(          a ≡ₚ b) ⇒            R b a
  isAntisymˢ' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]    R a b ⇒ ¬([ isset ] a ≡ˢ b) ⇒            R b a

  -- tightness is closely related to antisymmetry:
  --
  --   R-antisym : [    R a b ] → [    R b a ] → a ≡ b
  --   R-tight   : [ ¬ R a b ] → [ ¬ R b a ] → a ≡ b
  --
  -- this becomes even more obvious if we regard the intended use: when _≤_ and _#_ are derived from _<_
  --
  --    a ≤ b = ¬ (b < a)
  --    a # b = ¬ ([ a < b ] ⊎ [ b < a ])
  --
  -- and indeed, we get
  --
  --   isTight   _<_ ≡ isAntisym   (λ a b → ¬ (b < a))
  --   isTight'  _<_ ≡ isTight'''  (λ a b → (a < b) ⊔ (b < a))
  --
  -- In that case, `≤-antisym` and `#-tight` are almost the same, definitionally:
  --
  --   ≤-antisym : [ ¬ (b < a) ] → [ ¬ (a < b) ] → a ≡ b
  --   ≤-antisym : [ ¬ (b < a) ] × [ ¬ (a < b) ] → a ≡ b -- by curry/uncurry
  --   ≤-antisym : ¬ᵗ ( [ b < a ]  ⊎     [ a < b ]) → a ≡ b -- by deMorgan
  --   #-tight   : [ ¬ (a < b) ] → [ ¬ (b < a) ] → a ≡ b
  --   #-tight   : [ ¬ (a < b) ] × [ ¬ (b < a) ] → a ≡ b -- by curry/uncurry
  --   #-tight   : ¬ᵗ ( [ a < b ]  ⊎     [ b < a ]) → a ≡ b -- by deMorgan
  --
  -- We provide a few variants of tightness
  --
  isTight     =                      ∀[ a ] ∀[ b ]      ¬ R a b   ⇒  ¬ R b a      ⇒           a ≡ₚ b -- on _<_, "canonical"
  isTightˢ    = λ(isset : isSet A) → ∀[ a ] ∀[ b ]      ¬ R a b   ⇒  ¬ R b a      ⇒ [ isset ] a ≡ˢ b -- on _<_
  isTight'    =                      ∀[ a ] ∀[ b ]  ¬  (  R a b   ⊔    R b a   )  ⇒           a ≡ₚ b -- on _<_, definitional `isTight-ᵖ'≡'''`
  isTightˢ'   = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬  (  R a b   ⊔    R b a   )  ⇒ [ isset ] a ≡ˢ b -- on _<_
  isTight''   =                      ∀[ a ] ∀[ b ] (¬ᵗ ([ R a b ] ⊎  [ R b a ])) ᵗ⇒           a ≡ₚ b -- on _<_, definitional `isTight-ᵖ''≡'''`
  isTightˢ''  = λ(isset : isSet A) → ∀[ a ] ∀[ b ] (¬ᵗ ([ R a b ] ⊎  [ R b a ])) ᵗ⇒ [ isset ] a ≡ˢ b -- on _<_, "convenient"
  isTight'''  =                      ∀[ a ] ∀[ b ]  ¬     R a b                   ⇒           a ≡ₚ b -- on _#_
  isTightˢ''' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬     R a b                   ⇒ [ isset ] a ≡ˢ b -- on _#_, also "convenient"
  --
  -- where the very first one, `IsTight` corresponds to a "canonical" definition,
  -- the later one, `IsTightˢ''` is the "most convenient" one to use for `a # b = ¬ ([ a < b ] ⊎ [ b < a ])` on sets.
  -- and the last ones `IsTight'''` and `IsTightˢ'''` are for "_#_" instead of "_<_".
  --
  -- These tightness definitions are all equivalent in the following sense:
  --
  --   isTight-ˢ≡        : (is-set : isSet A)         → isTightˢ    is-set _<_ ≡ isTight     _<_
  --   isTight-ˢ'≡'      : (is-set : isSet A)         → isTightˢ'   is-set _<_ ≡ isTight'    _<_
  --   isTight-ˢ''≡''    : (is-set : isSet A)         → isTightˢ''  is-set _<_ ≡ isTight''   _<_
  --   isTight-ˢ'''≡'''  : (is-set : isSet A)         → isTightˢ''' is-set _#_ ≡ isTight'''  _#_
  --   isTight-≡'        :                              isTight            _<_ ≡ isTight'    _<_
  --   isTight-'≡''      :                              isTight'           _<_ ≡ isTight''   _<_
  --   isTight-'≡'''     :                              isTight'           _<_ ≡ isTight'''  (λ a b →                (a < b) ⊔  (b < a))
  --   isTight-''≡'''    : (<-asym : [ isAsym  _<_ ]) → isTight''          _<_ ≡ isTight'''  (λ a b → [ <-asym a b ] (a < b) ⊎ᵖ (b < a))
  --
  -- where `isTight-ᵖ'≡'''`  and `isTight-ᵖ''≡'''`  hold definitionally.


-- common definitions of less equal _≤_ and apartness _#_ with respect to _<_
module _ {ℓ ℓ'} {X : Type ℓ} {_<_ : hPropRel X X ℓ'} where

  _#'_ : hPropRel X X ℓ'
  _#'_ x y = (x < y) ⊔ (y < x)

  -- a variant that omits propositional truncation by using asymmetry of _<_
  _#''_ : {<-asym : [ isAsym  _<_ ]} → hPropRel X X ℓ'
  _#''_ {<-asym = <-asym} x y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

  _≤'_ : hPropRel X X ℓ'
  _≤'_ x y = ¬ (y < x)

  -- this is how Bridges 1999 defines _≤_
  _≤''_ : hPropRel X X (ℓ-max ℓ ℓ')
  x ≤'' y = ∀[ ε ] (y < ε) ⇒ (x < ε) -- (∀ ε → [ y < ε ] → [ x < ε ]) , isPropΠ2 (λ ε y<ε → isProp[] (x < ε))

-- combined hProps of relations
module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ')
  (let _<_ = R; _≤_ = R) -- "strict" is denoted by _<_, and "non-strict" by _≤_
  where

  record IsApartnessRel : Type (ℓ-max ℓ ℓ') where
    constructor isapartnessrel
    field
      is-irrefl  : ∀ a → [ ¬ R a a ]
      is-sym     : ∀ a b → [ R a b ] → [ R b a ]
      is-cotrans : ∀ a b → [ R a b ] → ∀ x → [ R a x ⊔ R x b ]

    _ : [ isIrrefl   R ]; _ = is-irrefl
    _ : [ isSym      R ]; _ = is-sym
    _ : [ isCotrans  R ]; _ = is-cotrans

  isApartnessRel  : hProp (ℓ-max ℓ ℓ')
  isApartnessRel  .fst = IsApartnessRel
  isApartnessRel  .snd (isapartnessrel a₀ b₀ c₀) (isapartnessrel a₁ b₁ c₁) = φ where
    abstract φ = λ i → isapartnessrel (snd (isIrrefl  R) a₀ a₁ i) (snd (isSym  R) b₀ b₁ i) (snd (isCotrans  R) c₀ c₁ i)

  record IsStrictPartialOrder : Type (ℓ-max ℓ ℓ') where
    constructor isstrictpartialorder
    field
      is-irrefl  : ∀ a → [ ¬ a < a ]
      is-trans   : ∀ a b x → [ a < b ] → [ b < x ] → [ a < x ]
      is-cotrans : ∀ a b → [ a < b ] → ∀ x → [ a < x ⊔ x < b ]

    _ : [ isIrrefl   _<_ ]; _ = is-irrefl
    _ : [ isTrans    _<_ ]; _ = is-trans
    _ : [ isCotrans  _<_ ]; _ = is-cotrans

  isStrictPartialOrder  : hProp (ℓ-max ℓ ℓ')
  isStrictPartialOrder  .fst = IsStrictPartialOrder
  isStrictPartialOrder  .snd (isstrictpartialorder a₀ b₀ c₀) (isstrictpartialorder a₁ b₁ c₁) = φ where
    abstract φ = λ i → isstrictpartialorder (snd (isIrrefl _<_) a₀ a₁ i) (snd (isTrans _<_) b₀ b₁ i) (snd (isCotrans _<_) c₀ c₁ i)

  record IsPreorder : Type (ℓ-max ℓ ℓ') where
    constructor ispreorder
    field
      is-refl    : ∀ a → [ R a a ]
      is-trans   : ∀ a b x → [ R a b ] → [ R b x ] → [ R a x ]

    _ : [ isRefl   R ]; _ = is-refl
    _ : [ isTrans  R ]; _ = is-trans

  isPreorder  : hProp (ℓ-max ℓ ℓ')
  isPreorder  .fst = IsPreorder
  isPreorder  .snd (ispreorder a₀ b₀) (ispreorder a₁ b₁) = φ where
    abstract φ = λ i → ispreorder (snd (isRefl  R) a₀ a₁ i) (snd (isTrans  R) b₀ b₁ i)

  record IsPartialOrder : Type (ℓ-max ℓ ℓ') where
    constructor ispartialorder
    field
      is-refl    : ∀ a → [ a ≤ a ]
      is-antisym : ∀ a b → [ a ≤ b ] → [ b ≤ a ] → [ a ≡ₚ b ]
      is-trans   : ∀ a b x → [ a ≤ b ] → [ b ≤ x ] → [ a ≤ x ]

    _ : [ isRefl     _≤_ ]; _ = is-refl
    _ : [ isAntisym  _≤_ ]; _ = is-antisym
    _ : [ isTrans    _≤_ ]; _ = is-trans

  isPartialOrder  : hProp (ℓ-max ℓ ℓ')
  isPartialOrder  .fst = IsPartialOrder
  isPartialOrder  .snd (ispartialorder a₀ b₀ c₀) (ispartialorder a₁ b₁ c₁) = φ where
    abstract φ = λ i → ispartialorder (snd (isRefl _≤_) a₀ a₁ i) (snd (isAntisym _≤_) b₀ b₁ i) (snd (isTrans _≤_) c₀ c₁ i)

  record IsLinearOrder : Type (ℓ-max ℓ ℓ') where
    constructor islinearorder
    field
      is-connex  : ∀ a b → [ a ≤ b ⊔ b ≤ a ]
      is-antisym : ∀ a b → [ a ≤ b ] → [ b ≤ a ] → [ a ≡ₚ b ]
      is-trans   : ∀ a b x → [ a ≤ b ] → [ b ≤ x ] → [ a ≤ x ]

    _ : [ isConnex   _≤_ ]; _ = is-connex
    _ : [ isAntisym  _≤_ ]; _ = is-antisym
    _ : [ isTrans    _≤_ ]; _ = is-trans

  isLinearOrder : hProp (ℓ-max ℓ ℓ')
  isLinearOrder .fst = IsLinearOrder
  isLinearOrder .snd (islinearorder a₀ b₀ c₀) (islinearorder a₁ b₁ c₁) = φ where
    abstract φ = λ i → islinearorder (snd (isConnex _≤_) a₀ a₁ i) (snd (isAntisym _≤_) b₀ b₁ i) (snd (isTrans _≤_) c₀ c₁ i)

  record IsStrictLinearOrder : Type (ℓ-max ℓ ℓ') where
    constructor isstrictlinearorder
    field
      is-irrefl  : ∀ a → [ ¬ a < a ]
      is-trans   : ∀ a b x → [ a < b ] → [ b < x ] → [ a < x ]
      is-tricho  : ∀ a b → ([ a < b ] ⊎ [ b < a ]) ⊎ [ a ≡ₚ b ]

    private
      is-asym : ∀ a b → [ a < b ] → [ ¬ b < a ]
      is-asym a b a<b b<a = is-irrefl _ (is-trans _ _ _ a<b b<a)

      is-irrefl'' : ∀ a b → [ a < b ] ⊎ [ b < a ] → [ ¬(a ≡ₚ b) ]
      is-irrefl'' a b (inl a<b) a≡b = is-irrefl _ (substₚ (λ p → p < b) a≡b a<b)
      is-irrefl'' a b (inr b<a) a≡b = is-irrefl _ (substₚ (λ p → b < p) a≡b b<a)

      _ : [ isIrrefl       _<_                     ]; _ = is-irrefl
      _ : [ isTrans        _<_                     ]; _ = is-trans
      _ : [ isTrichotomous _<_ is-irrefl'' is-asym ]; _ = is-tricho

  isStrictLinearOrder : hProp (ℓ-max ℓ ℓ')
  isStrictLinearOrder .fst = IsStrictLinearOrder
  isStrictLinearOrder .snd (isstrictlinearorder a₀ b₀ c₀) (isstrictlinearorder a₁ b₁ c₁) = φ where
    abstract φ = λ i → let is-irrefl = snd (isIrrefl       _<_                    ) a₀ a₁ i
                           is-trans  = snd (isTrans        _<_                    ) b₀ b₁ i
                           is-asym : ∀ a b → [ a < b ] → [ ¬ b < a ]
                           is-asym a b a<b b<a = is-irrefl _ (is-trans _ _ _ a<b b<a)
                           is-irrefl'' : ∀ a b → [ a < b ] ⊎ [ b < a ] → [ ¬(a ≡ₚ b) ]
                           is-irrefl'' a b = λ
                             { (inl a<b) a≡b → is-irrefl _ (substₚ (λ p → p < b) a≡b a<b)
                             ; (inr b<a) a≡b → is-irrefl _ (substₚ (λ p → b < p) a≡b b<a)
                             }
                           is-tricho = snd (isTrichotomous _<_ is-irrefl'' is-asym) c₀ c₁ i
                       in isstrictlinearorder is-irrefl is-trans is-tricho

-- properties tied to some operation `op` on sets
module _ {ℓ : Level} {A : Type ℓ} (op : A → A → A) (is-set : isSet A)
  (let _·_  = op -- different semantics
       _+_  = op --
       _≡ˢ_ = λ(x y : A) → [ is-set ] x ≡ˢ y
       infixl 7 _·_
       infixl 5 _+_
       infixl 4 _≡ˢ_
  ) where

  isAssociativeˢ =            ∀[ x ] ∀[ y ] ∀[ z ]   x · (y · z) ≡ˢ (x · y) · z
  isIdentityˢ    = λ(ε : A) → ∀[ x ]               ( x · ε ≡ˢ x) ⊓ ( ε · x ≡ˢ x)
  isCommutativeˢ =            ∀[ x ] ∀[ y ]                x + y ≡ˢ y + x

-- other properties
module _ {ℓ : Level} {A : Type ℓ} where
  is-+-#-Extensional  :             (_+_     : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ')                                                → hProp _
  is-+-<-Extensional  :             (_+_     : A → A → A)              → ∀{ℓ'} → (_<_ : hPropRel A A ℓ')                                                → hProp _

  is-+-#-Extensional         _+_ _#_      = ∀[ w ] ∀[ x ] ∀[ y ] ∀[ z ]         (w + x) # (y + z) ⇒                    (w # y) ⊔ (x # z)
  is-+-<-Extensional         _+_ _<_      = ∀[ w ] ∀[ x ] ∀[ y ] ∀[ z ]         (w + x) < (y + z) ⇒                    (w < y) ⊔ (x < z)

  isMin : ∀{ℓ'} → (_≤_ : hPropRel A A ℓ') (min : A → A → A) → hProp _
  isMax : ∀{ℓ'} → (_≤_ : hPropRel A A ℓ') (max : A → A → A) → hProp _

  isMin _≤_ min  = ∀[ x ] ∀[ y ] ∀[ z ] z ≤ (min x y) ⇔ z ≤ x ⊓ z ≤ y
  isMax _≤_ max  = ∀[ x ] ∀[ y ] ∀[ z ] (max x y) ≤ z ⇔ x ≤ z ⊓ y ≤ z

  operation_preserves_when_ : (op : A → A → A) → ∀{ℓ'} → (R : hPropRel A A ℓ') → ∀{ℓ''} → (A → hProp ℓ'') → hProp _
  operation_reflects_when_  : (op : A → A → A) → ∀{ℓ'} → (R : hPropRel A A ℓ') → ∀{ℓ''} → (A → hProp ℓ'') → hProp _
  operation_reflects_〚when〛 : (op : A → A → A) → ∀{ℓ'} → (R : hPropRel A A ℓ') → ∀{ℓ''} → (A → hProp ℓ'') → hProp _
  operation_creates_when_  : (op : A → A → A) → ∀{ℓ'} → (R : hPropRel A A ℓ') → ∀{ℓ''} → (A → hProp ℓ'') → hProp _

  operation _·_ preserves _<_  when  P = ∀[ x ] ∀[ y ] ∀[ z ] P z ⇒ x < y ⇒ (x · z) < (y · z)
  operation _·_ reflects  _<_  when  P = ∀[ x ] ∀[ y ] ∀[ z ] P z ⇒ (x · z) < (y · z) ⇒ x < y
  operation _·_ reflects  _<_ 〚when〛 P = ∀[ x ] ∀[ y ] ∀[ z ] ∀〚 _ ∶ [ P z ] 〛 (x · z) < (y · z) ⇒ x < y
  operation _·_ creates   _<_  when  P = ∀[ x ] ∀[ y ] ∀[ z ] P z ⇒ (x < y ⇔ (x · z) < (y · z))


isAbsNonnegative             : ∀{ℓ} {F : Type ℓ}                                                      {Rℓ Rℓ'} {R : Type Rℓ}                     (0ᴿ : R)                         (_≤ᴿ_ : hPropRel R R Rℓ') (abs : F → R) → hProp _
isAbsCreatesZero             : ∀{ℓ} {F : Type ℓ} (is-set  : isSet F) (0f : F)                         {Rℓ Rℓ'} {R : Type Rℓ} (is-setᴿ : isSet R) (0ᴿ : R)                         (_≤ᴿ_ : hPropRel R R Rℓ') (abs : F → R) → hProp _
isAbsPreservesMultiplication : ∀{ℓ} {F : Type ℓ}                              (     _·_  : F → F → F) {Rℓ    } {R : Type Rℓ} (is-setᴿ : isSet R)          (     _·ᴿ_ : R → R → R)                           (abs : F → R) → hProp _
isAbsTriangleInequality      : ∀{ℓ} {F : Type ℓ}                              (_+_       : F → F → F) {Rℓ Rℓ'} {R : Type Rℓ}                              (_+ᴿ_      : R → R → R) (_≤ᴿ_ : hPropRel R R Rℓ') (abs : F → R) → hProp _

isAbsNonnegative                                       0ᴿ           _≤ᴿ_ abs = ∀[ x ]                                     0ᴿ ≤ᴿ (abs x)
isAbsCreatesZero             is-set 0f         is-setᴿ 0ᴿ           _≤ᴿ_ abs = ∀[ x ]                   ([ is-set ] x ≡ˢ 0f  ⇔ [ is-setᴿ ] abs x ≡ˢ 0ᴿ)
isAbsPreservesMultiplication               _·_ is-setᴿ         _·ᴿ_      abs = ∀[ x ] ∀[ y ] [ is-setᴿ ]       (abs (x · y)) ≡ˢ (abs x ·ᴿ abs y)
isAbsTriangleInequality                _+_                _+ᴿ_      _≤ᴿ_ abs = ∀[ x ] ∀[ y ]                    abs (x + y)  ≤ᴿ (abs x +ᴿ abs y)

record IsAbsˢ
  { ℓ     : Level} {F : Type ℓ } (is-set  : isSet F) (0f : F) (_+_  _·_  : F → F → F)
  {Rℓ Rℓ' : Level} {R : Type Rℓ} (is-setᴿ : isSet R) (0ᴿ : R) (_+ᴿ_ _·ᴿ_ : R → R → R) (_≤ᴿ_ : hPropRel R R Rℓ')
  (abs : F → R)
  : Type (ℓ-suc (ℓ-max ℓ (ℓ-max Rℓ Rℓ')))
  where
  constructor isabs
  field
    is-0≤abs        : ∀ x   → [                  0ᴿ ≤ᴿ (abs x)                ]
    abs-creates-0   : ∀ x   → [ [ is-set ] x ≡ˢ 0f  ⇔ [ is-setᴿ ] abs x ≡ˢ 0ᴿ ]
    abs-preserves-· : ∀ x y →         (abs (x · y)) ≡  (abs x ·ᴿ abs y)
    triangle-ineq   : ∀ x y → [        abs (x + y)  ≤ᴿ (abs x +ᴿ abs y)       ]

  _ : [ isAbsNonnegative 0ᴿ _≤ᴿ_ abs                      ]; _ = is-0≤abs
  _ : [ isAbsCreatesZero is-set 0f is-setᴿ 0ᴿ _≤ᴿ_ abs    ]; _ = abs-creates-0
  _ : [ isAbsPreservesMultiplication _·_ is-setᴿ _·ᴿ_ abs ]; _ = abs-preserves-·
  _ : [ isAbsTriangleInequality _+_ _+ᴿ_ _≤ᴿ_ abs         ]; _ = triangle-ineq

  abs-preserves-0 : ∀ x → x ≡ 0f → abs x ≡ 0ᴿ
  abs-preserves-0 x = abs-creates-0 x .fst

  abs-reflects-0 : ∀ x → abs x ≡ 0ᴿ → x ≡ 0f
  abs-reflects-0 x = abs-creates-0 x .snd

isAbs : { ℓ     : Level} {F : Type ℓ } (is-set  : isSet F) (0f : F) (_+_  _·_  : F → F → F)
        {Rℓ Rℓ' : Level} {R : Type Rℓ} (is-setᴿ : isSet R) (0ᴿ : R) (_+ᴿ_ _·ᴿ_ : R → R → R) (_≤ᴿ_ : hPropRel R R Rℓ')
        (abs : F → R)
        → hProp (ℓ-suc (ℓ-max ℓ (ℓ-max Rℓ Rℓ')))
isAbs is-set 0f _+_ _·_ is-setᴿ 0ᴿ _+ᴿ_ _·ᴿ_ _≤ᴿ_ abs .fst = IsAbsˢ is-set 0f _+_ _·_ is-setᴿ 0ᴿ _+ᴿ_ _·ᴿ_ _≤ᴿ_ abs
isAbs is-set 0f _+_ _·_ is-setᴿ 0ᴿ _+ᴿ_ _·ᴿ_ _≤ᴿ_ abs .snd (isabs a₀ b₀ c₀ d₀) (isabs a₁ b₁ c₁ d₁) = φ where
  abstract φ = λ i → isabs (snd (isAbsNonnegative 0ᴿ _≤ᴿ_ abs) a₀ a₁ i) (snd (isAbsCreatesZero is-set 0f is-setᴿ 0ᴿ _≤ᴿ_ abs) b₀ b₁ i)
                     (snd (isAbsPreservesMultiplication _·_ is-setᴿ _·ᴿ_ abs) c₀ c₁ i) (snd (isAbsTriangleInequality _+_ _+ᴿ_ _≤ᴿ_ abs) d₀ d₁ i)

-- other properties on sets
module _ {ℓ : Level} {A : Type ℓ} (is-set : isSet A)
  (let _≡ˢ_ = λ(x y : A) → [ is-set ] x ≡ˢ y; infixl 4 _≡ˢ_) where

  -- NOTE: the left  inverse is "on the right" of `_⊓_` (you get it with `snd`)
  --   and the right inverse is "on the left"  of `_⊓_` (you get it with `fst`)
  --   .. this is how it's done in the cubical standard library

  isInverseˢ          : (0g    : A) (_+_     : A → A → A) (-_ : A → A)                                                                                  → hProp _
  isDistributiveˢ     :             (_+_ _·_ : A → A → A)                                                                                               → hProp _
  isNonzeroInverseˢ'  : (0f 1f : A) (    _·_ : A → A → A)                                                  (_⁻¹ : (x : A) → {{ ! [ ¬'(x ≡ 0f) ] }} → A) → hProp _
  isNonzeroInverseˢ   : (0f 1f : A) (    _·_ : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ') → (_⁻¹ : (x : A) → {{   [    x # 0f  ] }} → A) → hProp _
  isNonzeroInverseˢ'' : (0f 1f : A) (    _·_ : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ')                                                → hProp _
  -- isNonzeroInverseˢ''' : (0f 1f : A) (    _·_ : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ')                                                → hProp _
  isInverseNonzeroˢ   : (0f 1f : A) (    _·_ : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ')                                                → hProp _

  isInverseˢ          0g _+_ -_         = ∀[ x ]                 (   x  + (- x) ≡ˢ 0g)
                                                               ⊓ ((- x) +    x  ≡ˢ 0g)

  isDistributiveˢ     _+_ _·_           = ∀[ x ] ∀[ y ] ∀[ z ]   ( x · (y +  z) ≡ˢ (x · y) + (x · z))
                                                               ⊓ ((x +  y) · z  ≡ˢ (x · z) + (y · z))

  -- classical notion of inverse operating on `¬(x ≡ 0)`, used in `IsClassicalField`
  --   `∀ᵖ!〚_〛_` creates in instance argument of type `!_`
  --   because `¬'(x ≡ 0f)` is a function type with an explicit argument and won't be considered in instance search
  isNonzeroInverseˢ'  0f 1f _·_ _⁻¹     = ∀[ x ] ∀ᵖ!〚 p ∶ ¬'(x ≡ 0f) 〛    (x · (x ⁻¹) {{ p }} ≡ˢ 1f)
                                                                        ⊓ ((x ⁻¹) {{ p }} · x ≡ˢ 1f)

  -- constructive notion of inverse operating on `x # 0`
  --   `∀ᵖ〚_〛_` creates in instance argument
  isNonzeroInverseˢ   0f 1f _·_ _#_ _⁻¹ = ∀[ x ] ∀ᵖ〚 p ∶ x # 0f 〛         (x · (x ⁻¹) {{ p }} ≡ˢ 1f)
                                                                        ⊓ ((x ⁻¹) {{ p }} · x ≡ˢ 1f)

  -- constructive notion of inverse
  -- this is the formulation in Booij2020, used in `IsAlmostOrderedField`
  --   we need to proof uniqueness of inverses to obtain `_⁻¹` for `isNonzeroInverseˢ`
  isNonzeroInverseˢ'' 0f 1f _·_ _#_     = ∀[ x ]        (∃[ y ] x · y ≡ˢ 1f) ⇔ x # 0f
  -- isNonzeroInverseˢ''' 0f 1f _·_ _#_    = ∀[ x ]        (Σᵖ[ y ] x · y ≡ˢ 1f) ⇔ x # 0f

  isInverseNonzeroˢ   0f 1f _·_ _#_     = ∀[ x ] ∀[ y ] x · y ≡ˢ 1f ⇒ x # 0f ⊓ y # 0f
