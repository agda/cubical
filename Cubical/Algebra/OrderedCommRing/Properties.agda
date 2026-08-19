module Cubical.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommSemiring
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Semigroup

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.QuosetReasoning
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' ℓ'' : Level

OrderedCommRing→StrictOrder : OrderedCommRing ℓ ℓ' → StrictOrder ℓ ℓ'
OrderedCommRing→StrictOrder R .fst = R .fst
OrderedCommRing→StrictOrder R .snd = strictorderstr _ isStrictOrder where
  open OrderedCommRingStr (str R)

OrderedCommRing→Ring : OrderedCommRing ℓ ℓ' → Ring ℓ
OrderedCommRing→Ring = CommRing→Ring ∘ OrderedCommRing→CommRing

OrderedCommRing→Poset : OrderedCommRing ℓ ℓ' → Poset ℓ ℓ'
OrderedCommRing→Poset = Pseudolattice→Poset ∘ OrderedCommRing→PseudoLattice

OrderedCommRing→Quoset : OrderedCommRing ℓ ℓ' → Quoset ℓ ℓ'
OrderedCommRing→Quoset = StrictOrder→Quoset ∘ OrderedCommRing→StrictOrder

OrderedCommRing→Apartness : OrderedCommRing ℓ ℓ' → Apartness ℓ ℓ'
OrderedCommRing→Apartness = StrictOrder→Apartness ∘ OrderedCommRing→StrictOrder

module _ (R' : OrderedCommRing ℓ ℓ') where
  private
    R = fst R'
    RCR = OrderedCommRing→CommRing R'
  open RingTheory (OrderedCommRing→Ring R')
  open OrderedCommRingStr (snd R')

  module OrderedCommRingReasoning where
    open <-≤-Reasoning
      (fst R')
      (str (OrderedCommRing→Poset  R'))
      (str (OrderedCommRing→Quoset R'))
      (λ x {y} {z} → <-≤-trans x y z)
      (λ x {y} {z} → ≤-<-trans x y z)
      (λ   {x} {y} → <-≤-weaken x y)
      public

    open <-syntax public
    open ≤-syntax public
    open ≡-syntax public

    _<+[_] : ∀ {x y} → x < y → ∀ z → x + z < y + z
    _<+[_] x<y z = +MonoR< _ _ z x<y

    [_]+<_ : ∀ {x y} z → x < y → z + x < z + y
    [_]+<_ z = subst2 _<_ (+Comm _ z) (+Comm _ z) ∘ +MonoR< _ _ z

    _≤+[_] : ∀ {x y} → x ≤ y → ∀ z → x + z ≤ y + z
    _≤+[_] x≤y z = +MonoR≤ _ _ z x≤y

    [_]+≤_ : ∀ {x y} z → x ≤ y → z + x ≤ z + y
    [_]+≤_ z = subst2 _≤_ (+Comm _ z) (+Comm _ z) ∘ +MonoR≤ _ _ z

    _<·[_,_] : ∀ {x y} → x < y → ∀ z → 0r < z → x · z < y · z
    _<·[_,_] x<y z 0<z = ·MonoR< _ _ z 0<z x<y

    [_,_]·<_ : ∀ {x y} z → 0r < z → x < y → z · x < z · y
    [_,_]·<_ z = (subst2 _<_ (·Comm _ z) (·Comm _ z) ∘_) ∘ ·MonoR< _ _ z

    _≤·[_,_] : ∀ {x y} → x ≤ y → ∀ z → 0r ≤ z → x · z ≤ y · z
    _≤·[_,_] x≤y z 0≤z = ·MonoR≤ _ _ z 0≤z x≤y

    [_,_]·≤_ : ∀ {x y} z → 0r ≤ z → x ≤ y → z · x ≤ z · y
    [_,_]·≤_ z = (subst2 _≤_ (·Comm _ z) (·Comm _ z) ∘_) ∘ ·MonoR≤ _ _ z

    private
      example : ∀ a b c d e f g
              → (0r < f) → a < (b + c) → b ≤ d → (d + c) < (e · f) → e < g
              → a < (g · f)
      example a b c d e f g 0<f a<b+c b≤d d+c<e·f e<g = begin<
        a     <⟨ a<b+c ⟩
        b + c ≤⟨ b≤d ≤+[ c ] ⟩
        d + c <⟨ d+c<e·f ⟩
        e · f <⟨ e<g <·[ f , 0<f ] ⟩
        g · f ◾

  open OrderedCommRingReasoning

  module OrderedCommRingTheory where
    open ApartnessStr (str (OrderedCommRing→Apartness R')) using (_#_) public
    open PseudolatticeTheory (OrderedCommRing→PseudoLattice R') public using () renaming (
        L≤∨ to L≤⊔ ; R≤∨ to R≤⊔ ; ∨Comm to ⊔Comm ; ∨Idem to ⊔Idem ; ∨LUB to ⊔LUB
      ; ∧≤L to ⊓≤L ; ∧≤R to ⊓≤R ; ∧Comm to ⊓Comm ; ∧Idem to ⊓Idem ; ∧GLB to ⊓GLB)

    0≤1 : 0r ≤ 1r
    0≤1 = <-≤-weaken 0r 1r 0<1

    ≤→¬> : ∀ x y → x ≤ y → ¬ (y < x)
    ≤→¬> x y = equivFun (≤≃¬> x y)

    ¬<→≥ : ∀ x y → ¬ (x < y) → y ≤ x
    ¬<→≥ x y = invEq (≤≃¬> y x)

    +MonoL< : ∀ x y z → x < y → z + x < z + y
    +MonoL< x y z = subst2 _<_ (+Comm _ _) (+Comm _ _) ∘ +MonoR< x y z

    +Mono< : ∀ x y z w → x < y → z < w → x + z < y + w
    +Mono< x y z w x<y z<w = is-trans< _ _ _ (+MonoR< _ _ _ x<y) (+MonoL< _ _ _ z<w)

    +MonoL≤ : ∀ x y z → x ≤ y → z + x ≤ z + y
    +MonoL≤ x y z = subst2 _≤_ (+Comm _ _) (+Comm _ _) ∘ +MonoR≤ x y z

    +Mono≤ : ∀ x y z w → x ≤ y → z ≤ w → x + z ≤ y + w
    +Mono≤ x y z w x≤y z≤w = is-trans≤ _ _ _ (+MonoR≤ _ _ _ x≤y) (+MonoL≤ _ _ _ z≤w)

    ·MonoL< : ∀ x y z → 0r < z → x < y → z · x < z · y
    ·MonoL< x y z = (subst2 _<_ (·Comm _ _) (·Comm _ _) ∘_) ∘ ·MonoR< _ _ _

    ·MonoL≤ : ∀ x y z → 0r ≤ z → x ≤ y → z · x ≤ z · y
    ·MonoL≤ x y z = (subst2 _≤_ (·Comm _ _) (·Comm _ _) ∘_) ∘ ·MonoR≤ _ _ _

    ·CancelL≤ : ∀ x y z → 0r < z → z · x ≤ z · y → x ≤ y
    ·CancelL≤ x y z 0<z zx≤zy = ¬<→≥ y x $ ≤→¬> _ _ zx≤zy ∘ ·MonoL< _ _ z 0<z

    ·CancelR≤ : ∀ x y z → 0r < z → x · z ≤ y · z → x ≤ y
    ·CancelR≤ x y z 0<z zx≤zy = ¬<→≥ y x $ ≤→¬> _ _ zx≤zy ∘ ·MonoR< _ _ z 0<z

    -- It is not clear if the properties commented below are constructively derivable.
    --
    -- ·CancelL< : ∀ x y z → 0r < z → z · x < z · y → x < y
    -- ·CancelL< = ?
    --
    -- ·CancelR< : ∀ x y z → 0r < z → x · z < y · z → x < y
    -- ·CancelR< = ?

    -- Howeverer, we can prove their double negations, so they are classically valid
    ¬¬·CancelL< : ∀ x y z → 0r < z → z · x < z · y → ¬ ¬ (x < y)
    ¬¬·CancelL< x y z 0<z zx<zy ¬x<y =
      ≤→¬> _ _ (·MonoL≤ _ _ z (<-≤-weaken 0r z 0<z) (¬<→≥ _ _ ¬x<y)) zx<zy

    ¬¬·CancelR< : ∀ x y z → 0r < z → x · z < y · z → ¬ ¬ (x < y)
    ¬¬·CancelR< x y z 0<z xz<yz ¬x<y =
      ≤→¬> _ _ (·MonoR≤ _ _ z (<-≤-weaken 0r z 0<z) (¬<→≥ _ _ ¬x<y)) xz<yz

    ≥Using< : ∀ x y → (x < y → y ≤ x) → y ≤ x
    ≥Using< x y <→≥ = ¬<→≥ x y (∘diag (≤→¬> y x ∘ <→≥))

    abs ∣_∣ : R → R
    abs z = z ⊔ (- z)
    ∣_∣ = abs

    <SumLeftPos : ∀ x y → 0r < y → x < x + y
    <SumLeftPos x y = subst (_< x + y) (+IdR x) ∘ +MonoL< 0r y x

    <SumRightPos : ∀ x y → 0r < y → x < y + x
    <SumRightPos x y = subst (_< y + x) (+IdL x) ∘ +MonoR< 0r y x

    ≤SumLeftNonNeg : ∀ x y → 0r ≤ y → x ≤ x + y
    ≤SumLeftNonNeg x y = subst (_≤ x + y) (+IdR x) ∘ +MonoL≤ 0r y x

    ≤SumRightNonNeg : ∀ x y → 0r ≤ y → x ≤ y + x
    ≤SumRightNonNeg x y = subst (_≤ y + x) (+IdL x) ∘ +MonoR≤ 0r y x

    -Flip< : ∀ x y → x < y → - y < - x
    -Flip< x y x<y = begin<
      - y           ≡→≤⟨ solve! RCR ⟩
      x + (- x - y)   <⟨ x<y <+[ - x - y ] ⟩
      y + (- x - y) ≡→≤⟨ solve! RCR ⟩
      - x             ◾

    -Flip≤ : ∀ x y → x ≤ y → - y ≤ - x
    -Flip≤ x y x≤y = begin≤
      - y           ≡→≤⟨ solve! RCR ⟩
      x + (- x - y)   ≤⟨ x≤y ≤+[ - x - y ] ⟩
      y + (- x - y) ≡→≤⟨ solve! RCR ⟩
      - x             ◾

    0<→-<0 : ∀ x → 0r < x → - x < 0r
    0<→-<0 x = subst (- x <_) 0Selfinverse ∘ -Flip< 0r x

    <0→0<- : ∀ x → x < 0r → 0r < - x
    <0→0<- x = subst (_< - x) 0Selfinverse ∘ -Flip< x 0r

    0≤→-≤0 : ∀ x → 0r ≤ x → - x ≤ 0r
    0≤→-≤0 x = subst (- x ≤_) 0Selfinverse ∘ -Flip≤ 0r x

    ≤0→0≤- : ∀ x → x ≤ 0r → 0r ≤ - x
    ≤0→0≤- x = subst (_≤ - x) 0Selfinverse ∘ -Flip≤ x 0r

    <→0<Δ : ∀ x y → x < y → 0r < y - x
    <→0<Δ x y = subst (_< (y - x)) (+InvR x) ∘ +MonoR< x y (- x)

    ≤→0≤Δ : ∀ x y → x ≤ y → 0r ≤ y - x
    ≤→0≤Δ x y = subst (_≤ (y - x)) (+InvR x) ∘ +MonoR≤ x y (- x)

    0<Δ→< : ∀ x y → 0r < y - x → x < y
    0<Δ→< x y = subst2 _<_ (+IdL x) (solve! RCR) ∘ +MonoR< 0r (y - x) x

    0≤Δ→≤ : ∀ x y → 0r ≤ y - x → x ≤ y
    0≤Δ→≤ x y = subst2 _≤_ (+IdL x) (solve! RCR) ∘ +MonoR≤ 0r (y - x) x

    0≤² : ∀ x → 0r ≤ x · x
    0≤² x = ≥Using< (x · x) 0r λ x²<0 →
      let
        0≤x : 0r ≤ x
        0≤x = ¬<→≥ x 0r λ x<0 → is-irrefl 0r $ begin<
          0r             ≡→≤⟨ sym $ 0LeftAnnihilates (- x) ⟩
          0r · (- x)       <⟨ ∘diag (·MonoR< _ _ _) (<0→0<- x x<0) ⟩
          (- x) · (- x)  ≡→≤⟨ solve! RCR ⟩
          x · x            <⟨ x²<0 ⟩
          0r               ◾
      in
        subst (_≤ x · x) (0LeftAnnihilates x) (∘diag (·MonoR≤ _ _ _) 0≤x)

    #→0<² : ∀ x → x # 0r → 0r < x · x
    #→0<² x (inl x<0) =
      subst2 _<_ (0LeftAnnihilates _) (solve! RCR) (∘diag (·MonoR< _ _ _) (<0→0<- x x<0))
    #→0<² x (inr 0<x) =
      subst (_< x · x) (0LeftAnnihilates _) (∘diag (·MonoR< _ _ _) 0<x)

    ≤abs : ∀ z → z ≤ abs z
    ≤abs z = L≤⊔

    -≤abs : ∀ z → - z ≤ abs z
    -≤abs z = R≤⊔

    0≤abs : ∀ z → 0r ≤ abs z
    0≤abs z = ¬<→≥ (abs z) 0r λ ∣z∣<0 → is-irrefl 0r $ begin<
      0r      ≡→≤⟨ sym 0Selfinverse ⟩
      - 0r      <⟨ -Flip< _ _ ∣z∣<0 ⟩
      - abs z   ≤⟨ -Flip≤ _ _ (≤abs z) ⟩
      - z       ≤⟨ -≤abs z ⟩
      abs z     <⟨ ∣z∣<0 ⟩
      0r        ◾

    abs≤0→≡0 : ∀ z → abs z ≤ 0r → z ≡ 0r
    abs≤0→≡0 z ∣z∣≤0 = is-antisym z 0r
      (begin≤
        z     ≤⟨ ≤abs z ⟩
        abs z ≤⟨ ∣z∣≤0 ⟩
        0r         ◾)
      (begin≤
        0r        ≡→≤⟨ sym 0Selfinverse ⟩
        - 0r        ≤⟨ -Flip≤ _ _ ∣z∣≤0 ⟩
        - (abs z)   ≤⟨ -Flip≤ _ _ $ -≤abs z ⟩
        - - z     ≡→≤⟨ -Idempotent z ⟩
        z           ◾)

    #→0<abs : ∀ z → z # 0r → 0r < abs z
    #→0<abs z (inl z<0) = begin<
      0r    ≡→≤⟨ sym 0Selfinverse ⟩
      - 0r    <⟨ -Flip< z 0r z<0 ⟩
      - z     ≤⟨ -≤abs _ ⟩
      abs z   ◾
    #→0<abs z (inr 0<z) = begin<
      0r    <⟨ 0<z ⟩
      z     ≤⟨ ≤abs _ ⟩
      abs z ◾

    abs- : ∀ x → abs (- x) ≡ abs x
    abs- x = cong ((- x) ⊔_) (-Idempotent x) ∙ ⊔Comm

    0≤→abs≡id : ∀ x → 0r ≤ x → abs x ≡ x
    0≤→abs≡id x 0≤x = is-antisym (abs x) x
      (⊔LUB (is-refl x) (begin≤ - x ≤⟨ 0≤→-≤0 x 0≤x ⟩ 0r ≤⟨ 0≤x ⟩ x ◾))
      (≤abs x)

    ≤0→abs≡- : ∀ x → x ≤ 0r → abs x ≡ - x
    ≤0→abs≡- x x≤0 = sym (abs- x) ∙ 0≤→abs≡id (- x) (≤0→0≤- x x≤0)

    0<→abs≡id : ∀ x → 0r < x → abs x ≡ x
    0<→abs≡id x = 0≤→abs≡id x ∘ <-≤-weaken 0r x

    <0→abs≡- : ∀ x → x < 0r → abs x ≡ - x
    <0→abs≡- x = ≤0→abs≡- x ∘ <-≤-weaken x 0r

    ²∘abs≡² : ∀ x → abs x · abs x ≡ x · x
    ²∘abs≡² x = is-antisym (abs x · abs x) (x · x)
      (¬<→≥ (x · x) (abs x · abs x) λ x²<∣x∣² →
        let
          0≤x : 0r ≤ x
          0≤x = ¬<→≥ x 0r λ x<0 → is-irrefl (x · x) (begin<
            x · x           <⟨ x²<∣x∣² ⟩
            abs x · abs x ≡→≤⟨ cong (∘diag _·_) (<0→abs≡- x x<0) ∙ solve! RCR ⟩
            x · x           ◾)
        in
          is-irrefl (x · x) (begin<
            x · x           <⟨ x²<∣x∣² ⟩
            abs x · abs x ≡→≤⟨ cong (∘diag _·_) (0≤→abs≡id x 0≤x) ⟩
            x · x           ◾))
      (0≤Δ→≤ (x · x) (abs x · abs x) (begin≤
        0r                          ≡→≤⟨ sym $ 0LeftAnnihilates (abs x - - x) ⟩
        0r · (abs x - - x)            ≤⟨ ≤→0≤Δ _ _ (≤abs x) ≤·[ _ , ≤→0≤Δ _ _ (-≤abs x) ] ⟩
        (abs x - x) · (abs x - - x) ≡→≤⟨ solve! RCR ⟩
        abs x · abs x - x · x         ◾))

    abs∘²≡² : ∀ x → abs(x · x) ≡ x · x
    abs∘²≡² x = 0≤→abs≡id (x · x) (0≤² x)

    triangularInequality ▵≤ : ∀ x y → abs (x + y) ≤ abs x + abs y
    triangularInequality x y = ⊔LUB
      (begin≤
        x     + y     ≤⟨ +Mono≤ _ _ _ _ (≤abs x) (≤abs y) ⟩
        abs x + abs y ◾)
      (begin≤
        - (x + y)    ≡→≤⟨ solve! RCR ⟩
        (- x) - y      ≤⟨ +Mono≤ _ _ _ _ (-≤abs x) (-≤abs y) ⟩
        abs x + abs y ◾)

    ▵≤ = triangularInequality

    triangularInequality- ▵≤- : ∀ x y z → abs (x - y) ≤ abs (x - z) + abs (z - y)
    triangularInequality- x y z = begin≤
      abs (x - y)               ≡→≤⟨ cong abs (solve! RCR) ⟩
      abs ((x - z) + (z - y))     ≤⟨ triangularInequality (x - z) (z - y) ⟩
      abs (x - z) + abs (z - y)   ◾

    ▵≤- = triangularInequality-

    abs-Comm : ∀ x y → abs (x - y) ≡ abs (y - x)
    abs-Comm x y =
      abs (x - y)             ≡⟨⟩
      (x - y) ⊔ (- (x - y))   ≡⟨ ⊔Comm ⟩
      (- (x - y)) ⊔ (x - y)   ≡⟨ cong₂ _⊔_ (solve! RCR) (solve! RCR) ⟩
      (y - x) ⊔ (- (y - x))   ≡⟨⟩
      abs (y - x)             ∎

    abs0 : abs 0r ≡ 0r
    abs0 = 0≤→abs≡id 0r (is-refl 0r)

    abs1 : abs 1r ≡ 1r
    abs1 = 0≤→abs≡id 1r 0≤1

  open OrderedCommRingTheory

  module AdditiveSubType
    (P : R → Type ℓ'')
    (P-prop : ∀ x → isProp (P x))
    (+Closed : (x y : R) → P x → P y → P (x + y))
    where

    subtype : Type (ℓ-max ℓ ℓ'')
    subtype = Σ[ x ∈ R ] P x

    isSetSubtype : isSet subtype
    isSetSubtype = isSetΣSndProp is-set P-prop

    ι : subtype → R
    ι = fst

    subtype≡ : ∀ {x y} → ι x ≡ ι y → x ≡ y
    subtype≡ = Σ≡Prop P-prop

    _+subtype_ : subtype → subtype → subtype
    (x +subtype y) .fst = fst x + fst y
    (x +subtype y) .snd = +Closed (fst x) (fst y) (snd x) (snd y)

    _-subtype_ : subtype → subtype → R
    _-subtype_ x y = ι x - ι y

    _<subtype_ : subtype → subtype → Type ℓ'
    _<subtype_ x y = ι x < ι y

    _≤subtype_ : subtype → subtype → Type ℓ'
    _≤subtype_ x y = ι x ≤ ι y

    infixl 6 _+subtype_ _-subtype_
    infix  4 _<subtype_ _≤subtype_

  module AdditiveAndMultiplicativeSubType
    (P : R → Type ℓ'')
    (P-prop : ∀ x → isProp (P x))
    (+Closed : (x y : R) → P x → P y → P (x + y))
    (·Closed : (x y : R) → P x → P y → P (x · y))
    where
    open AdditiveSubType P P-prop +Closed public

    _·subtype_ : subtype → subtype → subtype
    (x ·subtype y) .fst = fst x · fst y
    (x ·subtype y) .snd = ·Closed (fst x) (fst y) (snd x) (snd y)

    infixl 7 _·subtype_

  -- 0<+Closed and 0<·Closed are derivable, but for concrete instances
  -- (like the rationals) it's more efficient to use alternative proofs
  module Positive
    (0<+Closed : (x y : R) → 0r < x → 0r < y → 0r < x + y)
    (0<·Closed : (x y : R) → 0r < x → 0r < y → 0r < x · y)
    where
    open AdditiveAndMultiplicativeSubType
      (0r <_) (is-prop-valued< 0r) 0<+Closed 0<·Closed public renaming (
        subtype to R₊ ; isSetSubtype to isSetR₊ ; ι to ⟨_⟩₊ ; subtype≡ to R₊≡
      ; _+subtype_ to _+₊_ ; _·subtype_ to _·₊_ ; _-subtype_ to _-₊_
      ; _≤subtype_ to _≤₊_ ; _<subtype_ to _<₊_)

    R₊AdditiveSemigroup : Semigroup _
    fst R₊AdditiveSemigroup = R₊
    SemigroupStr._·_ (snd R₊AdditiveSemigroup) = _+₊_
    SemigroupStr.isSemigroup (snd R₊AdditiveSemigroup) = isSG
      where
        isSG : IsSemigroup _
        isSG .IsSemigroup.is-set = isSetR₊
        isSG .IsSemigroup.·Assoc = λ _ _ _ → R₊≡ (+Assoc _ _ _)

    open SemigroupStr (snd R₊AdditiveSemigroup) using () public renaming (
      ·Assoc to +₊Assoc)

    R₊MultiplicativeCommMonoid : CommMonoid _
    fst R₊MultiplicativeCommMonoid = R₊
    CommMonoidStr.ε   (snd R₊MultiplicativeCommMonoid) = 1r , 0<1
    CommMonoidStr._·_ (snd R₊MultiplicativeCommMonoid) = _·₊_
    CommMonoidStr.isCommMonoid (snd R₊MultiplicativeCommMonoid) =
      makeIsCommMonoid
        isSetR₊
        (λ _ _ _ → R₊≡ (·Assoc _ _ _))
        (λ _     → R₊≡ (·IdR _))
        (λ _ _   → R₊≡ (·Comm _ _))

    open CommMonoidStr (snd R₊MultiplicativeCommMonoid) using () public renaming (
      ε to 1₊ ; ·Assoc to ·₊Assoc ; ·IdR to ·₊IdR ; ·Comm to ·₊Comm)

    selfSeparated : ∀ (x y : R) → (∀ (z : R₊) → abs(x - y) < ⟨ z ⟩₊) → x ≡ y
    selfSeparated x y ∀[•]∣x-y∣<• =
      let
        ∣x-y∣≤0 : abs(x - y) ≤ 0r
        ∣x-y∣≤0 = ¬<→≥ 0r (abs(x - y)) λ 0<∣x-y∣ → is-irrefl (abs(x - y)) $ begin<
          abs(x - y) <⟨ ∀[•]∣x-y∣<• (abs(x - y) , 0<∣x-y∣) ⟩
          abs(x - y) ◾

        x-y≡0 : x - y ≡ 0r
        x-y≡0 = abs≤0→≡0 (x - y) ∣x-y∣≤0
      in
        equalByDifference x y x-y≡0

    _⊔₊_ : R₊ → R₊ → R₊
    (x ⊔₊ y) .fst = ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊
    (x ⊔₊ y) .snd = begin< 0r <⟨ snd x ⟩ ⟨ x ⟩₊ ≤⟨ L≤⊔ ⟩ ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊ ◾

    plusMinus₊ : ∀ x y → (x +₊ y) -₊ y ≡ ⟨ x ⟩₊
    plusMinus₊ (x , _) (y , _) = solve! RCR

    minusPlus₊ : ∀ x y → x -₊ y + ⟨ y ⟩₊ ≡ ⟨ x ⟩₊
    minusPlus₊ (x , _) (y , _) = solve! RCR

    ≡₊→0< : ∀ {x} y → x ≡ ⟨ y ⟩₊ → 0r < x
    ≡₊→0< y p = subst (0r <_) (sym p) (snd y)

    ≡₊→R₊ : ∀ {x} y → x ≡ ⟨ y ⟩₊ → R₊
    ≡₊→R₊ y p .fst = _
    ≡₊→R₊ y p .snd = ≡₊→0< y p

    infixl 6 -₊<
    -₊< : ∀ x y → y <₊ x → R₊
    -₊< x y y<x .fst = x -₊ y
    -₊< x y y<x .snd = <→0<Δ ⟨ y ⟩₊ ⟨ x ⟩₊ y<x

    syntax -₊< x y y<x = x -₊[ y<x ] y

    [_-₊_]⟨_⟩ : ∀ x y → y <₊ x → R₊
    [_-₊_]⟨_⟩ = -₊<

    <₊SumLeft : ∀ x y → x <₊ x +₊ y
    <₊SumLeft (x , _) (y , 0<y) = begin<
      x ≡→≤⟨ sym $ +IdR x ⟩ x + 0r <⟨ [ x ]+< 0<y ⟩ x + y ◾

    <₊SumRight : ∀ x y → x <₊ y +₊ x
    <₊SumRight (x , _) (y , 0<y) = begin<
      x ≡→≤⟨ sym $ +IdL x ⟩ 0r + x <⟨ 0<y <+[ x ] ⟩ y + x ◾

    Δ<₊ : ∀ x y → x -₊ y < ⟨ x ⟩₊
    Δ<₊ (x , _) (y , 0<y) = begin<
      x - y <⟨ [ x ]+< -Flip< 0r y 0<y ⟩ x - 0r ≡→≤⟨ solve! RCR ⟩ x ◾

  -- 0≤+Closed and 0≤·Closed are derivable, but for concrete instances
  -- (like the rationals) it's more efficient to use alternative proofs
  module NonNegative
    (0≤+Closed : (x y : R) → 0r ≤ x → 0r ≤ y → 0r ≤ x + y)
    (0≤·Closed : (x y : R) → 0r ≤ x → 0r ≤ y → 0r ≤ x · y)
    where
    open AdditiveAndMultiplicativeSubType
      (0r ≤_) (is-prop-valued≤ 0r) 0≤+Closed 0≤·Closed public renaming (
        subtype to R₀₊ ; isSetSubtype to isSetR₀₊ ; ι to ⟨_⟩₀₊ ; subtype≡ to R₀₊≡
      ; _+subtype_ to _+₀₊_ ; _·subtype_ to _·₀₊_ ; _-subtype_ to _-₀₊_
      ; _≤subtype_ to _≤₀₊_ ; _<subtype_ to _<₀₊_)

    R₀₊CommSemiring : CommSemiring _
    fst R₀₊CommSemiring = R₀₊
    CommSemiringStr.0r  (snd R₀₊CommSemiring) = 0r , is-refl _
    CommSemiringStr.1r  (snd R₀₊CommSemiring) = 1r , 0≤1
    CommSemiringStr._+_ (snd R₀₊CommSemiring) = _+₀₊_
    CommSemiringStr._·_ (snd R₀₊CommSemiring) = _·₀₊_
    CommSemiringStr.isCommSemiring (snd R₀₊CommSemiring) =
      makeIsCommSemiring
        isSetR₀₊
        (λ _ _ _ → R₀₊≡ (+Assoc _ _ _))
        (λ _     → R₀₊≡ (+IdR _))
        (λ _ _   → R₀₊≡ (+Comm _ _))
        (λ _ _ _ → R₀₊≡ (·Assoc _ _ _))
        (λ _     → R₀₊≡ (·IdR _))
        (λ _ _ _ → R₀₊≡ (·DistR+ _ _ _))
        (λ _     → R₀₊≡ (0LeftAnnihilates _))
        (λ _ _   → R₀₊≡ (·Comm _ _))

    open CommSemiringStr (snd R₀₊CommSemiring) using () public renaming (
        0r to 0₀₊ ; 1r to 1₀₊
      ; +Assoc to +₀₊Assoc ; +IdL to +₀₊IdL ; +IdR to +₀₊IdR ; +Comm to +₀₊Comm
      ; ·Assoc to ·₀₊Assoc ; ·IdL to ·₀₊IdL ; ·IdR to ·₀₊IdR ; ·Comm to ·₀₊Comm
      ; ·DistL+ to ·₀₊DistL+₀₊ ; ·DistR+ to ·₀₊DistR+₀₊
      ; AnnihilL to AnnihilL₀₊ ; AnnihilR to AnnihilR₀₊)

    _⊔₀₊_ : R₀₊ → R₀₊ → R₀₊
    (x ⊔₀₊ y) .fst = ⟨ x ⟩₀₊ ⊔ ⟨ y ⟩₀₊
    (x ⊔₀₊ y) .snd = begin≤ 0r ≤⟨ snd x ⟩ ⟨ x ⟩₀₊ ≤⟨ L≤⊔ ⟩ ⟨ x ⟩₀₊ ⊔ ⟨ y ⟩₀₊ ◾

    _⊓₀₊_ : R₀₊ → R₀₊ → R₀₊
    (x ⊓₀₊ y) .fst = ⟨ x ⟩₀₊ ⊓ ⟨ y ⟩₀₊
    (x ⊓₀₊ y) .snd = ⊓GLB (snd x) (snd y)

    plusMinus₀₊ : ∀ x y → (x +₀₊ y) -₀₊ y ≡ ⟨ x ⟩₀₊
    plusMinus₀₊ (x , _) (y , _) = solve! RCR

    minusPlus₀₊ : ∀ x y → x -₀₊ y + ⟨ y ⟩₀₊ ≡ ⟨ x ⟩₀₊
    minusPlus₀₊ (x , _) (y , _) = solve! RCR

    ≡₀₊→0≤ : ∀ {x} y → x ≡ ⟨ y ⟩₀₊ → 0r ≤ x
    ≡₀₊→0≤ y p = subst (0r ≤_) (sym p) (snd y)

    ≡₀₊→R₀₊ : ∀ {x} y → x ≡ ⟨ y ⟩₀₊ → R₀₊
    ≡₀₊→R₀₊ y p .fst = _
    ≡₀₊→R₀₊ y p .snd = ≡₀₊→0≤ y p

    infixl 6 -₀₊≤
    -₀₊≤ : ∀ x y → y ≤₀₊ x → R₀₊
    -₀₊≤ x y y≤x .fst = x -₀₊ y
    -₀₊≤ x y y≤x .snd = ≤→0≤Δ ⟨ y ⟩₀₊ ⟨ x ⟩₀₊ y≤x

    syntax -₀₊≤ x y y≤x = x -₀₊[ y≤x ] y

    [_-₀₊_]⟨_⟩ : ∀ x y → y ≤₀₊ x → R₀₊
    [_-₀₊_]⟨_⟩ = -₀₊≤

    ≤₀₊SumLeft : ∀ x y → x ≤₀₊ x +₀₊ y
    ≤₀₊SumLeft (x , _) (y , 0≤y) = begin≤
      x ≡→≤⟨ sym $ +IdR x ⟩ x + 0r ≤⟨ [ x ]+≤ 0≤y ⟩ x + y ◾

    ≤₀₊SumRight : ∀ x y → x ≤₀₊ y +₀₊ x
    ≤₀₊SumRight (x , _) (y , 0≤y) = begin≤
      x ≡→≤⟨ sym $ +IdL x ⟩ 0r + x ≤⟨ 0≤y ≤+[ x ] ⟩ y + x ◾

    Δ≤₀₊ : ∀ x y → x -₀₊ y ≤ ⟨ x ⟩₀₊
    Δ≤₀₊ (x , _) (y , 0≤y) = begin≤
      x - y ≤⟨ [ x ]+≤ -Flip≤ 0r y 0≤y ⟩ x - 0r ≡→≤⟨ solve! RCR ⟩ x ◾

  private
    2r = 1r + 1r

  module 1/2∈R (1/2 : R) (1/2≡2⁻¹ : 1/2 · 2r ≡ 1r) where

    1/2+1/2≡1 : 1/2 + 1/2 ≡ 1r
    1/2+1/2≡1 =
      1/2 + 1/2 ≡⟨ solve! RCR ⟩
      1/2 · 2r  ≡⟨ 1/2≡2⁻¹ ⟩
      1r        ∎

    0<1/2 : 0r < 1/2
    0<1/2 = flip (PT.rec (is-prop-valued< 0r 1/2))
      (posSum→pos∨pos 1/2 1/2 (subst (0r <_) (sym 1/2+1/2≡1) 0<1)) λ
      { (inl 0<1/2) → 0<1/2
      ; (inr 0<1/2) → 0<1/2
      }

    0≤1/2 : 0r ≤ 1/2
    0≤1/2 = <-≤-weaken _ _ 0<1/2

    _/2 : R → R
    _/2 = _· 1/2

    _/4 : R → R
    _/4 = _/2 ∘ _/2

    mean : R → R → R
    mean x y = (x + y) · 1/2

    /2+/2≡mean : ∀ x y → x /2 + y /2 ≡ mean x y
    /2+/2≡mean x y = sym (·DistL+ x y 1/2)

    meanIdem : ∀ x → mean x x ≡ x
    meanIdem x =
      (x + x) · 1/2     ≡⟨ solve! RCR ⟩
      x · (1/2 + 1/2)   ≡⟨ cong (x ·_) 1/2+1/2≡1 ⟩
      x · 1r            ≡⟨ ·IdR x ⟩
      x                 ∎

    <→<mean : ∀ x y → x < y → x < mean x y
    <→<mean x y x<y = begin<
      x             ≡→≤⟨ sym (meanIdem x) ⟩
      (x + x) · 1/2   <⟨ ([ x ]+< x<y) <·[ 1/2 , 0<1/2 ] ⟩
      (x + y) · 1/2   ◾

    <→mean< : ∀ x y → x < y → mean x y < y
    <→mean< x y x<y = begin<
      (x + y) · 1/2   <⟨ (x<y <+[ y ]) <·[ 1/2 , 0<1/2 ] ⟩
      (y + y) · 1/2 ≡→≤⟨ meanIdem y ⟩
      y               ◾

    /2+/2≡id : ∀ x → x /2 + x /2 ≡ x
    /2+/2≡id x = /2+/2≡mean x x ∙ meanIdem x

    id-/2≡/2 : ∀ x → x - x /2 ≡ x /2
    id-/2≡/2 x = cong (_- x /2) (sym (/2+/2≡id x)) ∙ solve! RCR

    /4+/4≡/2 : ∀ x → x /4 + x /4 ≡ x /2
    /4+/4≡/2 = /2+/2≡id ∘ (_/2)

    /4+/4+/4+/4≡id : ∀ x → (x /4 + x /4) + (x /4 + x /4) ≡ x
    /4+/4+/4+/4≡id x = cong (∘diag _+_) (/4+/4≡/2 x) ∙ /2+/2≡id x

    /2-/4≡/4 : ∀ x → x /2 - x /4 ≡ x /4
    /2-/4≡/4 = id-/2≡/2 ∘ (_/2)

    id-[/4+/4]≡/2 : ∀ x → x - (x /4 + x /4) ≡ x /2
    id-[/4+/4]≡/2 x = cong (_-_ x) (/4+/4≡/2 x) ∙ id-/2≡/2 x

  module PositiveHalves
    (1/2 : R)
    (1/2≡2⁻¹ : 1/2 · 2r ≡ 1r)
    (0<+Closed : (x y : R) → 0r < x → 0r < y → 0r < x + y)
    (0<·Closed : (x y : R) → 0r < x → 0r < y → 0r < x · y)
    where

    open 1/2∈R 1/2 1/2≡2⁻¹
    open Positive 0<+Closed 0<·Closed

    _/2₊ : R₊ → R₊
    _/2₊ = _·₊ (1/2 , 0<1/2)

    _/4₊ : R₊ → R₊
    _/4₊ = _/2₊ ∘ _/2₊

    mean₊ : R₊ → R₊ → R₊
    mean₊ x y = (x +₊ y) /2₊

    /2₊<id : ∀ x → (x /2₊) <₊ x
    /2₊<id x = begin<
      ⟨ x /2₊ ⟩₊            <⟨ <₊SumLeft (x /2₊) (x /2₊) ⟩
      ⟨ x /2₊ +₊ x /2₊ ⟩₊ ≡→≤⟨ /2+/2≡id ⟨ x ⟩₊ ⟩
      ⟨ x ⟩₊                ◾

    /4₊</2₊ : ∀ x → (x /4₊) <₊ (x /2₊)
    /4₊</2₊ = /2₊<id ∘ _/2₊

    /4₊<id : ∀ x → (x /4₊) <₊ x
    /4₊<id x = begin<
      ⟨ x /4₊ ⟩₊ <⟨ /4₊</2₊ x ⟩
      ⟨ x /2₊ ⟩₊ <⟨ /2₊<id x ⟩
      ⟨ x ⟩₊     ◾

    id-/2₊ : ∀ x → 0r < x -₊ (x /2₊)
    id-/2₊ x = subst (0r <_) (sym (id-/2≡/2 ⟨ x ⟩₊)) (snd (x /2₊))

    id-[/4+/4]₊ : ∀ x → 0r < x -₊ (x /4₊ +₊ x /4₊)
    id-[/4+/4]₊ x = subst (0r <_) (cong (_-_ ⟨ x ⟩₊) (sym (/4+/4≡/2 ⟨ x ⟩₊))) (id-/2₊ x)
