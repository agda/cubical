{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.RPn.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

open import Cubical.Data.Prod hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.HITs.PropositionalTruncation as PropTrunc

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Bundle : (F : Type ℓ) (E : Type ℓ') (B : Type ℓ'') → Type _
-- Bundle F E B = Σ[ p ∈ (E → B) ] ∀ x → ∥ F ≃ fiber p x ∥

TypeEqvTo : (ℓ : Level) (X : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeEqvTo ℓ X = TypeWithStr ℓ (λ Y → ∥ Y ≃ X ∥)

PointedEqvTo : (ℓ : Level) (X : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
PointedEqvTo ℓ X = TypeWithStr ℓ (λ Y → Y × ∥ Y ≃ X ∥)

-- Bundle' : Type ℓ' → Type ℓ'' → (ℓ : Level) → Type (ℓ-max (ℓ-max ℓ' ℓ'') (ℓ-suc ℓ))
-- Bundle' F X ℓ = X → TypeEqvTo ℓ F

Total : ∀ {B : Type ℓ} {F : Type ℓ'} {ℓ''} → (B → TypeEqvTo ℓ'' F) → Type _
Total {B = B} {F} p⁻¹ = Σ[ x ∈ B ] typ (p⁻¹ x)

pr : ∀ {B : Type ℓ} {F : Type ℓ'} {ℓ''} (p⁻¹ : B → TypeEqvTo ℓ'' F) → Total p⁻¹ → B
pr p⁻¹ = fst

open import Cubical.Data.Bool
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels

2-EltType : (ℓ : Level) → Type (ℓ-suc ℓ)
2-EltType ℓ = TypeEqvTo ℓ Bool

2-EltType₀ = 2-EltType ℓ-zero

2-EltPointed : (ℓ : Level) → Type (ℓ-suc ℓ)
2-EltPointed ℓ = PointedEqvTo ℓ Bool

2-EltPointed₀ = 2-EltPointed ℓ-zero

open import Cubical.Foundations.SIP renaming (SNS₂ to SNS)
open import Cubical.Foundations.Pointed
open import Cubical.Structures.Pointed

2-EltPointed-structure : Type ℓ → Type ℓ
2-EltPointed-structure = add-to-structure pointed-structure (λ Y _ → ∥ Y ≃ Bool ∥)

2-EltPointed-iso : StrIso 2-EltPointed-structure ℓ''
2-EltPointed-iso = add-to-iso pointed-structure pointed-iso (λ Y _ → ∥ Y ≃ Bool ∥)

2-EltPointed-SNS : SNS {ℓ} 2-EltPointed-structure 2-EltPointed-iso
2-EltPointed-SNS = add-axioms-SNS pointed-structure pointed-iso (λ Y _ → ∥ Y ≃ Bool ∥)
                                  (λ _ _ → squash)
                                  pointed-is-SNS

2-EltPointed-SIP : (A B : 2-EltPointed ℓ) → A ≃[ 2-EltPointed-iso ] B ≃ (A ≡ B)
2-EltPointed-SIP = SIP 2-EltPointed-structure 2-EltPointed-iso (SNS₂→SNS₄ 2-EltPointed-SNS)

2-EltPointed-sip : (A B : 2-EltPointed ℓ) → A ≃[ 2-EltPointed-iso ] B → (A ≡ B)
2-EltPointed-sip A B = equivFun (2-EltPointed-SIP A B)

pointed-SIP : (A B : Pointed ℓ) → A ≃[ pointed-iso ] B ≃ (A ≡ B)
pointed-SIP = SIP pointed-structure pointed-iso (SNS₂→SNS₄ pointed-is-SNS)

pointed-sip : (A B : Pointed ℓ) → A ≃[ pointed-iso ] B → (A ≡ B)
pointed-sip A B (e , p) i = ua e i , ua-gluePath e p i -- equivFun (pointed-SIP A B)

open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum

dichotomyBool : (x : Bool) → (x ≡ true) ⊎ (x ≡ false)
dichotomyBool true  = inl refl
dichotomyBool false = inr refl

_⊕_ : Bool → Bool → Bool
false ⊕ x = x
true  ⊕ x = not x

⊕-invol : ∀ x y → x ⊕ (x ⊕ y) ≡ y
⊕-invol false x = refl
⊕-invol true  x = notnot x

⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
⊕-comm false false = refl
⊕-comm false true  = refl
⊕-comm true  false = refl
⊕-comm true  true  = refl

not≢const : ∀ x → ¬ not x ≡ x
not≢const false = true≢false
not≢const true  = false≢true

open import Cubical.Foundations.Isomorphism

isEquiv-⊕ : ∀ x → isEquiv (x ⊕_)
isEquiv-⊕ x = isoToIsEquiv (iso _ (x ⊕_) (⊕-invol x) (⊕-invol x))

invEq≡→equivFun≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) {x y} → invEq e x ≡ y → equivFun e y ≡ x
invEq≡→equivFun≡ e {x} p = cong (equivFun e) (sym p) ∙ retEq e x

-- open import Cubical.Foundations.GroupoidLaws

-- wop : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) {x y} → (invEq e x ≡ y) ≃ (equivFun e y ≡ x)
-- wop e {x} {y} = isoToEquiv (iso (λ p → cong (equivFun e) (sym p) ∙ retEq e x)
--                                 (λ p → cong (invEq e) (sym p)    ∙ secEq e y)
--                                 (λ p → cong (_∙ retEq e x) {!!} ∙ {!!})
--                                 -- cong (equivFun e) (sym (cong (invEq e) (sym p) ∙ secEq e y)) ∙ retEq e x)
--                                 (λ p → {!!}))

isContr-BoolPointedIso : ∀ x → isContr ((Bool , false) ≃[ pointed-iso ] (Bool , x))
fst (isContr-BoolPointedIso x) = ((λ y → x ⊕ y) , isEquiv-⊕ x) , ⊕-comm x false
snd (isContr-BoolPointedIso x) (e , p)
  = ΣProp≡ (λ e → isSetBool (equivFun e false) x)
           (ΣProp≡ isPropIsEquiv (funExt λ { false → ⊕-comm x false ∙ sym p
                                           ; true  → ⊕-comm x true  ∙ sym q }))
  where q : e .fst true ≡ not x
        q with dichotomyBool (invEq e (not x))
        ... | inl q = invEq≡→equivFun≡ e q
        ... | inr q = ⊥.rec (not≢const x (sym (invEq≡→equivFun≡ e q) ∙ p))

-- compPointedIso : ∀ {ℓ} {A : Pointed ℓ} {B : Pointed ℓ} {C : Pointed ℓ}
--                    (f : A ≃[ pointed-iso ] B) (g : B ≃[ pointed-iso ] C) → A ≃[ pointed-iso ] C
-- compPointedIso (f , p) (g , q) = compEquiv f g , cong (g .fst) p ∙ q

                  -- (λ e →   compPointedIso (fst (isContr-BoolPointedIso (equivFun e x))) (invEquiv e , secEq e x)
                  --        , λ { (f , p) → {!snd (isContr-BoolPointedIso (equivFun e x))!} })

isContr-2-EltPointed-iso : (A∙ : 2-EltPointed₀)
                         → isContr ((Bool , false , ∣ idEquiv Bool ∣) ≃[ 2-EltPointed-iso ] A∙)
isContr-2-EltPointed-iso (A , x , ∣e∣)
  = PropTrunc.rec isPropIsContr
                  (λ e → J (λ A∙ _ → isContr ((Bool , false) ≃[ pointed-iso ] A∙))
                           (isContr-BoolPointedIso (e .fst x))
                           (sym (pointed-sip _ _ (e , refl))))
                  ∣e∣

isContr-2-EltPointed : isContr (2-EltPointed₀)
fst isContr-2-EltPointed = (Bool , false , ∣ idEquiv Bool ∣)
snd isContr-2-EltPointed A∙ = 2-EltPointed-sip _ A∙ (fst (isContr-2-EltPointed-iso A∙))

-- toPointed : 2-EltType₀ → 2-EltPointed₀
-- toPointed (A , ∣e∣) = PropTrunc.rec (isContr→isProp isContr-2-EltPointed)
--                                     (λ e → A , invEq e false , ∣e∣)
--                                     ∣e∣

-- inhab : (A : 2-EltType₀) → typ A
-- inhab A = {!!}

-- qwe : (A : 2-EltType₀) → Bool ≡ typ A
-- qwe (A , ∣e∣) i = typ (snd isContr-2-EltPointed {!!} i)

-- _⊕*_ : ∀ {A : 2-EltType₀} → typ A → typ A → Bool
-- _⊕*_ {A , ∣e∣} x y = pathToEquiv (λ i → typ (snd isContr-2-EltPointed (A , x , ∣e∣) (~ i))) .fst y

open import Cubical.Data.Sum

R : ∀ {ℓ} {X : Type ℓ} (F : X → 2-EltType₀) (x : X) (y : typ (F x)) → Bool ≃ typ (F x)
R F x y = fst (fst (isContr-2-EltPointed-iso (fst (F x) , y , snd (F x))))

-- Equivalence induction
EquivJ' : {A B : Type ℓ} (P : (B : Type ℓ) → (e : B ≃ A) → Type ℓ')
        → (r : P A (idEquiv A)) → (e : B ≃ A) → P B e
EquivJ' P r e = subst (λ x → P (x .fst) (x .snd)) (contrSinglEquiv e) r

-- this lemma is just ⊕-comm wrapped up in two elims which unfold the elims in isContr-2-EltPointed-iso
lemR : ∀ {ℓ} {X : Type ℓ} (F : X → 2-EltType₀) (x : X) (y z : typ (F x))
     → invEq (R F x y) z ≡ invEq (R F x z) y
lemR F x = PropTrunc.elim {P = λ ∣e∣ → (y z : typ (F x)) → invEq (fst (fst (isContr-2-EltPointed-iso (fst (F x) , y , ∣e∣)))) z
                                                         ≡ invEq (fst (fst (isContr-2-EltPointed-iso (fst (F x) , z , ∣e∣)))) y}
                          (λ _ → isPropPi (λ _ → isPropPi (λ _ → isSetBool _ _)))
                          (EquivJ' (λ A e → (y z : A) → invEq (fst (fst (J (λ A∙ _ → isContr ((Bool , false) ≃[ pointed-iso ] A∙))
                                                                           (isContr-BoolPointedIso (e .fst y)) (sym (pointed-sip (A , y) (Bool , e .fst y) (e , refl)))))) z
                                                      ≡ invEq (fst (fst (J (λ A∙ _ → isContr ((Bool , false) ≃[ pointed-iso ] A∙))
                                                                           (isContr-BoolPointedIso (e .fst z)) (sym (pointed-sip (A , z) (Bool , e .fst z) (e , refl)))))) y)
                                   (λ y z → ⊕-comm y z))
                          (snd (F x))

-- PropTrunc.rec isPropIsContr _ ∣e∣ ≡ PropTrunc.rec isPropIsContr _ ∣e∣

-- setA : (A : 2-EltType₀) → isSet (typ A)
-- setA A

-- mdec : (A : 2-EltType₀) → Discrete (typ A)
-- mdec (A , ∣e∣) = PropTrunc.elim {P = λ _ → Discrete A} (λ ∣e∣ → PropTrunc.elim (λ _ → isPropIsProp) (λ e → {!!}) ∣e∣) -- isPropPi (λ x → isPropPi (λ y → isPropDec {!!})))
--                                 {!!} ∣e∣

open import Cubical.Data.NatMinusOne
open import Cubical.HITs.Pushout
open import Cubical.Data.Unit

RP  : ℕ₋₁ → Type₀
cov⁻¹ : (n : ℕ₋₁) → RP n → 2-EltType₀

α : ∀ {n} (x : Total (cov⁻¹ n)) → typ (cov⁻¹ n (x .fst)) ≃ Bool
α {n} (x , y) = invEquiv (R (cov⁻¹ n) x y)

RP neg1 = ⊥
RP (ℕ→ℕ₋₁ n) = Pushout (pr (cov⁻¹ (-1+ n))) (λ _ → tt)
             -- Cone (pr (cov⁻¹ (-1+ n)) {- : Total (cov⁻¹ (-1+ n)) → RP (-1+ n) -})

cov⁻¹ neg1 x = Bool , ∣ idEquiv _ ∣
cov⁻¹ (ℕ→ℕ₋₁ n) (inl x) = cov⁻¹ (-1+ n) x
cov⁻¹ (ℕ→ℕ₋₁ n) (inr _) = Bool , ∣ idEquiv _ ∣
cov⁻¹ (ℕ→ℕ₋₁ n) (push (x,y) i) = ua (α (x,y)) i , isProp→PathP (λ i → squash {A = ua (α (x,y)) i ≃ _})
                                                               (str (cov⁻¹ (-1+ n) (fst (x,y))))
                                                               (∣ idEquiv Bool ∣)
                                                               i
  -- typ (eq i) , str (eq i) .snd
  -- where eq : (Bool , true , ∣ idEquiv Bool ∣) ≡ (typ (cov⁻¹ (-1+ n) x) , y , str (cov⁻¹ (-1+ n) x))
  --       eq = snd isContr-2-EltPointed _

-- module Wrong! (α-lem : ∀ {n} (x : RP n) (y : typ (cov⁻¹ n x)) → (α (x , y)) .fst ≡ const y) where

--   fact : ∀ n (x : RP n) (y : typ (cov⁻¹ n x)) → isEquiv (λ (_ : Bool) → y)
--   fact n x y = subst isEquiv (α-lem x y) (α (x , y) .snd)

--   contra : ⊥
--   contra = true≢false (retEq (_ , fact (ℕ→ℕ₋₁ 0) (inl tt) true) false)

open import Cubical.HITs.Susp
open import Cubical.HITs.Sn

open import Cubical.Data.Prod renaming (_×_ to _×'_ ; _×Σ_ to _×_)

open import Cubical.HITs.Pushout.Flattening

open import Cubical.HITs.Join

-- Susp≡Join

ΣUnit : ∀ {ℓ} (A : Unit → Type ℓ) → Σ Unit A ≃ A tt
ΣUnit A = isoToEquiv (iso (λ { (tt , x) → x }) (λ { x → (tt , x) }) (λ _ → refl) (λ _ → refl))

private
  e₁ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → A × B ≃ B ×' A
  e₁ A B = isoToEquiv (iso (λ { (x , y) → (y , x) }) (λ { (x , y) → (y , x) })
                           (λ { (x , y) → refl })    (λ { (x , y) → refl }))

  e₁' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A × B ≃ B × A
  e₁' = isoToEquiv (iso (λ { (x , y) → (y , x) }) (λ { (x , y) → (y , x) })
                        (λ _ → refl) (λ _ → refl))

  e₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
       → (Σ[ (a,b) ∈ Σ A B ] C (fst (a,b))) ≃ (Σ[ a ∈ A ] B a × C a)
  e₂ = isoToEquiv (iso (λ { ((x , y) , z) → (x , (y , z)) }) (λ { (x , (y , z)) → ((x , y) , z) })
                       (λ _ → refl) (λ _ → refl))

  e₃ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
       → (∀ a → B a ≃ C a) → Σ A B ≃ Σ A C
  e₃ h = isoToEquiv (iso (λ { (x , y)   → (x , equivFun (h x) y) })
                         (λ { (x , y)   → (x , invEq    (h x) y) })
                         (λ { (x , y) i → (x , retEq    (h x) y i) })
                         (λ { (x , y) i → (x , secEq    (h x) y i) }))

ui : ∀ {n} (x : RP n) → typ (cov⁻¹ n x) → typ (cov⁻¹ n x) → Bool
ui x y z = α (x , z) .fst y

isEquiv-ui : ∀ {n} (x : RP n) (y : typ (cov⁻¹ n x)) → isEquiv (ui x y)
isEquiv-ui {n} x y = subst isEquiv (funExt (λ z → lemR (cov⁻¹ n) x y z)) (α (x , y) .snd)

ee : ∀ {n} → (Σ[ x ∈ Total (cov⁻¹ n) ] typ (cov⁻¹ n (fst x))) ≃ (Total (cov⁻¹ n) × Bool)
ee = compEquiv (compEquiv e₂ (e₃ (λ x → compEquiv e₁' (e₃ (λ z → ui x z , isEquiv-ui x z))))) (invEquiv e₂)

-- joinBool≃Susp : ∀ {A : Type ℓ} → join A Bool ≃ Susp A
-- joinBool≃Susp = {!isoc!}

thm : ∀ n → Total (cov⁻¹ n) ≡ S n
thm neg1 = isoToPath (iso (λ { () }) (λ { () }) (λ { () }) (λ { () }))
thm (ℕ→ℕ₋₁ n) = Total (cov⁻¹ (ℕ→ℕ₋₁ n))                 ≡⟨ cong (Σ _) (funExt cov⁻¹≡E) ⟩
                 Σ (Pushout _ _) E                        ≡⟨ ua flatten ⟩
                 Pushout Σf Σg                            ≡⟨ spanEquivToPushoutPath nat ⟩
                 joinPushout (Total (cov⁻¹ (-1+ n))) Bool ≡⟨ joinPushout≡join _ _ ⟩
                 join (Total (cov⁻¹ (-1+ n))) Bool        ≡⟨ sym Susp≡joinBool ⟩
                 Susp (Total (cov⁻¹ (-1+ n)))             ≡⟨ cong Susp (thm (-1+ n)) ⟩
                 S (ℕ→ℕ₋₁ n)                              ∎
  where open FlatteningLemma (λ x → pr (cov⁻¹ (-1+ n)) x) (λ _ → tt)
                             (λ x → typ (cov⁻¹ (-1+ n) x)) (λ _ → Bool)
                             (λ (x,y) → α (x,y))
                             hiding (Σf ; Σg)

        cov⁻¹≡E : ∀ x → typ (cov⁻¹ (ℕ→ℕ₋₁ n) x) ≡ E x
        cov⁻¹≡E (inl x) = refl
        cov⁻¹≡E (inr x) = refl
        cov⁻¹≡E (push a i) = refl
        
        Σf : Σ[ x ∈ Total (cov⁻¹ (-1+ n)) ] typ (cov⁻¹ (-1+ n) (fst x))
           → Σ[ x ∈ RP (-1+ n) ] typ (cov⁻¹ (-1+ n) x)
        Σf (x , y) = (pr (cov⁻¹ (-1+ n)) x , y)
        Σg : Σ[ x ∈ Total (cov⁻¹ (-1+ n)) ] typ (cov⁻¹ (-1+ n) (fst x))
           → Unit × Bool
        Σg (x , y) = (tt , (α x) .fst y)

        span₁ span₂ : 3-span
        span₁ = record { f1 = Σf ; f3 = Σg }
        span₂ = record { A2 = (Total (cov⁻¹ (-1+ n)) ×' Bool) ; f1 = proj₁ ; f3 = proj₂ }

        nat : 3-span-equiv span₁ span₂
        nat = record { e0 = idEquiv _ ; e4 = ΣUnit _ ; e2 = compEquiv ee (pathToEquiv (sym A×B≡A×ΣB)) ;
                       H1 = λ x → transportRefl _ ; H3 = λ x → refl }

        

        -- e₂ : ∀ (x : RP (-1+ n)) (b : Bool) → (typ (cov⁻¹ (-1+ n) x)) ≃ (typ (cov⁻¹ (-1+ n) x))
        -- e₂ x b = isoToEquiv (iso (λ { y → α (x , y) .fst b }) {!!} {!!} {!!})

        -- eq : Pushout Σf Σg ≡ joinPushout Bool (Total (cov⁻¹ (-1+ n)))
        -- eq i = Pushout {A = ua (e₁ (Total (cov⁻¹ (-1+ n))) Bool) i }
        --                {B = ua (ΣUnit (λ _ → Bool)) i}
        --                {C = {!!}} -- Σ[ x ∈ RP (-1+ n) ] typ (cov⁻¹ (-1+ n) x)}
        --                (λ x → glue (λ { (i = i0) → tt , snd x
        --                               ; (i = i1) → proj₁ x })
        --                            (proj₁ (unglue (i ∨ ~ i) x)))
        --                (λ x → glue (λ { (i = i0) → {!!} -- fst (fst x) , α (fst x) .fst (snd x)
        --                               ; (i = i1) → proj₂ x })
        --                            (proj₂ (unglue (i ∨ ~ i) x)))
        --                -- want:   equivFun e₃ (fst (fst x) , α (fst x) .fst (snd x))
        --                --        ≡ fst (fst x) , snd (fst x)
