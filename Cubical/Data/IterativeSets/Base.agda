module Cubical.Data.IterativeSets.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Fibration
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.Fiberwise

-- TODO: remove ⊥*-elim, Data.Unit, Data.Bool Data.SumFin once the statements that need them have found their way to a better place
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sum renaming (rec to ⊎-rec)

open import Cubical.Data.IterativeMultisets.Base renaming (overline to overline-∞ ; tilde to tilde-V∞ ; toFib to toFib-∞)

private
  variable
    ℓ : Level

isIterativeSet : V∞ {ℓ} → Type (ℓ-suc ℓ)
isIterativeSet (sup-∞ A f) = (isEmbedding f) × ((a : A) → isIterativeSet (f a))

isPropIsIterativeSet : (x : V∞ {ℓ}) → isProp (isIterativeSet x)
isPropIsIterativeSet (sup-∞ A f) = isProp× isPropIsEmbedding helper
  where
    helper : isProp ((a : A) → isIterativeSet (f a))
    helper g h i x = isPropIsIterativeSet (f x) (g x) (h x) i

V⁰ : Type (ℓ-suc ℓ)
V⁰ = Σ[ x ∈ V∞ ] isIterativeSet x

private
  variable
    x y z : V⁰ {ℓ}

-- accessing the components

overline : V⁰ {ℓ} → Type ℓ
overline = overline-∞ ∘ fst

tilde-∞ : (x : V⁰ {ℓ}) → overline x → V∞ {ℓ}
tilde-∞ = tilde-V∞ ∘ fst

tilde : (x : V⁰ {ℓ}) → overline x → V⁰ {ℓ}
tilde (sup-∞ _ f , _) a .fst = f a
tilde (sup-∞ _ _ , isitset) a .snd = isitset .snd a

isEmbedding-tilde-∞ : (x : V⁰ {ℓ}) → isEmbedding (tilde-∞ x)
isEmbedding-tilde-∞ (sup-∞ _ _ , its) = its .fst

isEmbedding-tilde : (x : V⁰ {ℓ}) → isEmbedding (tilde x)
isEmbedding-tilde (sup-∞ _ _ , isitset) = isEmbeddingSndΣProp isPropIsIterativeSet _ (isitset .fst)

Embedding-tilde : (x : V⁰ {ℓ}) → overline x ↪ V⁰ {ℓ}
Embedding-tilde x .fst = tilde x
Embedding-tilde x .snd = isEmbedding-tilde x

V⁰↪V∞ : V⁰ {ℓ} ↪ V∞ {ℓ}
V⁰↪V∞ = EmbeddingΣProp isPropIsIterativeSet

≡V⁰-≃-≡V∞ : (x ≡ y) ≃ (x .fst ≡ y .fst)
≡V⁰-≃-≡V∞ .fst = cong fst
≡V⁰-≃-≡V∞ .snd = V⁰↪V∞ .snd _ _

_∈⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → Type (ℓ-suc ℓ)
x ∈⁰ y = fiber (tilde y) (x)

∈⁰-irrefl : ¬ x ∈⁰ x
∈⁰-irrefl {x = sup-∞ A f , _} (a , p) = ∈∞-irrefl {x = sup-∞ A f} (a , cong fst p)

Iso-V⁰-Emb : Iso (V⁰ {ℓ}) (Embedding (V⁰ {ℓ}) ℓ)
Iso-V⁰-Emb {ℓ} = compIso isom Σ-assoc-Iso
  where
    isom : Iso (V⁰ {ℓ}) (Σ[ F ∈ Fibration (V⁰ {ℓ}) ℓ ] isEmbedding (F .snd))
    isom .Iso.fun (sup-∞ A f , its) .fst .fst = overline (sup-∞ A f , its)
    isom .Iso.fun (sup-∞ A f , its) .fst .snd a .fst = f a
    isom .Iso.fun (sup-∞ A f , its) .fst .snd a .snd = its .snd a
    isom .Iso.fun (sup-∞ A f , its) .snd = isEmbeddingSndΣProp isPropIsIterativeSet _ (its .fst)
    isom .Iso.inv E .fst = sup-∞ (E .fst .fst) (compEmbedding V⁰↪V∞ (E .fst .snd , E .snd) .fst)
    isom .Iso.inv E .snd .fst = compEmbedding V⁰↪V∞ (E .fst .snd , E .snd) .snd
    isom .Iso.inv E .snd .snd a = E .fst .snd a .snd
    isom .Iso.sec E = Σ≡Prop (λ _ → isPropIsEmbedding) refl
    isom .Iso.ret (sup-∞ _ _ , _) = Σ≡Prop isPropIsIterativeSet refl

toEmb : V⁰ {ℓ} → Embedding (V⁰ {ℓ}) ℓ
toEmb = Iso-V⁰-Emb .Iso.fun

fromEmb : Embedding (V⁰ {ℓ}) ℓ → V⁰ {ℓ}
fromEmb = Iso-V⁰-Emb .Iso.inv

-- TODO: figure out why this one computes poorly
secEmb : section (toEmb {ℓ}) (fromEmb {ℓ})
secEmb = Iso-V⁰-Emb .Iso.sec

retEmb : retract (toEmb {ℓ}) (fromEmb {ℓ})
retEmb = Iso-V⁰-Emb .Iso.ret

V⁰≃Emb : V⁰ {ℓ} ≃ Embedding (V⁰ {ℓ}) ℓ
V⁰≃Emb = isoToEquiv Iso-V⁰-Emb

Emb≃V⁰ : Embedding (V⁰ {ℓ}) ℓ ≃ V⁰ {ℓ}
Emb≃V⁰ = isoToEquiv (invIso Iso-V⁰-Emb)

isSetV⁰ : isSet (V⁰ {ℓ})
isSetV⁰ = isOfHLevelRespectEquiv 2 Emb≃V⁰ isSetEmbedding

_≃V⁰_ : (x y : V⁰ {ℓ}) → Type (ℓ-suc ℓ)
x ≃V⁰ y = ((z : V⁰) → (z ∈⁰ x) → (z ∈⁰ y)) ×
          ((z : V⁰) → (z ∈⁰ y) → (z ∈⁰ x))

≃V⁰-≃-≡V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≃V⁰ y) ≃ (x ≡ y)
≃V⁰-≃-≡V⁰ {x = sup-∞ A f , itsx} {y = sup-∞ B g , itsy} =
    let
        x = sup-∞ A f , itsx
        y = sup-∞ B g , itsy
    in compEquiv (EmbeddingIP (toEmb x) (toEmb y)) (invEquiv (cong toEmb , iso→isEmbedding Iso-V⁰-Emb x y))

≡V⁰-≃-≃V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≡ y) ≃ (x ≃V⁰ y)
≡V⁰-≃-≃V⁰ {x = sup-∞ A f , itsx} {y = sup-∞ B g , itsy} =
    let
        x = sup-∞ A f , itsx
        y = sup-∞ B g , itsy
    in compEquiv (cong toEmb , iso→isEmbedding Iso-V⁰-Emb x y) (invEquiv (EmbeddingIP (toEmb x) (toEmb y)))

V⁰↪Fib : (V⁰ {ℓ}) ↪ Fibration (V⁰ {ℓ}) ℓ
V⁰↪Fib {ℓ} = compEmbedding Emb↪Fib (Iso→Embedding Iso-V⁰-Emb)
  where
    open EmbeddingIdentityPrinciple
    Emb↪Fib : Embedding (V⁰ {ℓ}) ℓ ↪ Fibration (V⁰ {ℓ}) ℓ
    Emb↪Fib .fst = toFibr
    Emb↪Fib .snd = isEmbeddingToFibr

toFib : (V⁰ {ℓ}) → Fibration (V⁰ {ℓ}) ℓ
toFib = V⁰↪Fib .fst
    
_≃V⁰'_ : (x y : V⁰ {ℓ}) → Type (ℓ-suc ℓ)
x ≃V⁰' y = (z : V⁰) → ((z ∈⁰ x) ≃ (z ∈⁰ y))

≃V⁰'-≃-≡V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≃V⁰' y) ≃ (x ≡ y)
≃V⁰'-≃-≡V⁰ {x = sup-∞ A f , itsx} {y = sup-∞ B g , itsy} =
    let
        x = sup-∞ A f , itsx
        y = sup-∞ B g , itsy
    in compEquiv (FibrationIP (toFib x) (toFib y)) (invEquiv (cong toFib , V⁰↪Fib .snd x y))

≡V⁰-≃-≃V⁰' : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≡ y) ≃ (x ≃V⁰' y)
≡V⁰-≃-≃V⁰' {x = sup-∞ A f , itsx} {y = sup-∞ B g , itsy} =
    let
        x = sup-∞ A f , itsx
        y = sup-∞ B g , itsy
    in compEquiv (cong toFib , V⁰↪Fib .snd x y) (invEquiv (FibrationIP (toFib x) (toFib y)))

isProp∈∞ : {z : V∞ {ℓ}} → isProp (z ∈∞ (x .fst))
isProp∈∞ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-tilde-∞ x) z

isProp∈⁰ : {x z : V⁰ {ℓ}} → isProp (z ∈⁰ x)
isProp∈⁰ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-tilde x) z

El⁰ : V⁰ {ℓ} → Type ℓ
El⁰ = overline

fromEmb' : (x : V⁰ {ℓ}) → (El⁰ x ↪ V⁰ {ℓ})
fromEmb' (sup-∞ A f , its) = toEmb (sup-∞ A f , its) .snd

isSetEl⁰ : (x : V⁰ {ℓ}) → isSet (El⁰ x)
isSetEl⁰ {ℓ} x = Embedding-into-isSet→isSet {A = El⁰ {ℓ} x} {B = V⁰ {ℓ}} (fromEmb' x) (isSetV⁰ {ℓ})

-- TODO move somewhere better
private
  ΣEq-const-fst-fiberwiseEq : {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : A → Type ℓB} {C : A → Type ℓC}
                                (E : Σ A B ≃ Σ A C)
                                → ((S : Σ A B) → E .fst S .fst ≡ S .fst)
                                → (a : A) → B a ≃ C a
  ΣEq-const-fst-fiberwiseEq {A = A} {B = B} {C = C} E p a = goal
    where
       fiberwise : (a : A) → B a → C a
       fiberwise a b = subst C (p (a , b)) (E .fst (a , b) .snd)

       total : Σ A B → Σ A C
       total S .fst = S .fst
       total S .snd = fiberwise (S .fst) (S .snd)

       EΣ≡total : (S : Σ A B) → Σ[ q ∈ E .fst S .fst ≡ total S .fst ] PathP (λ i → C (q i)) (E .fst S .snd) (total S .snd)
       EΣ≡total S .fst = p S
       EΣ≡total S .snd = subst-filler C (p S) (E .fst S .snd)

       E≡total : E .fst ≡ total
       E≡total = funExt (λ S → ΣPathP (EΣ≡total S))

       eqTotal : isEquiv total
       eqTotal = subst isEquiv E≡total (E .snd)

       goal : B a ≃ C a
       goal .fst = fiberwise a
       goal .snd = Cubical.Foundations.Equiv.Fiberwise.fiberEquiv B C fiberwise
                    eqTotal a

-- TODO: move this to some other place in the library
isEmbeddingFunctionFromIsPropToIsSet : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → isProp A → isSet B → isEmbedding f
isEmbeddingFunctionFromIsPropToIsSet f propA setB = injEmbedding setB λ {w} {x} _ → propA w x

isProp-∈⁰-Equiv : (x y : V⁰ {ℓ}) → isProp ((z : V⁰) → (z ∈⁰ x) ≃ (z ∈⁰ y))
isProp-∈⁰-Equiv x y = isPropΠ λ z → isOfHLevel≃ 1 (isProp∈⁰ {x = x} {z = z}) (isProp∈⁰ {x = y} {z = z})

∈⁰≃∈∞ : {x z : V⁰ {ℓ}} → (z ∈⁰ x) ≃ (z .fst ∈∞ x .fst)
∈⁰≃∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz} = propBiimpl→Equiv (isProp∈⁰ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz}) (isProp∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ}) f g
    where
        f : (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx) → sup-∞ z γ ∈∞ sup-∞ x α
        f (a , p) .fst = a
        f (a , p) .snd = cong fst p
        g : sup-∞ z γ ∈∞ sup-∞ x α → (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx)
        g (a , p) .fst = a
        g (a , p) .snd = Σ≡Prop isPropIsIterativeSet p

-- TODO move to better place
⊥*≢Unit* : ((⊥* {ℓ} :> Type ℓ) ≡ (Unit* {ℓ} :> Type ℓ)) → ⊥
⊥*≢Unit* p = ⊥*-elim {A = λ _ → ⊥} (transport (sym p) (lift tt))

Unit*≢⊥* : ((Unit* {ℓ} :> Type ℓ) ≡ (⊥* {ℓ} :> Type ℓ)) → ⊥
Unit*≢⊥* p = ⊥*-elim {A = λ _ → ⊥} (transport p (lift tt))

-- TODO: move to better place
≡-from-isOfHLevel→isOfHLevel : {ℓ : Level} {A B : Type ℓ} {n : HLevel} → A ≡ B → isOfHLevel n A → isOfHLevel n B
≡-from-isOfHLevel→isOfHLevel {n = n} A≡B = subst (isOfHLevel n) A≡B

≡-to-isOfHLevel→isOfHLevel : {ℓ : Level} {A B : Type ℓ} {n : HLevel} → A ≡ B → isOfHLevel n B → isOfHLevel n A
≡-to-isOfHLevel→isOfHLevel {n = n} A≡B = subst⁻ (isOfHLevel n) A≡B

≡-to-isContr→isContr : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isContr B → isContr A
≡-to-isContr→isContr = ≡-to-isOfHLevel→isOfHLevel {n = 0}

≡-from-isContr→isContr : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isContr A → isContr B
≡-from-isContr→isContr = ≡-from-isOfHLevel→isOfHLevel {n = 0}

≡-to-isProp→isProp : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isProp B → isProp A
≡-to-isProp→isProp = ≡-to-isOfHLevel→isOfHLevel {n = 1}

≡-from-isProp→isProp : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isProp A → isProp B
≡-from-isProp→isProp = ≡-from-isOfHLevel→isOfHLevel {n = 1}

≡-to-isSet→isSet : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isSet B → isSet A
≡-to-isSet→isSet = ≡-to-isOfHLevel→isOfHLevel {n = 2}

≡-from-isSet→isSet : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isSet A → isSet B
≡-from-isSet→isSet = ≡-from-isOfHLevel→isOfHLevel {n = 2}

Unit≢Bool : ¬ (Unit ≡ Bool)
Unit≢Bool p = false≢true (≡-from-isProp→isProp p isPropUnit false true)

Bool≢Unit : ¬ (Bool ≡ Unit)
Bool≢Unit p = false≢true (≡-to-isProp→isProp p isPropUnit false true)

false*≢true* : ¬ (false* {ℓ} ≡ true* {ℓ})
false*≢true* p = subst (λ b → if b .lower then Unit else ⊥) (sym p) tt

true*≢false* : ¬ (true* {ℓ} ≡ false* {ℓ})
true*≢false* p = subst (λ b → if b .lower then Unit else ⊥) p tt

Unit*≢Bool* : ¬ (Unit* {ℓ} ≡ Bool* {ℓ})
Unit*≢Bool* p = false*≢true* (≡-from-isProp→isProp p isPropUnit* false* true*)

Bool*≢Unit* : ¬ (Bool* {ℓ} ≡ Unit* {ℓ})
Bool*≢Unit* p = false*≢true* (≡-to-isProp→isProp p isPropUnit* false* true*)

-- probably also move to some better place in the library
module _ {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} (setX : isSet X) (x₀ : X) (f : (X × Y) → Z) (embf : isEmbedding f) where
    f-x₀ : Y → Z
    f-x₀ = curry f x₀

    Embedding-Σ-fst-const : isEmbedding f-x₀
    Embedding-Σ-fst-const = hasPropFibers→isEmbedding (λ z → isPropRetract (g z) (h z) (ret z) (isPropΣ (isEmbedding→hasPropFibers embf z) λ s → setX (s .fst .fst) x₀))
        where
            g : (z : Z) → (fiber f-x₀ z) → (Σ[ s ∈ fiber f z ] (s .fst .fst) ≡ x₀)
            g _ _ .fst .fst .fst = x₀
            g _ fib .fst .fst .snd = fib .fst
            g _ fib .fst .snd = fib .snd
            g _ _ .snd = refl

            h : (z : Z) → (Σ[ s ∈ fiber f z ] (s .fst .fst) ≡ x₀) → (fiber f-x₀ z)
            h _ s .fst = s .fst .fst .snd
            h _ s .snd = cong (λ x' → f (x' , (s .fst .fst .snd))) (sym (s .snd)) ∙ (s .fst .snd)

            ret : (z : Z) → retract (g z) (h z)
            ret _ fib = cong (fib .fst ,_) (sym (lUnit _))

private
    module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
        uninhabIsEquiv : ¬ A → ¬ B → isEquiv f
        uninhabIsEquiv ¬A ¬B = isoToIsEquiv isom
            where
                open Iso
                isom : Iso A B
                isom .fun = f
                isom .inv = ⊥-elim ∘ ¬B
                isom .ret a = ⊥-elim {A = λ _ → isom .inv (f a) ≡ a} (¬A a)
                isom .sec b = ⊥-elim {A = λ _ → f (isom .inv b) ≡ b} (¬B b)

    module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} (f : A → B) (g : B → C) (h : A → C) (equivf : isEquiv f) (equivh : isEquiv h) (h≡g∘f : h ≡ g ∘ f) where
        B≃C : B ≃ C
        B≃C = compEquiv (invEquiv (f , equivf)) (h , equivh)

        g' : B → C
        g' = B≃C .fst

        equivg' : isEquiv g'
        equivg' = B≃C .snd

        g'≡g : g' ≡ g
        g'≡g = funExt λ b → funExt⁻ h≡g∘f _ ∙ cong g (secIsEq equivf b)
            -- g' b
            --     ≡⟨⟩
            -- h (invIsEq equivf b)
            --     ≡⟨ funExt⁻ h≡g∘f _ ⟩
            -- g (f (invIsEq equivf b))
            --     ≡⟨ cong g (secIsEq equivf b) ⟩
            -- g b
            --     ∎
        second-in-isEquiv-comp→isEquiv : isEquiv g
        second-in-isEquiv-comp→isEquiv = transport (cong isEquiv g'≡g) equivg'

SumInl≢Inr : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) → ¬ (inl a :> A ⊎ B) ≡ (inr b :> A ⊎ B)
SumInl≢Inr {A = A} {B = B} a b p = transport (cong helper p) _
    where
        helper : A ⊎ B → Type ℓ-zero
        helper (inl _) = Unit
        helper (inr _) = ⊥

module _ {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} (f : X → Z) (g : Y → Z) where
    f+g : (X ⊎ Y) → Z
    f+g = ⊎-rec f g

    cong-f+g∘inl : {x x' : X} → x ≡ x' → f x ≡ f x'
    cong-f+g∘inl {x = x} {x' = x'} = cong (f+g ∘ inl)

    cong-f+g∘inr : {y y' : Y} → y ≡ y' → g y ≡ g y'
    cong-f+g∘inr {y = y} {y' = y'} = cong (f+g ∘ inr)
    
    isEmbeddingPair : isEmbedding f → isEmbedding g → ((x : X) (y : Y) → ¬ f x ≡ g y) → isEmbedding f+g
    isEmbeddingPair embf embg fx≢gy (inl x) (inl x') = second-in-isEquiv-comp→isEquiv (cong inl) (cong f+g) cong-f+g∘inl (isEmbedding-inl x x') (embf x x') refl
    isEmbeddingPair embf embg fx≢gy (inl x) (inr y') = uninhabIsEquiv (cong f+g) (SumInl≢Inr x y') (fx≢gy x y')
    isEmbeddingPair embf embg fx≢gy (inr y) (inl x') = uninhabIsEquiv (cong f+g) (λ eq → SumInl≢Inr x' y (sym eq)) λ eq → fx≢gy x' y (sym eq)
    isEmbeddingPair embf embg fx≢gy (inr y) (inr y') = second-in-isEquiv-comp→isEquiv (cong inr) (cong f+g) cong-f+g∘inr (isEmbedding-inr y y') (embg y y') refl
