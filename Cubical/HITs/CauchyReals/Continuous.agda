module Cubical.HITs.CauchyReals.Continuous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.Int.Fast as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)


open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊)

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Base

open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order

open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection

open import Cubical.HITs.CauchyReals.LiftingExpr

rexprTest : ∀ (q q' q'' : ℚ) →
         maxᵣ (minᵣ (rat q) (rat q')) (absᵣ (rat q'')) ≡
           rat (ℚ.max (ℚ.min q q') (ℚ.abs' q''))
rexprTest q q' q'' = ℚℝ!



IsContinuous : (ℝ → ℝ) → Type
IsContinuous f =
 ∀ u ε → ∃[ δ ∈ ℚ₊ ] (∀ v → u ∼[ δ ] v → f u ∼[ ε ] f v)

IsContinuousWithPred : (P : ℝ → hProp ℓ-zero) →
                        (∀ r → ⟨ P r ⟩ → ℝ) → Type
IsContinuousWithPred P f =
  ∀ u ε u∈P  → ∃[ δ ∈ ℚ₊ ] (∀ v v∈P → u ∼[ δ ] v →  f u u∈P ∼[ ε ] f v v∈P)

Lipschitz→IsContinuous : ∀ L f → Lipschitz-ℝ→ℝ L f →  IsContinuous f
Lipschitz→IsContinuous L f p u ε =
 ∣ (ℚ.invℚ₊ L) ℚ₊· ε ,
   (λ v → subst∼ (ℚ.y·[x/y] L (fst ε))
      ∘S p u v ((invℚ₊ L) ℚ₊· ε)) ∣₁

AsContinuousWithPred : (P : ℝ → hProp ℓ-zero) → (f : ℝ → ℝ)
                      → IsContinuous f
                      → IsContinuousWithPred P (λ x _ → f x)
AsContinuousWithPred P f x u ε _ =
  PT.map (map-snd (λ y z _ → y z)) (x u ε)

IsContinuousWP∘ : ∀ P P' f g → (h : ∀ r x → ⟨ P (g r x) ⟩)
   → (IsContinuousWithPred P f)
   → (IsContinuousWithPred P' g )
   → IsContinuousWithPred P'
     (λ r x → f (g r x) (h r x))
IsContinuousWP∘ P P' f g h fC gC u ε u∈P =
  PT.rec squash₁
    (λ (δ , δ∼) →
      PT.map (map-snd λ x v v∈P →
          δ∼ (g v v∈P) (h v v∈P) ∘ (x _ v∈P)) (gC u δ u∈P))
    ((fC (g u u∈P) ε (h _ u∈P)))

IsContinuous∘ : ∀ f g → (IsContinuous f) → (IsContinuous g)
                    → IsContinuous (f ∘ g)
IsContinuous∘ f g fC gC u ε =
  PT.rec squash₁
    (λ (δ , δ∼) →
      PT.map (map-snd λ x v → δ∼ (g v) ∘  (x _)  ) (gC u δ))
    (fC (g u) ε)

isPropIsContinuous : ∀ f → isProp (IsContinuous f)
isPropIsContinuous f = isPropΠ2 λ _ _ → squash₁

-- HoTT Lemma 11.3.39
≡Continuous : ∀ f g → IsContinuous f → IsContinuous g
                → (∀ r → f (rat r) ≡ g (rat r))
                → ∀ u → f u ≡ g u
≡Continuous f g fC gC p = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop (λ z → f z ≡ g z)
 w .Elimℝ-Prop.ratA = p
 w .Elimℝ-Prop.limA x p R = eqℝ _ _ λ ε →
   let f' = fC (lim x p) (ℚ./2₊ ε)
       g' = gC (lim x p) (ℚ./2₊ ε)
   in PT.rec2
       (isProp∼ _ _ _)
        (λ (θ , θ∼) (η , η∼) →
         let δ = ℚ./2₊ (ℚ.min₊ θ η)
             zF : f (lim x p) ∼[ ℚ./2₊ ε ] g (x δ)
             zF = subst (f (lim x p) ∼[ ℚ./2₊ ε ]_)
                  (R _)
                 (θ∼ _ (∼-monotone≤ (
                     subst (ℚ._≤ fst θ)
                      (sym (ℚ.ε/2+ε/2≡ε (fst (ℚ.min₊ θ η))))
                       (ℚ.min≤ (fst θ) (fst η)))
                  (sym∼ _ _ _ ((𝕣-lim-self x p δ δ)))))
             zG : g (lim x p) ∼[ ℚ./2₊ ε ] g (x δ)
             zG = η∼ _ (∼-monotone≤ (subst (ℚ._≤ fst η)
                      (sym (ℚ.ε/2+ε/2≡ε (fst (ℚ.min₊ θ η))))
                       (ℚ.min≤' (fst θ) (fst η)))
                  (sym∼ _ _ _ ((𝕣-lim-self x p δ δ))))
         in subst∼ (ℚ.ε/2+ε/2≡ε (fst ε)) (triangle∼ zF (sym∼ _ _ _ zG)))
        f' g'
 w .Elimℝ-Prop.isPropA _ = isSetℝ _ _



fromLipschitz' : ∀ f → ∃[ L ∈ ℚ₊ ] (Lipschitz-ℚ→ℝ L f)
                     → Σ[ f' ∈ (ℝ → ℝ) ] ∃[ L ∈ ℚ₊ ] (Lipschitz-ℝ→ℝ L f')
fromLipschitz' f = PT.elim→Set
  (λ _ → isSetΣ (isSet→ isSetℝ)
   λ _ → isProp→isSet squash₁)
   (λ (L , lip) → map-snd (∣_∣₁ ∘ (L ,_)) $ fromLipschitz L (f , lip))
   λ (L , lip) (L' , lip') →
    Σ≡Prop (λ _ → squash₁)
          (funExt (≡Continuous _ _
            (Lipschitz→IsContinuous L _
              (snd (fromLipschitz L (f , lip))))
            (Lipschitz→IsContinuous L' _
              ((snd (fromLipschitz L' (f , lip')))) )
            λ _ → refl))


openPred : (P : ℝ → hProp ℓ-zero) → hProp ℓ-zero
openPred P = (∀ x → ⟨ P x ⟩ → ∃[ δ ∈ ℚ₊ ] (∀ y → x ∼[ δ ] y → ⟨ P y ⟩ ) )
   , isPropΠ2 λ _ _ → squash₁

opaque
 unfolding maxᵣ minᵣ
 <min-rr : ∀ p q r → p <ᵣ (rat q) → p <ᵣ (rat r) → p <ᵣ minᵣ (rat q) (rat r)
 <min-rr p =
  ℚ.elimBy≤ (λ x y R a b → subst (p <ᵣ_) (minᵣComm (rat x) (rat y)) (R b a))
    λ x y x≤y p<x _ → subst ((p <ᵣ_) ∘ rat)
     (sym (ℚ.≤→min _ _ x≤y) ) (p<x)


m·n/m : ∀ m n → [ pos (suc m) / 1 ] ℚ.· [ pos n / 1+ m ] ≡ [ pos n / 1 ]
m·n/m m n =
  eq/ _ _ ((λ i → ℤ.·IdR (ℤ.·Comm (pos (suc m)) (pos n) i) i)
       ∙ cong ((pos n ℤ.·_) ∘ ℚ.ℕ₊₁→ℤ) (sym (·₊₁-identityˡ (1+ m))))



opaque
 unfolding absᵣ _<ᵣ_
 abs'q≤Δ₁ : ∀ q n → absᵣ (rat q) <ᵣ rat [ pos (suc n) / 1+ 0 ]
      →  ℚ.abs' q ℚ.≤ ([ pos (suc (suc (n))) / 1 ] ℚ.- [ 1 / 4 ])
 abs'q≤Δ₁ q n n< = (ℚ.isTrans≤ (ℚ.abs' q) (fromNat (suc n)) _
           (ℚ.<Weaken≤ _ _ ((<ᵣ→<ℚ _ _ n<)))
            (subst2 ℚ._≤_
              ((ℚ.+IdR _)) ℚ!
              (ℚ.≤-o+ 0 [ 3 / 4 ] (fromNat (suc n))
                (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 3 / 4 ]} _ ))))

abs'q≤Δ₁' : ∀ q n → ℚ.abs' q ℚ.≤ [ pos (suc n) / 1+ 0 ]
     →  ℚ.abs' q ℚ.≤ ([ pos (suc (suc (n))) / 1 ] ℚ.- [ 1 / 4 ])
abs'q≤Δ₁' q n n< = (ℚ.isTrans≤ (ℚ.abs' q) (fromNat (suc n)) _
          (n<)
           (subst2 ℚ._≤_
             ((ℚ.+IdR _)) ℚ!
             (ℚ.≤-o+ 0 [ 3 / 4 ] (fromNat (suc n))
               (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 3 / 4 ]} _ ))))


ℚabs-abs≤abs- : (x y : ℚ) → (ℚ.abs x ℚ.- ℚ.abs y) ℚ.≤ ℚ.abs (x ℚ.- y)
ℚabs-abs≤abs- x y =
 subst2 ℚ._≤_
  (cong {x = ((x ℚ.- y) ℚ.+ y)} {y = x} ((ℚ._+ (ℚ.- (ℚ.abs y))) ∘ ℚ.abs) ℚ!! )
   ℚ!!
  (ℚ.≤-+o
   (ℚ.abs ((x ℚ.- y) ℚ.+ y))
   (ℚ.abs (x ℚ.- y) ℚ.+ ℚ.abs y) (ℚ.- (ℚ.abs y)) (ℚ.abs+≤abs+abs (x ℚ.- y) y))

opaque
 unfolding absᵣ _<ᵣ_
 IsContinuousAbsᵣ : IsContinuous absᵣ
 IsContinuousAbsᵣ = Lipschitz→IsContinuous 1 _ absᵣ-lip

opaque
 unfolding maxᵣ minᵣ
 IsContinuousMaxR : ∀ x → IsContinuous (λ u → maxᵣ u x)
 IsContinuousMaxR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L maxR _ _ _ ε) ∣₁

 IsContinuousMaxL : ∀ x → IsContinuous (maxᵣ x)
 IsContinuousMaxL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R maxR x _ _ ε) ∣₁

 IsContinuousMinR : ∀ x → IsContinuous (λ u → minᵣ u x)
 IsContinuousMinR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L minR _ _ _ ε) ∣₁

 IsContinuousMinL : ∀ x → IsContinuous (minᵣ x)
 IsContinuousMinL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R minR x _ _ ε) ∣₁

IsContinuousClamp : ∀ a b → IsContinuous (clampᵣ a b)
IsContinuousClamp a b =
 IsContinuous∘ _ _
   (IsContinuousMinR _)
   (IsContinuousMaxL _)

IsContinuous-ᵣ : IsContinuous (-ᵣ_)
IsContinuous-ᵣ = Lipschitz→IsContinuous 1 _ -ᵣ-lip


contDiagNE₂ : ∀ {h} → (ne : NonExpanding₂ h)
  → ∀ f g → (IsContinuous f) → (IsContinuous g)
  → IsContinuous (λ x → NonExpanding₂.go ne (f x) (g x))
contDiagNE₂ ne f g fC gC u ε =
  PT.map2
    (λ (x , x') (y , y') →
      ℚ.min₊ x y , (λ v z →
          subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
           (NonExpanding₂.go∼₂ ne (ℚ./2₊ ε) (ℚ./2₊ ε)
           (x' v (∼-monotone≤ (ℚ.min≤ (fst x) (fst y)) z))
           (y' v (∼-monotone≤ (ℚ.min≤' (fst x) (fst y)) z)))))
   (fC u (ℚ./2₊ ε)) (gC u (ℚ./2₊ ε))

contDiagNE₂WP : ∀ {h} → (ne : NonExpanding₂ h)
  → ∀ P f g
     → (IsContinuousWithPred P f)
     → (IsContinuousWithPred P  g)
  → IsContinuousWithPred P (λ x x∈ → NonExpanding₂.go ne (f x x∈) (g x x∈))
contDiagNE₂WP ne P f g fC gC u ε u∈ =
    PT.map2
    (λ (x , x') (y , y') →

      ℚ.min₊ x y , (λ v v∈ z →
          subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
           (NonExpanding₂.go∼₂ ne (ℚ./2₊ ε) (ℚ./2₊ ε)
           (x' v v∈ (∼-monotone≤ (ℚ.min≤ (fst x) (fst y)) z))
           (y' v v∈ (∼-monotone≤ (ℚ.min≤' (fst x) (fst y)) z))))
           )
   (fC u (ℚ./2₊ ε) u∈) (gC u (ℚ./2₊ ε) u∈)

opaque
 unfolding _+ᵣ_
 cont₂+ᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
   → IsContinuous (λ x → f x +ᵣ g x)
 cont₂+ᵣ = contDiagNE₂ sumR




 IsContinuous+ᵣR : ∀ x → IsContinuous (_+ᵣ x)
 IsContinuous+ᵣR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L sumR _ _ _ ε) ∣₁

 IsContinuous+ᵣL : ∀ x → IsContinuous (x +ᵣ_)
 IsContinuous+ᵣL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R sumR x _ _ ε) ∣₁

opaque
 unfolding maxᵣ
 cont₂maxᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
   → IsContinuous (λ x → maxᵣ (f x) (g x))
 cont₂maxᵣ = contDiagNE₂ maxR

opaque
 unfolding minᵣ
 cont₂minᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
   → IsContinuous (λ x → minᵣ (f x) (g x))
 cont₂minᵣ = contDiagNE₂ minR




opaque
 unfolding _≤ᵣ_ absᵣ
 absᵣ-triangle : (x y : ℝ) → absᵣ (x +ᵣ y) ≤ᵣ (absᵣ x +ᵣ absᵣ y)
 absᵣ-triangle x y =
  let z = IsContinuous∘ _ _ (IsContinuous+ᵣR (absᵣ y)) IsContinuousAbsᵣ

  in ≡Continuous
     (λ x → maxᵣ (absᵣ (x +ᵣ y)) ((absᵣ x +ᵣ absᵣ y)))
     (λ x → (absᵣ x +ᵣ absᵣ y))
     (cont₂maxᵣ _ _
       (IsContinuous∘ _ _ IsContinuousAbsᵣ (IsContinuous+ᵣR y)) z)
     z
     (λ r → let z' = IsContinuous∘ _ _ (IsContinuous+ᵣL (absᵣ (rat r)))
                 IsContinuousAbsᵣ
      in ≡Continuous
     (λ y → maxᵣ (absᵣ ((rat r) +ᵣ y)) ((absᵣ (rat r) +ᵣ absᵣ y)))
     (λ y → (absᵣ (rat r) +ᵣ absᵣ y))
     (cont₂maxᵣ _ _
         ((IsContinuous∘ _ _ IsContinuousAbsᵣ (IsContinuous+ᵣL (rat r))))
           z' ) z'
     (λ r' → cong rat (ℚ.≤→max _ _
               (subst2 ℚ._≤_ (ℚ.abs'≡abs (r ℚ.+ r'))
                 (cong₂ ℚ._+_ (ℚ.abs'≡abs r) (ℚ.abs'≡abs r'))
                (ℚ.abs+≤abs+abs r r') ) )) y) x



IsContinuousId : IsContinuous (λ x → x)
IsContinuousId u ε = ∣ ε , (λ _ x → x) ∣₁

IsContinuousConst : ∀ x → IsContinuous (λ _ → x)
IsContinuousConst x u ε = ∣ ε , (λ _ _ → refl∼ _ _ ) ∣₁


opaque
 unfolding _+ᵣ_ minᵣ maxᵣ
 +IdL : ∀ x → 0 +ᵣ x ≡ x
 +IdL = ≡Continuous _ _ (IsContinuous+ᵣL 0) IsContinuousId
   (cong rat ∘ ℚ.+IdL)

 +IdR : ∀ x → x +ᵣ 0 ≡ x
 +IdR = ≡Continuous _ _ (IsContinuous+ᵣR 0) IsContinuousId
   (cong rat ∘ ℚ.+IdR)


 +ᵣMaxDistr : ∀ x y z → (maxᵣ x y) +ᵣ z ≡ maxᵣ (x +ᵣ z) (y +ᵣ z)
 +ᵣMaxDistr x y z =
   ≡Continuous _ _
      (IsContinuous∘ _ _ (IsContinuous+ᵣR z) (IsContinuousMaxR y))
      (IsContinuous∘ _ _ (IsContinuousMaxR (y +ᵣ z)) (IsContinuous+ᵣR z))
      (λ x' →
        ≡Continuous _ _
          (IsContinuous∘ _ _ (IsContinuous+ᵣR z) (IsContinuousMaxL (rat x')))
          ((IsContinuous∘ _ _ (IsContinuousMaxL (rat x' +ᵣ z))
                                 (IsContinuous+ᵣR z)))
          (λ y' → ≡Continuous _ _
            (IsContinuous+ᵣL (maxᵣ (rat x') ( rat y')))
            (cont₂maxᵣ _ _ (IsContinuous+ᵣL (rat x'))
                           (IsContinuous+ᵣL (rat y')))
            (λ z' → cong rat $ ℚ.+MaxDistrℚ x' y' z')
            z)
          y)
      x

opaque
 unfolding _≤ᵣ_ absᵣ

 ≤ᵣ-+o : ∀ m n o →  m ≤ᵣ n → (m +ᵣ o) ≤ᵣ (n +ᵣ o)
 ≤ᵣ-+o m n o p = sym (+ᵣMaxDistr m n o) ∙ cong (_+ᵣ o) p


 abs-max : ∀ x → absᵣ x ≡ maxᵣ x (-ᵣ x)
 abs-max = ≡Continuous _ _
   IsContinuousAbsᵣ
    (cont₂maxᵣ _ _ IsContinuousId IsContinuous-ᵣ)
     λ r → cong rat (sym (ℚ.abs'≡abs r))


≤ᵣ-o+ : ∀ m n o →  m ≤ᵣ n → (o +ᵣ m) ≤ᵣ (o +ᵣ n)
≤ᵣ-o+ m n o = subst2 _≤ᵣ_ (+ᵣComm _ _) (+ᵣComm _ _)  ∘ ≤ᵣ-+o m n o


≤ᵣMonotone+ᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s → (m +ᵣ o) ≤ᵣ (n +ᵣ s)
≤ᵣMonotone+ᵣ m n o s m≤n o≤s =
  isTrans≤ᵣ _ _ _ (≤ᵣ-+o m n o m≤n) (≤ᵣ-o+ o s n o≤s)



opaque


 absᵣNonNeg : ∀ x → 0 ≤ᵣ x → absᵣ x ≡ x
 absᵣNonNeg x p = abs-max x ∙∙ maxᵣComm x (-ᵣ x) ∙∙ ≤ᵣ→≡ z
  where
    z : (-ᵣ x) ≤ᵣ x
    z = subst2 _≤ᵣ_
      (+IdL (-ᵣ x))
      (sym (+ᵣAssoc _ _ _) ∙∙ cong (x +ᵣ_) (+-ᵣ x) ∙∙ +IdR x)
      (≤ᵣ-+o 0 (x +ᵣ x) (-ᵣ x)
       (isTrans≡≤ᵣ _ _ _ (sym (+ᵣ-rat 0 0)) (≤ᵣMonotone+ᵣ 0 x 0 x p p)))


 absᵣPos : ∀ x → 0 <ᵣ x → absᵣ x ≡ x
 absᵣPos x = absᵣNonNeg x ∘ <ᵣWeaken≤ᵣ _ _

opaque
 unfolding maxᵣ

 ≤lim : ∀ r x y → (∀ δ → rat r ≤ᵣ x δ) → rat r ≤ᵣ lim x y
 ≤lim r x y p = ≡→≤ᵣ $
   snd (NonExpanding₂.β-rat-lim' maxR r x y) ∙
        congLim _ _ _ _ (≤ᵣ→≡ ∘ p)

 limConstRat : ∀ x y → lim (λ _ → (rat x)) y ≡ rat x
 limConstRat x y = eqℝ _ _ λ ε → lim-rat _ _ _ (/2₊ ε) _
   (ℚ.<→0< _ (ℚ.<→<minus _ _ (ℚ.x/2<x ε))) (refl∼  _ _)

 lim≤ : ∀ r x y → (∀ δ → x δ ≤ᵣ rat r ) → lim x y ≤ᵣ rat r
 lim≤ r x y p = ≡→≤ᵣ $ maxᵣComm (lim x y) (rat r) ∙ snd (NonExpanding₂.β-rat-lim' maxR r x y) ∙
    congLim' _ _ _ (λ δ → maxᵣComm (rat r) (x δ) ∙ ≤ᵣ→≡ (p δ))
     ∙ limConstRat _ _


 IsContinuousWithPred∘IsContinuous : ∀ P f g
  → (g∈ : ∀ x → g x ∈ P)
  → IsContinuousWithPred P f
  → IsContinuous g
  → IsContinuous λ x → f (g x) (g∈ x)
 IsContinuousWithPred∘IsContinuous P f g g∈ fc gc u ε =
   PT.rec squash₁
          (λ (δ , δ∼) →
       PT.map (map-snd λ x v u∼v →
          δ∼ (g v) (g∈ v) (x v u∼v)
           ) (gc u δ) )
       (fc (g u) ε (g∈ u))




 IsContinuousWP∘' : ∀ P f g
    → (IsContinuous f)
    → (IsContinuousWithPred P g )
    → IsContinuousWithPred P
      (λ r x → f (g r x))
 IsContinuousWP∘' P f g fC gC u ε u∈P =
   PT.rec squash₁
     (λ (δ , δ∼) →
       PT.map (map-snd λ x v v∈P →
           δ∼ (g v v∈P) ∘ (x _ v∈P)) (gC u δ u∈P))
     ((fC (g u u∈P) ε))


 contDropPred : ∀ f → IsContinuousWithPred ⊤Pred (λ x _ → f x)
                 → IsContinuous f
 contDropPred f =
  flip (IsContinuousWithPred∘IsContinuous  ⊤Pred (λ x _ → f x)
    (idfun _) _) IsContinuousId


 ∩-openPred : ∀ P Q → ⟨ openPred P ⟩ → ⟨ openPred Q ⟩ →
               ⟨ openPred (λ x → _ , isProp× (snd (P x)) (snd (Q x))) ⟩
 ∩-openPred _ _ oP oQ x (x∈P , x∈Q) =
   PT.map2 (λ (δ , Δ) (δ' , Δ') →
      (ℚ.min₊ δ δ') , λ y x∼y →
        (Δ y (∼-monotone≤ (ℚ.min≤ _ _) x∼y))
       , Δ' y (∼-monotone≤ (ℚ.min≤' (fst δ) (fst δ')) x∼y))
    (oP x x∈P) (oQ x x∈Q)




-ᵣ≤ᵣ : ∀ x y → x ≤ᵣ y → -ᵣ y ≤ᵣ -ᵣ x
-ᵣ≤ᵣ x y p = subst2 _≤ᵣ_
    (+ᵣAssoc _ _ _ ∙ cong (_+ᵣ (-ᵣ y)) (+-ᵣ x) ∙ +IdL _)
      (cong (y +ᵣ_) (+ᵣComm _ _)
       ∙∙ +ᵣAssoc _ _ _ ∙∙ (cong (_+ᵣ (-ᵣ x)) (+-ᵣ y) ∙ +IdL _)) (≤ᵣ-+o _ _ ((-ᵣ x) +ᵣ (-ᵣ y)) p)

≤ᵣ-ᵣ : ∀ x y → -ᵣ y ≤ᵣ -ᵣ x →  x ≤ᵣ y
≤ᵣ-ᵣ x y = subst2 _≤ᵣ_ (-ᵣInvol x) (-ᵣInvol y) ∘ -ᵣ≤ᵣ (-ᵣ y) (-ᵣ x)



opaque
 unfolding _<ᵣ_
 -ᵣ<ᵣ : ∀ x y → x <ᵣ y → -ᵣ y <ᵣ -ᵣ x
 -ᵣ<ᵣ x y = PT.map
   λ ((q , q') , z , z' , z'') →
        (ℚ.- q' , ℚ.- q) , -ᵣ≤ᵣ (rat q') _ z'' , ((ℚ.minus-< _ _ z') , -ᵣ≤ᵣ x _ z)


open ℚ.HLP

𝕣-lim-dist : ∀ x y ε → absᵣ ((x (ℚ./2₊ ε)) +ᵣ (-ᵣ lim x y)) <ᵣ rat (fst ε)
𝕣-lim-dist x y ε =
   fst (∼≃abs<ε _ _ ε) $ subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
     $ 𝕣-lim-self x y (ℚ./2₊ ε) (ℚ./2₊ ε)


opaque
 unfolding absᵣ _≤ᵣ_
 ≤absᵣ : ∀ x → x ≤ᵣ absᵣ x
 ≤absᵣ = ≡Continuous
   (λ x → maxᵣ x (absᵣ x))
   (λ x → absᵣ x)
   (cont₂maxᵣ _ _ IsContinuousId IsContinuousAbsᵣ)
   IsContinuousAbsᵣ
   λ x →  cong (maxᵣ (rat x) ∘ rat) (sym (ℚ.abs'≡abs x))
      ∙∙ cong rat (ℚ.≤→max _ _ (ℚ.≤abs x)) ∙∙
      cong rat (ℚ.abs'≡abs x )


from-abs< : ∀ x y z → absᵣ (x +ᵣ (-ᵣ y)) <ᵣ z
       → (x +ᵣ (-ᵣ y) <ᵣ z)
          × ((y +ᵣ (-ᵣ x) <ᵣ z))
            × ((-ᵣ y) +ᵣ x <ᵣ z)
from-abs< x y z p = isTrans≤<ᵣ _ _ _ (≤absᵣ _) p ,
 isTrans≤<ᵣ _ _ _ (≤absᵣ _) (subst (_<ᵣ z) (minusComm-absᵣ x y) p)
   , isTrans≤<ᵣ _ _ _ (≤absᵣ _) (subst (((_<ᵣ z) ∘ absᵣ)) (+ᵣComm x (-ᵣ y)) p)





opaque
 ∃rationalApprox≤ : ∀ u → (ε : ℚ₊) →
    ∃[ q ∈ ℚ ] (((rat q) +ᵣ (-ᵣ u)) ≤ᵣ rat (fst ε)) × (u ≤ᵣ rat q)
 ∃rationalApprox≤ = Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop λ u → (ε : ℚ₊) →
    ∃[ q ∈ ℚ ] (((rat q) +ᵣ (-ᵣ u)) ≤ᵣ rat (fst ε)) × (u ≤ᵣ rat q)
  w .Elimℝ-Prop.ratA r ε =
   ∣  r ℚ.+ fst (/2₊ ε) ,
    (isTrans≡≤ᵣ _ _ _ (-ᵣ-rat₂ _ _) $ ≤ℚ→≤ᵣ _ _ (
      let zz = (subst (ℚ._≤ fst ε) ℚ!!
             (ℚ.<Weaken≤ _ _ (ℚ.x/2<x (ε))) )
      in zz))
        , ≤ℚ→≤ᵣ _ _ (ℚ.≤+ℚ₊ r r (/2₊ ε) (ℚ.isRefl≤ r)) ∣₁
  w .Elimℝ-Prop.limA x y R ε =
    let z = 𝕣-lim-dist x y (/4₊ ε)
    in PT.map (λ (q , z , z') →
         let (_ , Xzz' , Xzz) = from-abs< _ _ _
                      (𝕣-lim-dist x y (/4₊ ε))

             zz :  (-ᵣ (lim x y)) +ᵣ x (/2₊ (/4₊ ε))   ≤ᵣ rat (fst (/4₊ ε))
             zz = <ᵣWeaken≤ᵣ _ _ Xzz
             zz' :  (lim x y) +ᵣ (-ᵣ (x (/2₊ (/4₊ ε))))   ≤ᵣ rat (fst (/4₊ ε))
             zz' = <ᵣWeaken≤ᵣ _ _ Xzz'
         in q ℚ.+ fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε))  ,
               let zzz = (≤ᵣ-+o _ _ (rat (fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε))))
                       (≤ᵣMonotone+ᵣ _ _ _ _ z zz))

               in subst2 _≤ᵣ_
                     (cong (_+ᵣ rat (fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε))))
                      (sym (+ᵣAssoc (rat q) _ _)) ∙
                      +ᵣComm _ _ ∙ +ᵣAssoc _ _ _ ∙
                       cong₂ _+ᵣ_
                        (+ᵣComm _ _ ∙ +ᵣ-rat _ _ ∙ cong rat ℚ!!)
                         (cong₂ _+ᵣ_ refl (+ᵣComm _ _) ∙ +ᵣAssoc _ _ _  ∙
                          cong₂ _+ᵣ_ (+ᵣComm _ _ ∙ +-ᵣ _) refl ∙ +IdL _))

                     (_∙_ {x = rat (fst (/2₊ (/4₊ ε))) +ᵣ rat (fst (/4₊ ε)) +ᵣ
                                rat (fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε)))}
                                 {y = rat
                                       (fst (/2₊ (/4₊ ε)) ℚ.+ fst (/4₊ ε) ℚ.+
                                        (fst (/2₊ ε) ℚ.+ fst (/2₊ (/4₊ ε))))}
                       ℚℝ!
                     (cong rat ℚ!!))

                   zzz
                 ,
                  isTrans≤ᵣ _ _ _ (subst (_≤ᵣ (rat q +ᵣ rat (fst (/4₊ ε))))
                    (cong (x (/2₊ (/4₊ ε)) +ᵣ_) (+ᵣComm _ _) ∙
                      +ᵣAssoc _ _ _ ∙
                       cong (_+ᵣ (lim x y)) (+-ᵣ _) ∙ +IdL _)
                     (≤ᵣMonotone+ᵣ _ _ _ _ z' zz'))
                     (isTrans≡≤ᵣ _ _ _ (+ᵣ-rat _  _) $ ≤ℚ→≤ᵣ _ _

                       (subst (q ℚ.+ fst (/4₊ ε) ℚ.≤_)
                         ((ℚ.+Assoc q _ _))
                          (ℚ.≤-o+ _ _ q distℚ≤!
                           ε [ ge[ ℚ.[ 1 / 4 ] ] ≤
                           ge[ ℚ.[ 1 / 2 ] ]
                             +ge (ge[ ℚ.[ 1 / 4 ] ]
                                ·ge ge[ ℚ.[ 1 / 2 ] ]) ]) )
                                ))
         (R (/2₊ (/4₊ ε)) (/2₊ (/4₊ ε)))
  w .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → squash₁



opaque
 ∃rationalApprox : ∀ u → (ε : ℚ₊) →
    ∃[ (q , q') ∈ (ℚ × ℚ) ] (q' ℚ.- q ℚ.< fst ε) ×
                            ((rat q <ᵣ u) × (u <ᵣ rat q'))
 ∃rationalApprox u ε =
   PT.map2 (uncurry (λ q (x , x') → uncurry (λ q' (y , y') →
       ((ℚ.- (q ℚ.+ (fst (/4₊ ε)))) , q' ℚ.+ (fst (/4₊ ε))) ,
             let zz = ℚ.≤-+o (q ℚ.+ q') _ (fst (/4₊ ε) ℚ.+ fst (/4₊ ε))
                       (≤ᵣ→≤ℚ _ _ (subst2 _≤ᵣ_
                        (sym (+ᵣAssoc (rat q) _ _) ∙
                         cong (rat q +ᵣ_) (cong₂ _+ᵣ_ (-ᵣInvol u) (+ᵣComm _ _)
                           ∙ +ᵣAssoc u (-ᵣ u) _ ∙ cong (_+ᵣ (rat q')) (+-ᵣ u)
                            ∙ +IdL (rat q'))
                            ∙ +ᵣ-rat q q')
                        (+ᵣ-rat _ _)
                       (≤ᵣMonotone+ᵣ _ _ _ _ x y)))
                 zzz : (fst (/2₊ (/4₊ ε)) ℚ.+ fst (/2₊ (/4₊ ε)))
                     ℚ.+ (fst (/4₊ ε) ℚ.+ fst (/4₊ ε)) ℚ.< fst ε
                 zzz = distℚ<! ε [
                              (ge[ ℚ.[ 1 / 4 ] ]
                                 ·ge ge[ ℚ.[ 1 / 2 ] ]
                               +ge ge[ ℚ.[ 1 / 4 ] ]
                                 ·ge ge[ ℚ.[ 1 / 2 ] ] )
                             +ge (ge[ ℚ.[ 1 / 4 ] ]
                               +ge ge[ ℚ.[ 1 / 4 ] ]) < ge1 ]
             in ℚ.isTrans≤< _ _ _ (subst (ℚ._≤ _) ℚ!! zz) zzz
                  ,
             (subst2 (_<ᵣ_) (-ᵣ-rat _) (-ᵣInvol u)
                (-ᵣ<ᵣ _ _ $ isTrans≤<ᵣ _ _ _ x'
                 (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ (/4₊ ε) (ℚ.isRefl≤ _) )))
                  , isTrans≤<ᵣ _ _ _ y'
                 (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ (/4₊ ε) (ℚ.isRefl≤ _) )))
      )
      )) (∃rationalApprox≤ (-ᵣ u) (/2₊ (/4₊ ε)))
         (∃rationalApprox≤ u (/2₊ (/4₊ ε)))


∃rationalApprox< : ∀ u → (ε : ℚ₊) →
   ∃[ q ∈ ℚ ] (((rat q) +ᵣ (-ᵣ u)) <ᵣ rat (fst ε)) × (u <ᵣ rat q)
∃rationalApprox< u ε =
  PT.map (uncurry (λ q (x , x') →
     q ℚ.+ (fst (/4₊ ε))  ,
          subst (_<ᵣ (rat (fst ε)))
            ((sym (+ᵣAssoc (rat q) (-ᵣ u) _) ∙
              cong ((rat q) +ᵣ_) (+ᵣComm (-ᵣ u) (rat (fst (/4₊ ε))) ))
               ∙∙ +ᵣAssoc (rat q) (rat (fst (/4₊ ε))) (-ᵣ u) ∙∙ ℚℝ!)  (
             isTrans≤<ᵣ _ _ (rat (fst ε)) (≤ᵣ-+o _ _ (rat (fst (/4₊ ε))) x)
              (isTrans≡<ᵣ _ _ _ (+ᵣ-rat _ _)
               ((<ℚ→<ᵣ _ _ $
               distℚ<! ε [ ge[ ℚ.[ 1 / 2 ] ]
                 +ge ge[ ℚ.[ 1 / 4 ] ] < ge1 ])))) ,
              isTrans≤<ᵣ _ _ _ x'
                (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ (/4₊ ε) (ℚ.isRefl≤ _) )) ))
            $ ∃rationalApprox≤ u (/2₊ ε)


opaque

 <ᵣ-+o-pre : ∀ m n o  → m ℚ.< n  → (rat m +ᵣ o) <ᵣ (rat n +ᵣ o)
 <ᵣ-+o-pre m n o m<n =
   PT.rec2 (isProp<ᵣ _ _) (λ (q , x , x') ((q' , q'') , y , y' , y'') →
      let x* : (rat q) ≤ᵣ rat (fst (/4₊ Δ)) +ᵣ ((rat m +ᵣ o))
          x* =  subst (_≤ᵣ rat (fst (/4₊ Δ)) +ᵣ ((rat m +ᵣ o)))
                 (sym (+ᵣAssoc (rat q) _ _) ∙
                  cong (rat q +ᵣ_) (+ᵣComm _ _ ∙ +-ᵣ _) ∙ +IdR (rat q))
                  (≤ᵣ-+o _ _
                   ((rat m +ᵣ o)) (<ᵣWeaken≤ᵣ _ _ x))

          y* : (rat (fst (/4₊ Δ)) +ᵣ (rat m +ᵣ o)) ≤ᵣ
                (-ᵣ (rat (fst (/4₊ Δ)) +ᵣ (-ᵣ (rat n +ᵣ o))))
          y* = subst2 {x = rat (fst (/2₊ Δ))
                  +ᵣ (rat m +ᵣ (o +ᵣ (-ᵣ (rat (fst (/4₊ Δ))))))}
                 _≤ᵣ_ -- (rat m +ᵣ (o +ᵣ (-ᵣ rat (fst (/4₊ Δ)))))
               ((λ i → +ᵣComm (rat (fst (/2₊ Δ)))
                    (+ᵣAssoc (rat m) o (-ᵣ rat (fst (/4₊ Δ))) i) i)
                     ∙ sym (+ᵣAssoc _ _ _) ∙
                       cong ((rat m +ᵣ o) +ᵣ_)
                         (+ᵣComm _ _ ∙
                          -ᵣ-rat₂ _ _ ∙
                           cong rat ℚ!!)
                         ∙ +ᵣComm _ _ )
               (+ᵣAssoc _ _ _ ∙
                 cong (_+ᵣ (o +ᵣ (-ᵣ rat (fst (/4₊ Δ)))))
                    (+ᵣ-rat (n ℚ.- m) _ ∙ cong rat ℚ!!) ∙
                     +ᵣAssoc _ _ _ ∙
                      (λ i → +ᵣComm (-ᵣInvol (rat n +ᵣ o) (~ i))
                        (-ᵣ rat (fst (/4₊ Δ))) i) ∙
                       sym (-ᵣDistr (rat (fst (/4₊ Δ))) ((-ᵣ (rat n +ᵣ o)))) )
               (≤ᵣ-+o _ _ (rat m +ᵣ (o +ᵣ (-ᵣ (rat (fst (/4₊ Δ))))))
                 (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ (ℚ.x/2<x Δ)))
                 )

          z* : -ᵣ (rat (fst (/4₊ Δ)) +ᵣ (-ᵣ (rat n +ᵣ o)))
                ≤ᵣ ((rat q'))
          z* = subst ((-ᵣ (rat (fst (/4₊ Δ)) +ᵣ (-ᵣ (rat n +ᵣ o)))) ≤ᵣ_)
                (cong (-ᵣ_) (sym (+ᵣAssoc (rat q'') (-ᵣ rat q') _)
                    ∙ _∙_ {y = rat (q'' ℚ.+ (ℚ.- q' ℚ.+ ℚ.- q''))}
                      ℚℝ!
                     (cong rat ℚ!! ∙ sym (-ᵣ-rat q'))) ∙
                      -ᵣInvol (rat q'))

                     (-ᵣ≤ᵣ _ _ (≤ᵣMonotone+ᵣ _ _ _ _
                 (isTrans≡≤ᵣ _ _ _ (-ᵣ-rat₂ _ _)
                   (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ y))) -- (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ y))
                  (<ᵣWeaken≤ᵣ _ _ (-ᵣ<ᵣ _ _ y''))))
          z : rat q ≤ᵣ rat q'
          z = isTrans≤ᵣ _ _ _
               (isTrans≤ᵣ _ _ _
                   x* y* ) z*
      in isTrans<ᵣ _ _ _ x'
         (isTrans≤<ᵣ _ _ _ z y'))
     (∃rationalApprox< (rat m +ᵣ o) (/4₊ Δ))
      ((∃rationalApprox (rat n +ᵣ o) (/4₊ Δ)))

  where
  Δ : ℚ₊
  Δ = ℚ.<→ℚ₊ m n m<n

opaque
 unfolding _<ᵣ_
 <ᵣ-+o : ∀ m n o →  m <ᵣ n → (m +ᵣ o) <ᵣ (n +ᵣ o)
 <ᵣ-+o m n o = PT.rec (isProp<ᵣ (m +ᵣ o) _)
   λ ((q , q') , x , x' , x'') →
    let y : (m +ᵣ o) ≤ᵣ (rat q +ᵣ o)
        y = ≤ᵣ-+o m (rat q) o x
        y'' : (rat q' +ᵣ o) ≤ᵣ (n +ᵣ o)
        y'' = ≤ᵣ-+o (rat q') n o x''

        y' : (rat q +ᵣ o) <ᵣ (rat q' +ᵣ o)
        y' = <ᵣ-+o-pre q q' o x'


    in isTrans<≤ᵣ (m +ᵣ o) _ _ (isTrans≤<ᵣ (m +ᵣ o) _ _ y y') y''

<ᵣ-o+ : ∀ m n o →  m <ᵣ n → (o +ᵣ m) <ᵣ (o +ᵣ n)
<ᵣ-o+ m n o = subst2 _<ᵣ_ (+ᵣComm m o) (+ᵣComm n o) ∘ <ᵣ-+o m n o


lowerℚBound : ∀ u → 0 <ᵣ u → ∃[ ε ∈ ℚ₊ ] (rat (fst ε) <ᵣ u)
lowerℚBound u x =
  PT.map (λ (ε , (x' , x'')) → (ε , ℚ.<→0< _ (<ᵣ→<ℚ _ _ x')) , x'')
    (denseℚinℝ 0 u x)


a<b-c⇒c<b-a : ∀ a b c → a <ᵣ b +ᵣ (-ᵣ c) → c <ᵣ b +ᵣ (-ᵣ a)
a<b-c⇒c<b-a a b c p =
   subst2 _<ᵣ_
    ((cong (a +ᵣ_) (+ᵣComm _ _) ∙∙ +ᵣAssoc _ _ _ ∙ cong (_+ᵣ c) (+-ᵣ a) ∙∙ +IdL c))
     ((sym (+ᵣAssoc _ _ _) ∙
      cong (b +ᵣ_) ((+ᵣAssoc _ _ _) ∙∙ cong (_-ᵣ a) (+ᵣComm _ _ ∙ +-ᵣ c) ∙∙ +IdL _)))
     (<ᵣ-+o _ _ (c +ᵣ (-ᵣ a)) p)

a≤b-c⇒c≤b-a : ∀ a b c → a ≤ᵣ b -ᵣ c → c ≤ᵣ b -ᵣ a
a≤b-c⇒c≤b-a a b c p =
   subst2 _≤ᵣ_
     (cong (a +ᵣ_) (+ᵣComm _ _) ∙∙ +ᵣAssoc _ _ _ ∙ cong (_+ᵣ c) (+-ᵣ a) ∙∙ +IdL c)
     (sym (+ᵣAssoc _ _ _) ∙
      cong (b +ᵣ_) ((+ᵣAssoc _ _ _) ∙∙ cong (_-ᵣ a) (+ᵣComm _ _ ∙ +-ᵣ c) ∙∙ +IdL _))
     (≤ᵣ-+o _ _ (c -ᵣ a) p)

a<b-c⇒a+c<b : ∀ a b c → a <ᵣ b +ᵣ (-ᵣ c) → a +ᵣ c <ᵣ b
a<b-c⇒a+c<b a b c p =
   subst ((a +ᵣ c) <ᵣ_)
        (sym (+ᵣAssoc _  _ _) ∙∙ cong (b +ᵣ_) (+ᵣComm _ _ ∙ +-ᵣ c) ∙∙ +IdR b)
     (<ᵣ-+o _ _ c p)



a+c<b⇒a<b-c : ∀ a b c → a +ᵣ c <ᵣ b  → a <ᵣ b -ᵣ c
a+c<b⇒a<b-c a b c p =
   subst (_<ᵣ b -ᵣ c)
        (sym (+ᵣAssoc _ _ _) ∙
         (cong (a +ᵣ_) (+-ᵣ c) ∙  +IdR a ))
     (<ᵣ-+o _ _ (-ᵣ c) p)

a-b<c⇒a-c<b : ∀ a b c → a +ᵣ (-ᵣ b) <ᵣ c  → a +ᵣ (-ᵣ c) <ᵣ b
a-b<c⇒a-c<b a b c p =
  subst2 _<ᵣ_
    (sym (+ᵣAssoc _ _ _) ∙
      cong (a +ᵣ_) ((+ᵣAssoc _ _ _) ∙∙
       cong (_+ᵣ (-ᵣ c)) (+ᵣComm _ _ ∙ +-ᵣ b) ∙∙ +IdL (-ᵣ c)))
    (cong (c +ᵣ_) (+ᵣComm _ _) ∙ +ᵣAssoc _ _ _ ∙∙ cong (_+ᵣ b) (+-ᵣ c) ∙∙ +IdL b )
     (<ᵣ-+o _ _ (b +ᵣ (-ᵣ c)) p)

x<y→0<y-x : ∀ x y →  x <ᵣ y  → 0 <ᵣ y +ᵣ (-ᵣ x)
x<y→0<y-x x y p =
  subst (_<ᵣ y +ᵣ (-ᵣ x)) (+-ᵣ x) (<ᵣ-+o x y (-ᵣ x) p)


a-b<c⇒a<c+b : ∀ a b c → a +ᵣ (-ᵣ b) <ᵣ c  → a <ᵣ c +ᵣ b
a-b<c⇒a<c+b a b c p =
  subst (_<ᵣ (c +ᵣ b))
    (sym (+ᵣAssoc _ _ _) ∙∙ cong (a +ᵣ_) (+ᵣComm _ _ ∙ +-ᵣ b) ∙∙ +IdR a)
     (<ᵣ-+o _ _ b p)


openPred< : ∀ x → ⟨ openPred (λ y → (x <ᵣ y) , isProp<ᵣ _ _)  ⟩
openPred< x y =
     PT.map (map-snd (λ {q} a<y-x v
        →   isTrans<ᵣ _ _ _
                (a<b-c⇒c<b-a (rat (fst q)) y x a<y-x )
          ∘S a-b<c⇒a-c<b y v (rat (fst q))
          ∘S isTrans≤<ᵣ _ _ _ (≤absᵣ _)
          ∘S fst (∼≃abs<ε _ _ _)))
  ∘S lowerℚBound (y +ᵣ (-ᵣ x))
  ∘S x<y→0<y-x x y

openPred> : ∀ x → ⟨ openPred (λ y → (y <ᵣ x) , isProp<ᵣ _ _)  ⟩
openPred> x y =
       PT.map (map-snd (λ {q} q<x-y v
        →     flip (isTrans<ᵣ _ _ _)
                (a<b-c⇒a+c<b (rat (fst q)) x y q<x-y )
          ∘S a-b<c⇒a<c+b v y (rat (fst q))
          ∘S isTrans≤<ᵣ _ _ _ (≤absᵣ _)
          ∘S fst (∼≃abs<ε _ _ _)
          ∘S sym∼ _ _ _ ))
  ∘S lowerℚBound (x +ᵣ (-ᵣ y))
  ∘S x<y→0<y-x y x


openIintervalℙ : ∀ a b → ⟨ openPred (ointervalℙ a b)  ⟩
openIintervalℙ a b = ∩-openPred (pred> a) (pred< b) (openPred< a) (openPred> b)


isIncrasingℙ : (P : ℙ ℚ) → (∀ x → x ∈ P → ℚ) → Type₀
isIncrasingℙ P f = ∀ x x∈ y y∈ → x ℚ.< y → f x x∈ ℚ.< f y y∈

isNondecrasingℙ : (P : ℙ ℚ) → (∀ x → x ∈ P → ℚ) → Type₀
isNondecrasingℙ P f = ∀ x x∈ y y∈ → x ℚ.≤ y → f x x∈ ℚ.≤ f y y∈



max-lem : ∀ x x' y → maxᵣ (maxᵣ x y) (maxᵣ x' y) ≡ (maxᵣ (maxᵣ x x') y)
max-lem x x' y = maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ y) (maxᵣComm _ _)
  ∙ sym (maxᵣAssoc _ _ _) ∙
    cong (maxᵣ x') (sym (maxᵣAssoc _ _ _) ∙ cong (maxᵣ x) (maxᵣIdem y))
     ∙ maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ y) (maxᵣComm _ _)

opaque
 unfolding maxᵣ


 minᵣIdem : ∀ x → minᵣ x x ≡ x
 minᵣIdem = ≡Continuous _ _
   (cont₂minᵣ _ _ IsContinuousId IsContinuousId)
   IsContinuousId
   (cong rat ∘ ℚ.minIdem)


min-lem : ∀ x x' y → minᵣ (minᵣ x y) (minᵣ x' y) ≡ (minᵣ (minᵣ x x') y)
min-lem x x' y = minᵣAssoc _ _ _ ∙ cong (flip minᵣ y) (minᵣComm _ _)
  ∙ sym (minᵣAssoc _ _ _) ∙
    cong (minᵣ x') (sym (minᵣAssoc _ _ _) ∙ cong (minᵣ x) (minᵣIdem y))
     ∙ minᵣAssoc _ _ _ ∙ cong (flip minᵣ y) (minᵣComm _ _)

max≤-lem : ∀ x x' y → x ≤ᵣ y → x' ≤ᵣ y → maxᵣ x x' ≤ᵣ y
max≤-lem x x' y p p' = ≡→≤ᵣ $
  sym (max-lem _ _ _)
   ∙∙ cong₂ maxᵣ (≤ᵣ→≡ p) (≤ᵣ→≡ p') ∙∙ maxᵣIdem y


opaque
 unfolding _<ᵣ_


 max<-lem : ∀ x x' y → x <ᵣ y → x' <ᵣ y → maxᵣ x x' <ᵣ y
 max<-lem x x' y = PT.map2
   λ ((q , q') , (a , a' , a''))
     ((r , r') , (b , b' , b'')) →
      (ℚ.max q r , ℚ.max q' r') ,
        (max≤-lem x x' (rat (ℚ.max q r))
          (isTrans≤ᵣ x _ _ a (≤ℚ→≤ᵣ _ _ (ℚ.≤max q r)))
          ((isTrans≤ᵣ x' _ _ b (≤ℚ→≤ᵣ _ _ (ℚ.≤max' q r)))) ,
           (ℚ.<MonotoneMax _ _ _ _ a' b' , max≤-lem (rat q') (rat r') _ a'' b''))

 minDistMaxᵣ : ∀ x y y' →
   maxᵣ x (minᵣ y y') ≡ minᵣ (maxᵣ x y) (maxᵣ x y')
 minDistMaxᵣ x y y' = ≡Continuous _ _
    (IsContinuousMaxR _)
    (cont₂minᵣ _ _ (IsContinuousMaxR _) (IsContinuousMaxR _))
    (λ xR →
      ≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuousMaxL (rat xR)) ((IsContinuousMinR y')))
        (IsContinuous∘ _ _ (IsContinuousMinR _) (IsContinuousMaxL (rat xR)))
        (λ yR →
          ≡Continuous _ _
            (IsContinuous∘ _ _ (IsContinuousMaxL (rat xR))
              ((IsContinuousMinL (rat yR))))
            (IsContinuous∘ _ _ (IsContinuousMinL (maxᵣ (rat xR) (rat yR)))
              (IsContinuousMaxL (rat xR)))
            (cong rat ∘ ℚ.minDistMax xR yR ) y')
        y)
    x


≤maxᵣ : ∀ m n →  m ≤ᵣ maxᵣ m n
≤maxᵣ m n = ≡→≤ᵣ $ maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ n) (maxᵣIdem m)

opaque
 unfolding _≤ᵣ_

 ≤min-lem : ∀ x y y' → x ≤ᵣ y → x ≤ᵣ y' →  x ≤ᵣ minᵣ y y'
 ≤min-lem x y y' p p' =
    minDistMaxᵣ x y y' ∙ cong₂ minᵣ p p'


opaque
 unfolding _<ᵣ_


 <min-lem : ∀ x x' y → y <ᵣ x → y <ᵣ x' →  y <ᵣ minᵣ x x'
 <min-lem x x' y = PT.map2
   λ ((q , q') , (a , a' , a''))
     ((r , r') , (b , b' , b'')) →
      (ℚ.min q r , ℚ.min q' r') , ≤min-lem y _ _ a b
         , ℚ.<MonotoneMin _ _ _ _ a' b' ,
             ≤min-lem (rat (ℚ.min q' r')) x x'
              (isTrans≤ᵣ (rat (ℚ.min q' r')) _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤ q' r')) a'')
              (isTrans≤ᵣ (rat (ℚ.min q' r')) _ _ (≤ℚ→≤ᵣ _ _ (ℚ.min≤' q' r')) b'')



maxᵣ₊ : ℝ₊ → ℝ₊ → ℝ₊
maxᵣ₊ (x , 0<x) (y , 0<y) =
 maxᵣ x y , isTrans<≤ᵣ _ _ _ 0<x (≤maxᵣ _ _)


minᵣ₊ : ℝ₊ → ℝ₊ → ℝ₊
minᵣ₊ (x , 0<x) (y , 0<y) =
  minᵣ x y , <min-lem _ _ _ 0<x 0<y

minᵣ₀₊ : ℝ₀₊ → ℝ₀₊ → ℝ₀₊
minᵣ₀₊ (x , 0≤x) (y , 0≤y) =
  minᵣ x y , ≤min-lem _ _ _ 0≤x 0≤y

maxᵣ₀₊ : ℝ₀₊ → ℝ₀₊ → ℝ₀₊
maxᵣ₀₊ (x , 0≤x) (y , 0≤y) =
  maxᵣ x y , isTrans≤ᵣ _ _ _ 0≤x (≤maxᵣ x y)


opaque
 unfolding _≤ᵣ_ absᵣ

 maxAbsorbLMinᵣ : ∀ x y → maxᵣ x (minᵣ x y) ≡ x
 maxAbsorbLMinᵣ x =
   ≡Continuous _ _
     (IsContinuous∘ _ _
       (IsContinuousMaxL x) (IsContinuousMinL x))
       (IsContinuousConst _)
      λ y' →
        ≡Continuous _ _
           (cont₂maxᵣ _ _ IsContinuousId (IsContinuousMinR _))
         IsContinuousId
          (λ x' → cong rat (ℚ.maxAbsorbLMin x' y')) x

 maxDistMin : ∀ x y z → minᵣ x (maxᵣ y z) ≡ maxᵣ (minᵣ x y) (minᵣ x z)

 maxDistMin x y y' =
   ≡Continuous _ _
    (IsContinuousMinR _)
    (cont₂maxᵣ _ _ (IsContinuousMinR _) (IsContinuousMinR _))
    (λ xR →
      ≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuousMinL (rat xR)) ((IsContinuousMaxR y')))
        (IsContinuous∘ _ _ (IsContinuousMaxR _) (IsContinuousMinL (rat xR)))
        (λ yR →
          ≡Continuous _ _
            (IsContinuous∘ _ _ (IsContinuousMinL (rat xR))
              ((IsContinuousMaxL (rat yR))))
            (IsContinuous∘ _ _ (IsContinuousMaxL (minᵣ (rat xR) (rat yR)))
              (IsContinuousMinL (rat xR)))
            (λ r →
              cong rat (ℚ.minComm xR (ℚ.max yR r)  ∙∙
               ℚ.maxDistMin yR r xR ∙∙
                cong₂ ℚ.max (ℚ.minComm yR xR) (ℚ.minComm r xR))) y')
        y)
    x

 min≤ᵣ : ∀ m n → minᵣ m n ≤ᵣ m
 min≤ᵣ m n = maxᵣComm (minᵣ m n) m ∙ maxAbsorbLMinᵣ _ n

 min≤ᵣ' : ∀ m n → minᵣ m n ≤ᵣ n
 min≤ᵣ' m n = subst (_≤ᵣ n) (minᵣComm n m) (min≤ᵣ n m)


 ≤→minᵣ : ∀ m n → m ≤ᵣ n → minᵣ m n ≡ m
 ≤→minᵣ m n p = cong₂ minᵣ (sym (maxᵣIdem m)) (sym p) ∙
   sym (minDistMaxᵣ m m n) ∙ maxAbsorbLMinᵣ m n


 ≤→maxᵣ : ∀ m n → m ≤ᵣ n → maxᵣ m n ≡ n
 ≤→maxᵣ m n p = p


∈ℚintervalℙ→clampᵣ≡ : ∀ a b → ∀ x →
    x ∈ intervalℙ a b → x ≡ clampᵣ a b x
∈ℚintervalℙ→clampᵣ≡ a b x (a≤x , x≤b) =
 sym (≤→minᵣ _ _ x≤b)  ∙ cong (λ y → minᵣ y b) (sym (≤ᵣ→≡ a≤x))


IsContinuous₂ : (ℝ → ℝ → ℝ) → Type
IsContinuous₂ f =
 (∀ x → IsContinuous (f x)) × (∀ x → IsContinuous (flip f x))

cont₂-fst : IsContinuous₂ (λ x _ → x)
cont₂-fst = (λ _ → IsContinuousConst _) , (λ _ → IsContinuousId)

cont₂-snd : IsContinuous₂ (λ _ x → x)
cont₂-snd = (λ _ → IsContinuousId) , (λ _ → IsContinuousConst _)

cont₂-id : ∀ x → IsContinuous₂ (λ _ _ → x)
cont₂-id _ = (λ _ → IsContinuousConst _) , (λ _ → IsContinuousConst _)

asIsContinuous₂-fst : ∀ f
  → IsContinuous f
  → IsContinuous₂ (λ x _ → f x)
asIsContinuous₂-fst f cf = (λ _ → IsContinuousConst _) , λ _ → cf


asIsContinuous₂-snd : ∀ f
  → IsContinuous f
  → IsContinuous₂ (λ _ x → f x)
asIsContinuous₂-snd f cf = (λ _ → cf) , (λ _ → IsContinuousConst _)


≡Cont₂ : {f₀ f₁ : ℝ → ℝ → ℝ}
         → IsContinuous₂ f₀
         → IsContinuous₂ f₁
         → (∀ u u' → f₀ (rat u) (rat u') ≡ f₁ (rat u) (rat u'))
             → ∀ x x' → f₀ x x' ≡ f₁ x x'
≡Cont₂ {f₀} {f₁} (f₀C , f₀C') (f₁C , f₁C') p x =
  ≡Continuous _ _ (f₀C x) (f₁C x)
    (λ q → ≡Continuous _ _ (f₀C' (rat q)) (f₁C' (rat q))
       (λ r → p r q) x)



contNE₂∘ : ∀ {h} → (ne : NonExpanding₂ h)
  {f₀ f₁ : ℝ → ℝ → ℝ}
   → IsContinuous₂ f₀
   → IsContinuous₂ f₁
  → IsContinuous₂ (λ x x' → NonExpanding₂.go ne (f₀ x x') (f₁ x x'))
contNE₂∘ ne x x₁ =
  (λ x₂ → contDiagNE₂ ne _ _ (x .fst x₂) (x₁ .fst x₂)) ,
   λ x₂ → contDiagNE₂ ne _ _ (x .snd x₂) (x₁ .snd x₂)

cont∘₂ : ∀ {g}
  {f : ℝ → ℝ → ℝ}
   → IsContinuous g
   → IsContinuous₂ f
  → IsContinuous₂ (λ x x' → g (f x x'))
cont∘₂ cG (cF , _) .fst x = IsContinuous∘ _ _ cG (cF x)
cont∘₂ cG (_ , cF) .snd x = IsContinuous∘ _ _ cG (cF x)

cont₂∘ :
  {g : ℝ → ℝ → ℝ}
  → ∀ {f f'}
   → IsContinuous₂ g
   → IsContinuous f
   → IsContinuous f'
  → IsContinuous₂ (λ x x' → g (f x) (f' x'))
cont₂∘ (cG , _) _ cF .fst x = IsContinuous∘ _ _ (cG _) cF
cont₂∘ (_ , cG) cF _ .snd x = IsContinuous∘ _ _ (cG _) cF


contNE₂ : ∀ {h} → (ne : NonExpanding₂ h)
  → IsContinuous₂ (NonExpanding₂.go ne)
contNE₂ ne =
  contNE₂∘ ne
   ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousId))
   ((λ _ → IsContinuousId) , (λ _ → IsContinuousConst _))



IsContinuousClamp₂ : ∀ x → IsContinuous₂ λ a b → clampᵣ a b x
IsContinuousClamp₂ x = (λ _ → IsContinuousMinL _) ,
   λ _ → IsContinuous∘ _ _ (IsContinuousMinR _) (IsContinuousMaxR _)

opaque
 unfolding minᵣ
 IsContinuousClamp₂∘ : ∀ {f₀} {f₁} x → IsContinuous₂ f₀ → IsContinuous₂ f₁ →
          IsContinuous₂ λ a b → clampᵣ (f₀ a b) (f₁ a b) x
 IsContinuousClamp₂∘ x =
   contNE₂∘ minR ∘
     (flip (contNE₂∘ maxR) ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousConst _)))

opaque
 unfolding maxᵣ
 IsContinuousClamp₂∘' : ∀ {f₀} {f₁} {f₂} →
          IsContinuous₂ f₀ → IsContinuous₂ f₁ → IsContinuous₂ f₂ →
          IsContinuous₂ λ a b → clampᵣ (f₀ a b) (f₁ a b) (f₂ a b)
 IsContinuousClamp₂∘' f₀C f₁C f₂C =
   contNE₂∘ minR (contNE₂∘ maxR f₀C f₂C) f₁C


opaque
 unfolding _+ᵣ_
 IsContinuous-₂∘ : ∀ {f₀} {f₁} → IsContinuous₂ f₀ → IsContinuous₂ f₁ →
      IsContinuous₂ λ a b → (f₀ a b) -ᵣ (f₁ a b)
 IsContinuous-₂∘ f₀C f₁C =
  contNE₂∘ sumR f₀C
    (cont∘₂ IsContinuous-ᵣ f₁C)




opaque
 unfolding _≤ᵣ_

 ≤Cont₂ : {f₀ f₁ : ℝ → ℝ → ℝ}
          → IsContinuous₂ f₀
          → IsContinuous₂ f₁
          → (∀ u u' → f₀ (rat u) (rat u') ≤ᵣ f₁ (rat u) (rat u'))
              → ∀ x x' → f₀ x x' ≤ᵣ f₁ x x'
 ≤Cont₂ f₀C f₁C =
   (≡Cont₂ (contNE₂∘ maxR f₀C f₁C) f₁C)




 ≤Cont : {f₀ f₁ : ℝ → ℝ}
          → IsContinuous f₀
          → IsContinuous f₁
          → (∀ u → f₀ (rat u) ≤ᵣ f₁ (rat u))
              → ∀ x → f₀ x ≤ᵣ f₁ x
 ≤Cont f₀C f₁C =
   ≡Continuous _ _ (contDiagNE₂ maxR _ _ f₀C f₁C ) f₁C

 ≤Cont₂Pos : {f₀ f₁ : ℝ → ℝ → ℝ}
          → IsContinuous₂ f₀
          → IsContinuous₂ f₁
          → (∀ u u' → 0 ℚ.≤ u → 0 ℚ.≤ u' → f₀ (rat u) (rat u') ≤ᵣ f₁ (rat u) (rat u'))
              → ∀ x x' → 0 ≤ᵣ x → 0 ≤ᵣ x' → f₀ x x' ≤ᵣ f₁ x x'
 ≤Cont₂Pos {f₀} {f₁} f₀C f₁C X x x' 0≤x 0≤x' =
   subst2 (λ x x' → f₀ x x' ≤ᵣ f₁ x x') 0≤x 0≤x'
     (≤Cont₂
       (cont₂∘ f₀C (IsContinuousMaxL 0) (IsContinuousMaxL 0))
       (cont₂∘ f₁C (IsContinuousMaxL 0) (IsContinuousMaxL 0))
         (λ u u' → (X _ _ (ℚ.≤max 0 u) (ℚ.≤max 0 u')))
          x x')



 ≤ContPos' : {x₀ : ℚ} {f₀ f₁ : ℝ → ℝ}
          → IsContinuous f₀
          → IsContinuous f₁
          → (∀ u → x₀ ℚ.≤ u → f₀ (rat u) ≤ᵣ f₁ (rat u) )
              → ∀ x → rat x₀ ≤ᵣ x → f₀ x ≤ᵣ f₁ x
 ≤ContPos' {x₀} {f₀} {f₁} f₀C f₁C X x 0≤x =
   subst (λ x → f₀ x  ≤ᵣ f₁ x) 0≤x
     (≤Cont
       (IsContinuous∘ _ _  f₀C (IsContinuousMaxL (rat x₀)))
       (IsContinuous∘ _ _ f₁C (IsContinuousMaxL (rat x₀)))
         (λ u  → (X _ (ℚ.≤max x₀ u)))
          x)




 -- ≤ContPos'pred : {x₀ : ℚ} {f₀ f₁ : ∀ x → (rat x₀ ≤ᵣ x) → ℝ}
 --          → IsContinuousWithPred (λ _ → _ , isProp≤ᵣ _ _) f₀
 --          → IsContinuousWithPred (λ _ → _ , isProp≤ᵣ _ _) f₁
 --          → (∀ u x₀<u → f₀ (rat u) (≤ℚ→≤ᵣ _ _ x₀<u)
 --                 ≤ᵣ f₁ (rat u) (≤ℚ→≤ᵣ _ _ x₀<u) )
 --              → ∀ x x₀≤x → f₀ x x₀≤x ≤ᵣ f₁ x x₀≤x
 -- ≤ContPos'pred {x₀} {f₀} {f₁} f₀C f₁C X x 0≤x =
 --   subst (λ (x , x₀≤x) → f₀ x ?  ≤ᵣ f₁ x ?) -- ? x₀≤x
 --      (Σ≡Prop (λ _ → isSetℝ _ _) ?) -- ?
 --     (≤Cont
 --       (IsContinuousWithPred∘IsContinuous _ _ _
 --          (λ _ → ≤maxᵣ _ _) f₀C (IsContinuousMaxL (rat x₀)))
 --       (IsContinuousWithPred∘IsContinuous _ _ _
 --          (λ _ → ≤maxᵣ _ _) f₁C (IsContinuousMaxL (rat x₀)))
 --          (λ u  →
 --              subst (λ qq → f₀ (maxᵣ (rat x₀) (rat u)) qq
 --                      ≤ᵣ f₁ (maxᵣ (rat x₀) (rat u)) qq)
 --                 (?) ?) x) -- (X (ℚ.max x₀ u) (ℚ.≤max _ _))




 <→≤ContPos' : {x₀ : ℚ} {f₀ f₁ : ℝ → ℝ}
          → IsContinuous f₀
          → IsContinuous f₁
          → (∀ u → x₀ ℚ.< u → f₀ (rat u) ≤ᵣ f₁ (rat u) )
              → ∀ x → rat x₀ <ᵣ x → f₀ x ≤ᵣ f₁ x
 <→≤ContPos' {x₀} {f₀} {f₁} f₀C f₁C X x =
    PT.rec (isSetℝ _ _)
      λ ((q , q') , (x₀≤q , q<q' , q'≤x)) →
        ≤ContPos' {q'} f₀C f₁C
              ((_∘ ℚ.isTrans<≤ _ _ _
                (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ _ _ x₀≤q) q<q'))
                ∘ X ) x q'≤x



IsContinuousWithPred⊆ : ∀ (P P' : ℝ → hProp ℓ-zero) f
                       → (P'⊆P : P' ⊆ P)
                       → IsContinuousWithPred P f
                       → IsContinuousWithPred P' ((_∘ P'⊆P _) ∘ f )
IsContinuousWithPred⊆ P P' f P'⊆P X u ε u∈P =
  PT.map (map-snd ((_∘ P'⊆P _) ∘_))
   (X u ε (P'⊆P _ u∈P))

-- opaque
--  unfolding _<ᵣ_
--  <→≤ContPos'pred : {x₀ : ℚ} {f₀ f₁ : ∀ x → (rat x₀ <ᵣ x) → ℝ}
--           → IsContinuousWithPred (λ _ → _ , isProp<ᵣ _ _) f₀
--           → IsContinuousWithPred (λ _ → _ , isProp<ᵣ _ _) f₁
--           → (∀ u x₀<u → f₀ (rat u) x₀<u
--                      ≤ᵣ f₁ (rat u) x₀<u )
--               → ∀ x x₀<x → f₀ x x₀<x ≤ᵣ f₁ x x₀<x
--  <→≤ContPos'pred {x₀} {f₀} {f₁} f₀C f₁C X x =
--     PT.elim (λ _ → isSetℝ _ _)
--       λ ((q , q') , (x₀≤q , q<q' , q'≤x)) →
--        let z = ≤ContPos'pred {q'}
--                 (IsContinuousWithPred⊆ _ _ f₀
--                    (λ  _ → isTrans<≤ᵣ _ _ _
--                   ((<ℚ→<ᵣ _ _ (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ x₀ q x₀≤q) q<q'))))
--                    f₀C)
--                  (IsContinuousWithPred⊆ _ _ f₁
--                    (λ  _ → isTrans<≤ᵣ _ _ _
--                   ((<ℚ→<ᵣ _ _ (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ x₀ q x₀≤q) q<q'))))
--                    f₁C)
--                  (λ u _ → X u _)
--                        x q'≤x
--       in subst (λ x₀<x → f₀ x x₀<x  ≤ᵣ f₁ x x₀<x)
--              (squash₁ _ _) z



≤ContPos : {f₀ f₁ : ℝ → ℝ}
         → IsContinuous f₀
         → IsContinuous f₁
         → (∀ u → 0 ℚ.≤ u → f₀ (rat u) ≤ᵣ f₁ (rat u) )
             → ∀ x → 0 ≤ᵣ x → f₀ x ≤ᵣ f₁ x
≤ContPos = ≤ContPos' {0}


ℚabs-min-max : ∀ u v →
      ℚ.abs (ℚ.max u v ℚ.- ℚ.min u v) ≡ ℚ.abs (u ℚ.- v)
ℚabs-min-max = ℚ.elimBy≤
  (λ x y X →
    (cong ℚ.abs (cong₂ ℚ._-_ (ℚ.maxComm y x) (ℚ.minComm y x)))
       ∙∙ X ∙∙
      ℚ.absComm- x y)
  λ x y x≤y →
    cong ℚ.abs
      (cong₂ ℚ._-_
        (ℚ.≤→max _ _ x≤y) (ℚ.≤→min _ _ x≤y))
     ∙ ℚ.absComm- y x

opaque
 unfolding absᵣ
 absᵣ-min-max : ∀ u v →
       absᵣ (maxᵣ u v -ᵣ minᵣ u v) ≡ absᵣ (u -ᵣ v)
 absᵣ-min-max =
  ≡Cont₂
    (cont∘₂ IsContinuousAbsᵣ
     (contNE₂∘ sumR
       (contNE₂ maxR)
       (cont∘₂ IsContinuous-ᵣ (contNE₂ minR) )))
    (cont∘₂ IsContinuousAbsᵣ
     (cont₂∘ (contNE₂ sumR)
       IsContinuousId IsContinuous-ᵣ))
    λ u v →
       cong rat (sym (ℚ.abs'≡abs ((ℚ.max u v ℚ.- ℚ.min u v))) ∙∙ ℚabs-min-max u v ∙∙
         ℚ.abs'≡abs (u ℚ.- v))

opaque
 unfolding maxᵣ
 maxMonotoneᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s → maxᵣ m o ≤ᵣ maxᵣ n s
 maxMonotoneᵣ m n o s m≤n o≤s =
   max≤-lem _ _ _
     (isTrans≤ᵣ _ _ _ m≤n (≤maxᵣ _ _))
     (isTrans≤ᵣ _ _ _ o≤s
       (isTrans≤≡ᵣ _ _ _  (≤maxᵣ _ n) ((maxᵣComm s n)) ))

opaque
 unfolding minᵣ
 minMonotoneᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s → minᵣ m o ≤ᵣ minᵣ n s
 minMonotoneᵣ m n o s m≤n o≤s =
   ≤min-lem _ _ _
     (isTrans≤ᵣ _ _ _
      (min≤ᵣ _ _) m≤n)
     (isTrans≤ᵣ _ _ _
      (isTrans≡≤ᵣ _ _ _ (minᵣComm m o) (min≤ᵣ _ m)) o≤s)

opaque
 unfolding _≤ᵣ_ absᵣ
 incr→max≤ : (f : ∀ x → 0 <ᵣ x → ℝ)
        → (∀ x 0<x y 0<y → x ≤ᵣ y → f x 0<x ≤ᵣ f y 0<y)
       → ∀ u v 0<u 0<v →
          maxᵣ (f u 0<u) (f v 0<v)
            ≤ᵣ  (f (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v))))
 incr→max≤ f incr u v 0<u 0<v =
   isTrans≤≡ᵣ (maxᵣ (f u 0<u) (f v 0<v)) _ _
     (maxMonotoneᵣ (f u 0<u) _ (f v 0<v) _
       (incr u 0<u (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v)))
        (≤maxᵣ u v))
       (incr v 0<v (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v)))
        (isTrans≤≡ᵣ v _ _  (≤maxᵣ v u) (maxᵣComm v u))))
     (maxᵣIdem _)

opaque
 unfolding minᵣ
 incr→≤min : (f : ∀ x → 0 <ᵣ x → ℝ)
        → (∀ x 0<x y 0<y → x ≤ᵣ y → f x 0<x ≤ᵣ f y 0<y)
       → ∀ u v 0<u 0<v →
            (f (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v))))
             ≤ᵣ  minᵣ (f u 0<u) (f v 0<v)
 incr→≤min f incr u v 0<u 0<v =
   isTrans≡≤ᵣ _ _ _
     (sym (minᵣIdem _))
      (minMonotoneᵣ _ _ _ _
        (incr (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v)))
            u 0<u
           (min≤ᵣ _ _))
        (incr (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v)))
            v 0<v
           (isTrans≡≤ᵣ _ _ _  (minᵣComm u v) (min≤ᵣ _ u))))

absᵣ-monotoneOnNonNeg : (x y : ℝ₀₊) →
 fst x ≤ᵣ fst y → absᵣ (fst x) ≤ᵣ absᵣ (fst y)
absᵣ-monotoneOnNonNeg x y x≤y =
  subst2 _≤ᵣ_
    (sym (absᵣNonNeg (fst x) (snd x)))
    (sym (absᵣNonNeg (fst y) (snd y)))
    x≤y



ℚApproxℙ : (P : ℙ ℝ) (Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ P Q f =
   Σ[ f' ∈ (∀ q → rat q ∈ P → ℚ₊ → ℚ) ]
    (((∀ q q∈ ε  → rat (f' q q∈ ε) ∈ Q)) × (Σ[ f'-cauchy ∈ (∀ q q∈P → _) ]
      (∀ q q∈P → lim (rat ∘ f' q q∈P) (f'-cauchy q q∈P)
                ≡ fst (f (rat q) q∈P))))

ℚApprox : (f : ℝ → ℝ) → Type
ℚApprox f =
   Σ[ f' ∈ (ℚ → ℚ₊ → ℚ) ]
    Σ[ f'-cauchy ∈ (∀ q → _) ]
      (∀ q → lim (rat ∘ f' q) (f'-cauchy q)
                ≡ f (rat q))


ℚApproxℙ'Num : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) →
   ∀ q → (q∈P : rat q ∈ P) → Type

ℚApproxℙ'Num P Q f q q∈P =
     Σ[ f' ∈ (ℚ₊ → ℚ) ]
    ((∀ ε  → rat (f' ε) ∈ Q) × (Σ[ f'-cauchy ∈ (_) ]
      (lim (rat ∘ f') (f'-cauchy) ≡ fst (f (rat q) q∈P))))


ℚApproxℙ' : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ' P Q f =
 ∀ q → (q∈P : rat q ∈ P) →
   ℚApproxℙ'Num P Q f q q∈P

Iso-ℚApproxℙ'-ℚApproxℙ : (P Q : ℙ ℝ) → ∀ f →
  Iso (ℚApproxℙ' P Q f) (ℚApproxℙ P Q f)
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.fun x =
  (λ q → fst ∘ x q) ,
   (λ q → fst ∘ snd ∘ x q) ,
    ((λ q → fst ∘ snd ∘ snd ∘ x q) ,
    (λ q → snd ∘ snd ∘ snd ∘ x q))
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.inv = _
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.rightInv _ = refl
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.leftInv _ = refl


ℚApproxℙ'≃ℚApproxℙ : (P Q : ℙ ℝ) → ∀ f →
  ℚApproxℙ' P Q f ≃ ℚApproxℙ P Q f
ℚApproxℙ'≃ℚApproxℙ P Q f =
 isoToEquiv (Iso-ℚApproxℙ'-ℚApproxℙ P Q f)



IsUContinuousℚℙ : (P : ℙ ℝ) → (∀ q → rat q ∈ P → ℝ) → Type
IsUContinuousℚℙ P f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ u v u∈ v∈ → ℚ.abs (u ℚ.- v) ℚ.< fst δ  → f u u∈ ∼[ ε ] f v v∈)

IsUContinuousℙ : (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsUContinuousℙ P f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ u v u∈ v∈ → u ∼[ δ ] v  → f u u∈ ∼[ ε ] f v v∈)


ℚApproxℙ'' : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ'' P Q f =
 ∀ x → (x∈P : rat x ∈ P) (ε : ℚ₊) →
    Σ[ r ∈ ℚ ] ((rat r ∈ Q) × (rat r ∼[ ε ] fst (f (rat x) x∈P)))

ℚApproxℙ'→ℚApproxℙ'' : (P Q : ℙ ℝ) → ∀ f →
  (ℚApproxℙ' P Q f) → (ℚApproxℙ'' P Q f)
ℚApproxℙ'→ℚApproxℙ'' P Q f X x x∈P ε =
   fst (X x x∈P) (/2₊ ε) , fst (snd (X x x∈P)) (/2₊ ε) ,
     subst (rat (fst (X x x∈P) (/2₊ ε)) ∼[ ε ]_)
    (snd (snd (snd ( ((X x x∈P))) )))
      ((rat-lim _ _ _ (/2₊ ε) _ (snd (ℚ.<→ℚ₊ _ _ (ℚ.x/2<x ε)))
        (refl∼ _ _)))


ℚApproxℙ∘ : ∀ P Q R g f
          → IsUContinuousℙ Q ((fst ∘_) ∘ g)
          → ℚApproxℙ'' Q R g
          → ℚApproxℙ'' P Q f
          → ℚApproxℙ'' P R (curry (uncurry g ∘ uncurry f))
ℚApproxℙ∘ P Q R  g f gC gA fA q q∈ ε =
  let (δ' , Δ) = gC (/2₊ ε)
      δ = ℚ.min₊ δ' (/2₊ ε)

      uu' : rat (fst (fA q q∈ δ)) ∈ Q
      uu' = (fst (snd (fA q q∈ δ)))

      zz : rat (fst (gA (fst (fA q q∈ δ)) uu' δ))
             ∼[ /2₊ ε ℚ₊+ /2₊ ε ]
              fst (g (fst (f (rat q) q∈)) (snd (f (rat q) q∈)))
      zz = triangle∼
               ((∼-monotone≤ (ℚ.min≤' (gC (/2₊ ε) .fst .fst) _)
                 ((snd (snd (gA (fst (fA q q∈ δ)) uu' δ))))))

                   (Δ _ _ uu' _ (
                     ∼-monotone≤ (ℚ.min≤ _ _)
                       (snd (snd (fA q q∈ δ)))))

  in fst (gA (fst (fA q q∈ δ)) uu' δ)
        , fst (snd (gA (fst (fA q q∈ δ)) uu' δ))
         , subst∼ (ℚ.ε/2+ε/2≡ε (fst ε)) zz

≡ContinuousWithPred : ∀ P P' → ⟨ openPred P ⟩ → ⟨ openPred P' ⟩ → ∀ f g
  → IsContinuousWithPred P  f
  → IsContinuousWithPred P' g
  → (∀ r r∈ r∈' → f (rat r) r∈  ≡ g (rat r) r∈')
  → ∀ u u∈ u∈' → f u u∈ ≡ g u u∈'
≡ContinuousWithPred P P' oP oP' f g fC gC e = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop
       (λ z → (u∈ : ⟨ P z ⟩) (u∈' : ⟨ P' z ⟩) → f z u∈ ≡ g z u∈')
 w .Elimℝ-Prop.ratA = e
 w .Elimℝ-Prop.limA x p R x∈ x∈' = PT.rec2 (isSetℝ _ _)
  (λ (Δ , PΔ) (Δ' , PΔ') → eqℝ _ _ λ ε₀ →
   let ε = ε₀
       f' = fC (lim x p) (ℚ./2₊ ε) x∈
       g' = gC (lim x p) (ℚ./2₊ ε) x∈'
   in PT.rec2
       (isProp∼ _ _ _)
        (λ (θ , θ∼) (η , η∼) →
         let δ = ℚ./2₊ (ℚ.min₊ (ℚ.min₊ Δ Δ') (ℚ.min₊ θ η))
             limX∼x = sym∼ _ _ _ (𝕣-lim-self x p δ δ)
             xδ∈P : ⟨ P (x δ) ⟩
             xδ∈P = PΔ (x δ)
                     (∼-monotone≤
                       (((subst (ℚ._≤ fst Δ)
                        (sym (ℚ.ε/2+ε/2≡ε
                          (fst ((ℚ.min₊
                           (ℚ.min₊ (Δ) (Δ')) (ℚ.min₊ θ η))))))
                       (ℚ.isTrans≤ _ _ _ ((ℚ.min≤
                          (fst (ℚ.min₊ (Δ) (Δ'))) (fst (ℚ.min₊ θ η)))
                           ) (ℚ.min≤ (fst Δ) (fst Δ'))))))
                       limX∼x)
             xδ∈P' : ⟨ P' (x δ) ⟩
             xδ∈P' = PΔ' (x δ)
                     (∼-monotone≤ ((((subst (ℚ._≤ fst Δ')
                        (sym (ℚ.ε/2+ε/2≡ε
                          (fst ((ℚ.min₊
                           (ℚ.min₊ (Δ) (Δ')) (ℚ.min₊ θ η))))))
                       (ℚ.isTrans≤ _ _ _ ((ℚ.min≤
                          (fst (ℚ.min₊ (Δ) (Δ'))) (fst (ℚ.min₊ θ η)))
                           ) (ℚ.min≤' (fst Δ) (fst Δ'))))))) limX∼x)
             zF : f (lim x p) x∈ ∼[ ℚ./2₊ ε ] g (x δ) xδ∈P'
             zF = subst (f (lim x p) x∈ ∼[ ℚ./2₊ ε ]_)
                  (R _ xδ∈P xδ∈P')
                 (θ∼ _ _ (∼-monotone≤
                    ((subst (ℚ._≤ fst θ)
                        (sym (ℚ.ε/2+ε/2≡ε
                          (fst ((ℚ.min₊
                           (ℚ.min₊ (Δ) (Δ')) (ℚ.min₊ θ η))))))
                       (ℚ.isTrans≤ _ _ _ ((ℚ.min≤'
                          (fst (ℚ.min₊ (Δ) (Δ'))) (fst (ℚ.min₊ θ η)))
                           ) (ℚ.min≤ (fst θ) (fst η)))))
                  (sym∼ _ _ _ ((𝕣-lim-self x p δ δ)))))
             zG : g (lim x p) x∈'  ∼[ ℚ./2₊ ε ] g (x δ) xδ∈P'
             zG = η∼ _ _
                   (∼-monotone≤
                        ((subst (ℚ._≤ fst η)
                        (sym (ℚ.ε/2+ε/2≡ε
                          (fst ((ℚ.min₊
                           (ℚ.min₊ (Δ) (Δ')) (ℚ.min₊ θ η))))))
                       (ℚ.isTrans≤ _ _ _ ((ℚ.min≤'
                          (fst (ℚ.min₊ (Δ) (Δ'))) (fst (ℚ.min₊ θ η)))
                           ) (ℚ.min≤' (fst θ) (fst η)))))

                  (sym∼ _ _ _ ((𝕣-lim-self x p δ δ))))
             zz = subst∼ ((ℚ.ε/2+ε/2≡ε (fst ε))) (triangle∼ zF (sym∼ _ _ _ zG))
         in  zz)
        f' g') (oP (lim x p) x∈) (oP' (lim x p) x∈')

 w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isSetℝ _ _



opaque
 unfolding minᵣ
 ≤clampᵣ : ∀ L L' x → L ≤ᵣ L' →  L ≤ᵣ clampᵣ L L' x
 ≤clampᵣ L L' x y =
   isTrans≤≡ᵣ _ _ _ (≤maxᵣ L (minᵣ x L'))
     (cong₂ maxᵣ (sym (≤→minᵣ _ _ y) ∙ minᵣComm L L') (minᵣComm x L' )
      ∙∙ sym (maxDistMin L' L x) ∙∙
      minᵣComm L' (maxᵣ L x) )


clamp≤ᵣ : ∀ L L' x →  clampᵣ L L' x ≤ᵣ L'
clamp≤ᵣ L L' x = min≤ᵣ' _ _


<ᵣ-ᵣ : ∀ x y → -ᵣ y <ᵣ -ᵣ x →  x <ᵣ y
<ᵣ-ᵣ x y = subst2 _<ᵣ_ (-ᵣInvol x) (-ᵣInvol y) ∘ -ᵣ<ᵣ (-ᵣ y) (-ᵣ x)


sym-intervalℙ⊆ointervalℙ : ∀ a b → a <ᵣ b →
  intervalℙ (-ᵣ a) a ⊆ ointervalℙ (-ᵣ b) b
sym-intervalℙ⊆ointervalℙ a b a<b =
 intervalℙ⊆ointervalℙ _ _ _ _ (-ᵣ<ᵣ _ _ a<b) a<b

