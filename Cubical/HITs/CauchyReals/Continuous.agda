{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Continuous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)


open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊)

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order


0≤absᵣ : ∀ x → 0 ≤ᵣ absᵣ x
0≤absᵣ = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop (λ z → 0 ≤ᵣ absᵣ z)
 w .Elimℝ-Prop.ratA q = ≤ℚ→≤ᵣ 0 (ℚ.abs' q)
   (subst (0 ℚ.≤_) (ℚ.abs'≡abs q) (ℚ.0≤abs q))
 w .Elimℝ-Prop.limA x p x₁ =
  let y0 = _
      zz0 = NonExpanding₂.β-rat-lim maxR 0 (λ q → (absᵣ (x (ℚ.invℚ₊ 1 ℚ₊· q))))
               y0 _

      zz = sym (congLim' _ _ _
                λ q →
                   sym $ x₁ (ℚ.invℚ₊ ([ pos 1 / (1+ 0) ] , tt) ℚ₊· q))
  in _∙_ {x = maxᵣ 0 (lim (λ q → (absᵣ (x (ℚ.invℚ₊ 1 ℚ₊· q)))) y0)}
       zz0 zz

 w .Elimℝ-Prop.isPropA _ = isSetℝ _ _


-ᵣInvol : ∀ x → -ᵣ (-ᵣ x) ≡ x
-ᵣInvol = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop _
 w .Elimℝ-Prop.ratA x = cong rat (ℚ.-Invol x)
 w .Elimℝ-Prop.limA x p x₁ =
   congLim _ _ _ _
     λ q → x₁ _ ∙ cong x (ℚ₊≡ (λ i → ℚ.·IdL (ℚ.·IdL (fst q) i) i))
 w .Elimℝ-Prop.isPropA x = isSetℝ (-ᵣ (-ᵣ x)) x


-ᵣDistr : ∀ x y → -ᵣ (x +ᵣ y) ≡ (-ᵣ x) +ᵣ (-ᵣ y)
-ᵣDistr = Elimℝ-Prop2Sym.go w
 where
 w : Elimℝ-Prop2Sym (λ z z₁ → (-ᵣ (z +ᵣ z₁)) ≡ ((-ᵣ z) +ᵣ (-ᵣ z₁)))
 w .Elimℝ-Prop2Sym.rat-ratA r q = cong rat (ℚ.-Distr r q)
 w .Elimℝ-Prop2Sym.rat-limA r x y x₁ =
   cong (-ᵣ_) (snd (NonExpanding₂.β-rat-lim' sumR r x y))
    ∙ fromLipshitzNEβ _ _ (λ q → (rat r) +ᵣ (x q))
         (fst (NonExpanding₂.β-rat-lim' sumR r x y))
    ∙  (congLim _ _ _ _ λ q → x₁ _ ∙
      cong (λ q' → (-ᵣ rat r) +ᵣ (-ᵣ x q')) (sym (ℚ₊≡ $ ℚ.·IdL _)))
    ∙ cong ((rat (ℚ.- r)) +ᵣ_) (sym (fromLipshitzNEβ _ _ x y))

 w .Elimℝ-Prop2Sym.lim-limA x y x' y' x₁ =
    cong (-ᵣ_) (snd (NonExpanding₂.β-lim-lim/2 sumR x y x' y'))  ∙
     fromLipshitzNEβ _ _ (λ q → (x (ℚ./2₊ q)) +ᵣ (x' (ℚ./2₊ q)))
      (fst (NonExpanding₂.β-lim-lim/2 sumR x y x' y')) ∙
     congLim _ _ _ _ (λ q → x₁ _ _)
     ∙ sym (snd (NonExpanding₂.β-lim-lim/2 sumR _ _ _ _))
      ∙ cong₂ _+ᵣ_ (sym (fromLipshitzNEβ _ _ x y))
           ((sym (fromLipshitzNEβ _ _ x' y')))
 w .Elimℝ-Prop2Sym.isSymA x y p =
  cong (-ᵣ_) (+ᵣComm y x)
   ∙∙ p  ∙∙
    +ᵣComm (-ᵣ x) (-ᵣ y)
 w .Elimℝ-Prop2Sym.isPropA x y = isSetℝ (-ᵣ (x +ᵣ y)) ((-ᵣ x) +ᵣ (-ᵣ y))

-absᵣ : ∀ x → absᵣ x ≡ absᵣ (-ᵣ x)
-absᵣ = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop _
 w .Elimℝ-Prop.ratA x = cong rat (ℚ.-abs' x)
 w .Elimℝ-Prop.limA x p x₁ =
  let yy = _
  in congLim  (λ v₁ →
                  Elimℝ.go
                  yy
                  (x (ℚ.invℚ₊ 1 ℚ₊· v₁))) _
                  (λ x₂ → Elimℝ.go yy
                            (Elimℝ.go
                             _
                             (x (1 ℚ₊· (1 ℚ₊· x₂))))) _
      λ q → _∙_ {y = Elimℝ.go yy (x (1 ℚ₊· (1 ℚ₊· q)))}
       (cong (Elimℝ.go yy ∘ x) ((ℚ₊≡ (sym (ℚ.·IdL _)))) ) (x₁ _)

 w .Elimℝ-Prop.isPropA x = isSetℝ (absᵣ x) (absᵣ (-ᵣ x))



-[x-y]≡y-x : ∀ x y → -ᵣ ( x +ᵣ (-ᵣ y) ) ≡ y +ᵣ (-ᵣ x)
-[x-y]≡y-x x y =
     -ᵣDistr x (-ᵣ y)
     ∙ λ i → +ᵣComm (-ᵣ x) (-ᵣInvol y i) i


minusComm-absᵣ : ∀ x y → absᵣ (x +ᵣ (-ᵣ y)) ≡ absᵣ (y +ᵣ (-ᵣ x))
minusComm-absᵣ x y = -absᵣ _ ∙ cong absᵣ (-[x-y]≡y-x x y)


open ℚ.HLP

-- HoTT Lemma (11.3.41)

denseℚinℝ : ∀ u v → u <ᵣ v → ∃[ q ∈ ℚ ] ((u <ᵣ rat q) × (rat q <ᵣ v))
denseℚinℝ u v =
  PT.map λ ((u , v) , (z , (z' , z''))) →
            u ℚ.+ ((v ℚ.- u) ℚ.· [ 1 / 2 ]) ,
              ∣ (u , u ℚ.+ ((v ℚ.- u) ℚ.· [ 1 / 4 ]))
                , (z , ((
                     let zz' = ℚ.<-·o u v [ pos 1 / 1+ 3 ]
                                (ℚ.0<→< [ pos 1 / 1+ 3 ] _ ) z'

                     in subst (ℚ._<
                              u ℚ.+ (v ℚ.- u) ℚ.· [ pos 1 / 1+ 3 ])
                               (cong (u ℚ.+_)
                                 (ℚ.·AnnihilL [ pos 1 / 1+ 3 ]) ∙ ℚ.+IdR u) $
                           ℚ.≤<Monotone+ u u ([ pos 0 / 1+ 0 ]
                              ℚ.· [ pos 1 / 1+ 3 ])
                           ((v ℚ.- u) ℚ.· [ pos 1 / 1+ 3 ])
                             (ℚ.isRefl≤ u) (
                              ℚ.<-·o 0 (v ℚ.- u)
                                 [ pos 1 / 1+ 3 ]
                                  (ℚ.decℚ<? {0} {[ pos 1 / 1+ 3 ]})
                                   (ℚ.<→<minus u v z')))
                    , ≤ℚ→≤ᵣ _ _
                       (ℚ.≤-o+
                         ((v ℚ.- u) ℚ.· [ pos 1 / 1+ 3 ])
                         ((v ℚ.- u) ℚ.· [ pos 1 / 1+ 1 ])
                          u (ℚ.≤-o· [ pos 1 / 1+ 3 ]
                             [ pos 1 / 1+ 1 ] (v ℚ.- u)
                              (ℚ.0≤ℚ₊ (ℚ.<→ℚ₊ u v z'))
                               (ℚ.decℚ≤? {[ pos 1 / 1+ 3 ]}
                                          {[ pos 1 / 1+ 1 ]}))))) ∣₁
                , ∣ (v ℚ.- ((v ℚ.- u) ℚ.· [ 1 / 4 ]) , v) ,
                  (≤ℚ→≤ᵣ _ _
                     (subst
                       {x = (u ℚ.+ (v ℚ.- u) ℚ.· [ pos 3 / 1+ 3 ])}
                       {(v ℚ.- ((v ℚ.- u) ℚ.· [ pos 1 / 1+ 3 ]))}
                       (u ℚ.+ (v ℚ.- u) ℚ.· [ pos 1 / 1+ 1 ] ℚ.≤_)
                        ((cong (u ℚ.+_) (ℚ.·DistR+ _ _ _ ∙ ℚ.+Comm _ _)
                          ∙ ℚ.+Assoc _ _ _) ∙∙
                            (cong₂ ℚ._+_
                              distℚ! u ·[
                               (ge1 +ge ((neg-ge ge1) ·ge
                                        ge[ [ pos 3 / 1+ 3 ] ]))
                                     ≡ (neg-ge ((neg-ge ge1) ·ge
                                        ge[ [ pos 1 / 1+ 3 ] ]))   ]
                             distℚ! v ·[ (( ge[ [ pos 3 / 1+ 3 ] ]))
                                     ≡ (ge1 +ge neg-ge (
                                        ge[ [ pos 1 / 1+ 3 ] ]))   ])
                            ∙∙ (ℚ.+Comm _ _ ∙ sym (ℚ.+Assoc v
                                   (ℚ.- (v ℚ.· [ 1 / 4 ]))
                                    (ℚ.- ((ℚ.- u) ℚ.· [ 1 / 4 ])))
                              ∙ cong (ℚ._+_ v)
                                  (sym (ℚ.·DistL+ -1 _ _)) ∙ cong (ℚ._-_ v)
                             (sym (ℚ.·DistR+ v (ℚ.- u) [ 1 / 4 ])) ))
                         (ℚ.≤-o+
                           ((v ℚ.- u) ℚ.· [ pos 1 / 1+ 1 ])
                           ((v ℚ.- u) ℚ.· [ pos 3 / 1+ 3 ]) u
                            (ℚ.≤-o· [ pos 1 / 1+ 1 ] [ pos 3 / 1+ 3 ]
                              (v ℚ.- u) ((ℚ.0≤ℚ₊ (ℚ.<→ℚ₊ u v z')))
                                ((ℚ.decℚ≤? {[ pos 1 / 1+ 1 ]}
                                          {[ pos 3 / 1+ 3 ]})))
                                  )) , (
                   subst ((v ℚ.- ((v ℚ.- u) ℚ.· [ pos 1 / 1+ 3 ])) ℚ.<_)
                    (ℚ.+IdR v) (ℚ.<-o+ (ℚ.- ((v ℚ.- u) ℚ.· [ 1 / 4 ])) 0 v
                       (ℚ.-ℚ₊<0 (ℚ.<→ℚ₊ u v z' ℚ₊· ([ pos 1 / 1+ 3 ] , _)))) , z'')) ∣₁



-- 11.3.42




∼→≤ : ∀ u q → u ≤ᵣ (rat q) → ∀ v ε → u ∼'[ ε ] v → v ≤ᵣ rat (q ℚ.+ fst ε)
∼→≤ u q u≤q v ε u∼v =
 let maxLip : ((rat q)) ∼[ ε ] maxᵣ v ((rat q))
     maxLip =
         subst (_∼[ ε ] maxᵣ v ((rat q)))
           u≤q $ NonExpanding₂.go∼L maxR ((rat q)) u v ε (∼'→∼ _ _ _ u∼v)
     zzz = ∼→≤-rat-u q q (≤ᵣ-refl (rat q)) (maxᵣ v ((rat q))) ε (∼→∼' _ _ _ maxLip)
 in cong (maxᵣ v ∘ rat) (sym (ℚ.≤→max q (q ℚ.+ fst ε)
          (ℚ.≤+ℚ₊ q q ε (ℚ.isRefl≤ q )))) ∙∙
     (maxᵣAssoc v (rat q) (rat (q ℚ.+ fst ε)))  ∙∙  zzz
 where

 ∼→≤-rat-u : ∀ u q → rat u ≤ᵣ (rat q) → ∀  v ε
             → rat u ∼'[ ε ] v → v ≤ᵣ rat (q ℚ.+ fst ε)
 ∼→≤-rat-u r q u≤q = Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop _
  w .Elimℝ-Prop.ratA x ε (u , v) = ≤ℚ→≤ᵣ _ _
    (subst (ℚ._≤ q ℚ.+ fst ε) lem--05 $ ℚ.≤Monotone+ r q (x ℚ.- r) (fst ε)
      (≤ᵣ→≤ℚ r q u≤q)
      (ℚ.<Weaken≤ _ _ (ℚ.minus-<'  (fst ε) (x ℚ.- r)
      $ subst ((ℚ.- fst ε) ℚ.<_) (sym (ℚ.-[x-y]≡y-x x r)) u)))
  w .Elimℝ-Prop.limA x y x₁ ε =
       PT.rec (isProp≤ᵣ _ _)
     (uncurry λ θ →
       PT.rec (isProp≤ᵣ _ _)
        (uncurry λ θ<ε →
          PT.rec (isProp≤ᵣ _ _)
            λ (η , xx , xx') →
              let xx'* : rat r
                       ∼'[ (((ε .fst ℚ.- fst θ) ℚ.- fst η) , xx) ] x η
                  xx'* = xx'

                  yy : (δ : ℚ₊) → fst δ ℚ.< fst θ →
                          rat r ∼[ ε ] x δ
                  yy δ δ<θ =
                    let z = triangle∼ {rat r}
                              {x η} {x δ}
                                {(((ε .fst ℚ.- fst θ) ℚ.- fst η) , xx)}
                                   { θ ℚ₊+  η  }
                             (∼'→∼ _ _
                              ((((ε .fst ℚ.- fst θ) ℚ.- fst η) , xx))
                               xx')
                                let uu = (y η δ)
                                 in ∼-monotone<
                                       (subst (ℚ._< fst (θ ℚ₊+ η))
                                          (ℚ.+Comm (fst δ) (fst η))
                                          (ℚ.<-+o
                                            (fst δ)
                                            (fst θ) (fst η)
                                            δ<θ)) uu
                    in subst∼ lem--054 z

              in sym (eqℝ _ _ λ ε' →
                    let ε* = ℚ.min₊ (ℚ./2₊ ε') (ℚ./2₊ θ)
                        ε*<ε' = snd
                          (ℚ.<→ℚ₊  (fst ε*) (fst ε')
                             (
                             ℚ.isTrans≤< (fst ε*) (fst (ℚ./2₊ ε')) (fst ε')
                              (ℚ.min≤ (fst (ℚ./2₊ ε')) (fst (ℚ./2₊ θ)))
                               (ℚ.x/2<x ε') ))

                        ε*<θ = ℚ.isTrans≤< (fst ε*) (fst (ℚ./2₊ θ)) (fst θ)
                              (ℚ.min≤' (fst (ℚ./2₊ ε')) (fst (ℚ./2₊ θ)))
                               (ℚ.x/2<x θ)

                        zzz = x₁ ε* ε  (∼→∼' _ _ _ (yy ε* ε*<θ))
                    in rat-lim (q ℚ.+ fst ε) _ _ ε* _ ε*<ε'
                           (subst (rat (q ℚ.+ fst ε)
                             ∼[ (fst ε' ℚ.- fst ε*) , ε*<ε' ]_)
                              (sym zzz) (refl∼ (rat (q ℚ.+ fst ε))
                             ((fst ε' ℚ.- fst ε*) , ε*<ε'))) )))
    ∘ fst (rounded∼' (rat r) (lim x y) ε)

  w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isSetℝ _ _



-- 11.3.43-i

∼→< : ∀ u q → u <ᵣ (rat q) → ∀ v ε → u ∼'[ ε ] v → v <ᵣ rat (q ℚ.+ fst ε)
∼→< u q u<q v ε x =
  PT.map (λ ((q' , r') , z , z' , z'') →
            ((q' ℚ.+ fst ε) , (r' ℚ.+ fst ε)) ,
               (∼→≤ u q' z v ε x  , ((ℚ.<-+o q' r' (fst ε) z') ,
                 ≤ℚ→≤ᵣ (r' ℚ.+ fst ε) (q ℚ.+ fst ε)
                   (ℚ.≤-+o r' q (fst ε) (≤ᵣ→≤ℚ r' q z'')))))
            u<q




x+[y-x]/2≡y-[y-x]/2 : ∀ x y →
  x ℚ.+ (y ℚ.- x) ℚ.· [ 1 / 2 ]
   ≡ y ℚ.- ((y ℚ.- x) ℚ.· [ 1 / 2 ])
x+[y-x]/2≡y-[y-x]/2 u v =
  ((cong (u ℚ.+_) (ℚ.·DistR+ _ _ _ ∙ ℚ.+Comm _ _)
        ∙ ℚ.+Assoc _ _ _) ∙∙
          cong₂ ℚ._+_
            distℚ! u ·[
             (ge1 +ge ((neg-ge ge1) ·ge
                      ge[ [ pos 1 / 1+ 1 ] ]))
                   ≡ (neg-ge ((neg-ge ge1) ·ge
                      ge[ [ pos 1 / 1+ 1 ] ]))   ]
           distℚ! v ·[ (( ge[ [ pos 1 / 1+ 1 ] ]))
                   ≡ (ge1 +ge neg-ge (
                      ge[ [ pos 1 / 1+ 1 ] ]))   ]
          ∙∙ (ℚ.+Comm _ _ ∙ sym (ℚ.+Assoc v
                 (ℚ.- (v ℚ.· [ 1 / 2 ]))
                  (ℚ.- ((ℚ.- u) ℚ.· [ 1 / 2 ])))
            ∙ cong (ℚ._+_ v)
                (sym (ℚ.·DistL+ -1 _ _)) ∙ cong (ℚ._-_ v)
           (sym (ℚ.·DistR+ v (ℚ.- u) [ 1 / 2 ])) ))


-- 11.3.43-ii

∼→<' : ∀ u q → u <ᵣ (rat q) → ∀ v
   → ∃[ ε ∈ ℚ₊ ] (u ∼'[ ε ] v → v <ᵣ rat q)
∼→<' u q u<q v =
 PT.map
      (λ ((u' , q') , z , z' , z'') →
            ℚ./2₊ (ℚ.<→ℚ₊ u' q' z')  ,
              (λ xx →
                let zwz = ∼→≤  u u'  z v _ xx
                in ∣ (_ , q') , (zwz ,
                  (subst2
                      {x = q' ℚ.- (fst (ℚ./2₊ (ℚ.<→ℚ₊ u' q' z')))}
                      {u' ℚ.+ fst (ℚ./2₊ (ℚ.<→ℚ₊ u' q' z'))}
                      ℚ._<_
                     (sym (x+[y-x]/2≡y-[y-x]/2 u' q'))
                     (ℚ.+IdR q')
                     (ℚ.<-o+ (ℚ.- fst (ℚ./2₊ (ℚ.<→ℚ₊ u' q' z'))) 0 q'
                          (ℚ.-ℚ₊<0 (ℚ./2₊ (ℚ.<→ℚ₊ u' q' z'))))
                     , z'')) ∣₁ ))
      u<q


-- 11.3.44

lem-11-3-44 : ∀ u ε → u ∼'[ ε ] 0 → absᵣ u <ᵣ rat (fst ε)
lem-11-3-44 = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop (λ z → (ε : ℚ₊) → z ∼'[ ε ] 0 → absᵣ z <ᵣ rat (fst ε))
 w .Elimℝ-Prop.ratA x ε (x₁ , x₂) =
    <ℚ→<ᵣ (ℚ.abs' x) (fst ε)
      (subst (ℚ._< fst ε) (ℚ.abs'≡abs x)
        (ℚ.absFrom<×< (fst ε) x
          (subst ((ℚ.- fst ε) ℚ.<_) (ℚ.+IdR x) x₁)
           (subst (ℚ._< (fst ε)) ((ℚ.+IdR x)) x₂)))
 w .Elimℝ-Prop.limA x p x₁ ε =
   (PT.rec squash₁
     $ uncurry λ θ → PT.rec squash₁ λ (xx , xx') →
       let zqz = ((subst∼ {ε' = (θ ℚ₊· ([ pos 1 / 1+ 2 ] , _))}
                              (ℚ.ε/6+ε/6≡ε/3 (fst θ))
                            (𝕣-lim-self
                              x p (θ ℚ₊· ([ pos 1 / 6 ] , _))
                                 (θ ℚ₊· ([ pos 1 / 6 ] , _)))))
           by▵ : Σ (ℚ.0< (fst ε ℚ.- (fst θ ℚ.· ℚ.[ 2 / 3 ] )))
                   (λ z → x (θ ℚ₊· (ℚ.[ pos 1 / 6 ] , _))
                    ∼'[ (fst ε ℚ.- (fst θ ℚ.· ℚ.[ 2 / 3 ] )) , z ]
                      0)
           by▵ =
             let zz = triangle∼' (x ( θ  ℚ₊·(ℚ.[ 1 / 6 ] , _)))
                         (lim x p) 0 (( θ  ℚ₊·(ℚ.[ 1 / 3 ] , _)))
                          ((fst ε ℚ.- fst θ) , xx)
                         zqz xx'
                 zz' : ((fst θ) ℚ.· [ 1 / 3 ])
                         ℚ.+ (fst ε ℚ.- fst θ) ≡
                         (fst ε ℚ.- (fst θ ℚ.· [ 2 / 3 ]))
                 zz' = (λ i → ((fst θ) ℚ.· [ 1 / 3 ])
                         ℚ.+ (fst ε ℚ.-
                           distℚ! (fst θ) ·[
                             (ge1) ≡ (ge[ ℚ.[ pos 1 / 1+ 2 ] ]
                               +ge  ge[ ℚ.[ pos 1 / 1+ 2 ] ]
                               +ge  ge[ ℚ.[ pos 1 / 1+ 2 ] ] ) ] i ))
                     ∙∙ lem--055 ∙∙
                       λ i → fst ε ℚ.-
                           distℚ! (fst θ) ·[
                             (ge[ ℚ.[ pos 1 / 1+ 2 ] ]
                               +ge  ge[ ℚ.[ pos 1 / 1+ 2 ] ])
                               ≡ (ge[ ℚ.[ pos 2 / 1+ 2 ] ] ) ] i
             in sΣℚ<' zz' zz
           xxx : absᵣ (x (θ ℚ₊· ([ pos 1 / 6 ] , tt))) <ᵣ
                  rat (fst ε ℚ.- (fst θ  ℚ.· [ pos 2 / 1+ 2 ]))
           xxx = x₁ _ _  (snd (by▵))

           ggg' : absᵣ (lim x p) <ᵣ _
           ggg' = ∼→< _ _ xxx (absᵣ (lim x p))
                   ((θ  ℚ₊· ([ pos 1 / 1+ 2 ] , _))) $
                     ∼→∼' _ _ _ $
                             absᵣ-nonExpanding _ _ _ zqz

           ggg : absᵣ (lim x p) <ᵣ rat (fst ε)
           ggg = isTrans<ᵣ (absᵣ (lim x p))
                   _ (rat (fst ε)) ggg'
                     (<ℚ→<ᵣ _ _ (subst2 ℚ._<_
                          (lem--056 ∙
                            (λ i → (fst ε ℚ.-
                             ((distℚ! (fst θ) ·[
                             (ge[ ℚ.[ pos 1 / 1+ 2 ] ]
                               +ge  ge[ ℚ.[ pos 1 / 1+ 2 ] ])
                               ≡ (ge[ ℚ.[ pos 2 / 1+ 2 ] ] ) ]) i))
                                ℚ.+
                               (fst (θ ℚ₊· ([ pos 1 / 1+ 2 ] , tt)))))
                               (ℚ.+IdR (fst ε))
                           (ℚ.<-o+ (ℚ.- (fst θ ℚ.· [ pos 1 / 1+ 2 ])) 0 (fst ε)
                          (ℚ.-ℚ₊<0 (θ ℚ₊· ([ pos 1 / 1+ 2 ] , tt))))))


       in ggg) ∘S fst (rounded∼' (lim x p) 0 ε)
 w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → squash₁


∼≃abs<ε⇐ : ∀ u v  ε →
  (absᵣ (u +ᵣ (-ᵣ  v)) <ᵣ rat (fst ε)) → (u ∼[ ε ] v)

∼≃abs<ε⇐ u v ε = Elimℝ-Prop2Sym.go w u v ε
 where
  w : Elimℝ-Prop2Sym λ u v → ∀ ε →
          (absᵣ (u +ᵣ (-ᵣ  v)) <ᵣ rat (fst ε))
            → u ∼[ ε ] v
  w .Elimℝ-Prop2Sym.rat-ratA r q ε z =
    rat-rat-fromAbs r q ε
     (subst (ℚ._< fst ε) (sym (ℚ.abs'≡abs _)) (<ᵣ→<ℚ _ _ z))
  w .Elimℝ-Prop2Sym.rat-limA q x y R ε =
    PT.rec (isProp∼ _ _ _) ( λ (θ , (xx , xx')) →
          let 0<θ = ℚ.<→0< _ (<ᵣ→<ℚ 0 θ
                       (isTrans≤<ᵣ 0 _ (rat θ)
                         (0≤absᵣ _) xx))
              ww : ∀ δ η → absᵣ (rat q +ᵣ (-ᵣ lim x y))
                          ∼[ δ ℚ₊+ η ] absᵣ (rat q +ᵣ (-ᵣ (x δ)))
              ww δ η =
                let uu : ⟨ NonExpandingₚ (absᵣ ∘S (rat q +ᵣ_) ∘S -ᵣ_) ⟩
                    uu = NonExpandingₚ∘ absᵣ ((rat q +ᵣ_) ∘S -ᵣ_)
                              absᵣ-nonExpanding
                               (NonExpandingₚ∘ (rat q +ᵣ_) -ᵣ_
                                      (NonExpanding₂.go∼R sumR (rat q))
                                       (Lipschitz-ℝ→ℝ-1→NonExpanding
                                         _ (snd -ᵣR)))
                in uu (lim x y) (x δ) (δ ℚ₊+ η) (
                           sym∼ _ _ _ (𝕣-lim-self x y δ η))
              δ = ℚ./4₊ (ℚ.<→ℚ₊ θ (fst ε) (<ᵣ→<ℚ _ _ xx'))
              www = ∼→< (absᵣ (rat q +ᵣ (-ᵣ lim x y)))
                      θ
                      xx ((absᵣ (rat q +ᵣ (-ᵣ (x δ)))))
                         (δ ℚ₊+ δ)
                      (∼→∼' _ _ (δ ℚ₊+ δ) (ww δ δ))

              wwwR = R δ ((θ , 0<θ) ℚ₊+ (δ ℚ₊+ δ)) www
              zz : fst (δ ℚ₊+ δ) ℚ.+ (fst δ ℚ.+ fst δ) ≡
                     fst ε ℚ.- θ
              zz = distℚ! (fst ε ℚ.- θ)
                     ·[ (ge[ [ 1 / 4 ] ] +ge ge[ [ 1 / 4 ] ]) +ge
                        (ge[ [ 1 / 4 ] ] +ge ge[ [ 1 / 4 ] ]) ≡ ge1 ]
          in subst∼ ( sym (ℚ.+Assoc _ _ _) ∙∙
                    cong (θ ℚ.+_) zz ∙∙ lem--05 {θ} {fst ε} )
               (triangle∼ wwwR (𝕣-lim-self x y δ δ))) ∘S
          (denseℚinℝ (absᵣ (rat q +ᵣ (-ᵣ lim x y))) (rat (fst ε)))
  w .Elimℝ-Prop2Sym.lim-limA x y x' y' R ε =
      PT.rec (isProp∼ _ _ _) ( λ (θ , (xx , xx')) →
        let 0<θ = ℚ.<→0< _ (<ᵣ→<ℚ 0 θ
                       (isTrans≤<ᵣ 0 _ (rat θ)
                         (0≤absᵣ _) xx))
            ww : ∀ δ η → absᵣ (lim x y +ᵣ (-ᵣ lim x' y'))
                        ∼[ (δ ℚ₊+ η) ℚ₊+ (δ ℚ₊+ η) ]
                         absᵣ ((x δ) +ᵣ (-ᵣ (x' δ)))
            ww δ η =
              let uu = absᵣ-nonExpanding
                    ((lim x y +ᵣ (-ᵣ lim x' y')))
                    (x δ +ᵣ (-ᵣ x' δ))
                        _
                         (NonExpanding₂.go∼₂ sumR
                          _ _
                          (sym∼ _ _ _ (𝕣-lim-self x y δ η))
                          (Lipschitz-ℝ→ℝ-1→NonExpanding
                                         _ (snd -ᵣR) _ _ _
                                          (sym∼ _ _ _ (𝕣-lim-self x' y' δ η))))
              in uu
            δ = (ℚ.<→ℚ₊ θ (fst ε) (<ᵣ→<ℚ _ _ xx')) ℚ₊· ([ 1 / 6 ] , _)
            www = ∼→< (absᵣ (lim x y +ᵣ (-ᵣ lim x' y')))
                      θ
                      xx ((absᵣ (x δ +ᵣ (-ᵣ (x' δ)))))
                         ((δ ℚ₊+ δ) ℚ₊+ (δ ℚ₊+ δ))
                      (∼→∼' _ _ ((δ ℚ₊+ δ) ℚ₊+ (δ ℚ₊+ δ)) (ww δ δ))
            wwwR = R δ δ
                       ((θ , 0<θ) ℚ₊+ ((δ ℚ₊+ δ) ℚ₊+ (δ ℚ₊+ δ)))
                         www

            zz = cong (λ x → (x ℚ.+ x) ℚ.+ x)
                  (ℚ.ε/6+ε/6≡ε/3 (fst ε ℚ.- θ))
                   ∙ sym (ℚ.+Assoc _ _ _) ∙ ℚ.ε/3+ε/3+ε/3≡ε (fst ε ℚ.- θ)
         in uncurry (lim-lim _ _ _ δ δ _ _)
              (sΣℚ< (ℚ.+CancelL- _ _ _
                        (sym (ℚ.+Assoc _ _ _) ∙∙
                    cong (θ ℚ.+_) zz ∙∙ lem--05 {θ} {fst ε} )) wwwR)
       ) ∘S (denseℚinℝ (absᵣ ((lim x y) +ᵣ (-ᵣ lim x' y'))) (rat (fst ε)))
  w .Elimℝ-Prop2Sym.isSymA x y u ε =
    sym∼ _ _ _ ∘S u ε ∘S subst (_<ᵣ rat (fst ε))
     (minusComm-absᵣ y x)
  w .Elimℝ-Prop2Sym.isPropA _ _ = isPropΠ2 λ _ _ → isProp∼ _ _ _



∼≃abs<ε : ∀ u v  ε →
  (u ∼[ ε ] v) ≃
    (absᵣ (u +ᵣ (-ᵣ  v)) <ᵣ rat (fst ε))
∼≃abs<ε u v ε =
  propBiimpl→Equiv (isProp∼ _ _ _) (squash₁)
   (λ x →
    lem-11-3-44 ((u +ᵣ (-ᵣ v))) ε
      (∼→∼' _ _ _ $  (subst ((u +ᵣ (-ᵣ v)) ∼[ ε ]_) (+-ᵣ v)
       (+ᵣ-∼ u v (-ᵣ v) ε x))))
   (∼≃abs<ε⇐ u v ε)

getClampsOnQ : (a : ℚ) →
      Σ ℕ₊₁ (λ n → absᵣ (rat a) <ᵣ rat [ pos (ℕ₊₁→ℕ n) / 1+ 0 ])
getClampsOnQ = (map-snd (λ {a} → subst (_<ᵣ rat [ pos (ℕ₊₁→ℕ a) / 1+ 0 ])
      (cong rat (ℚ.abs'≡abs _ ))
      ∘S (<ℚ→<ᵣ _ _))) ∘ ℚ.boundℕ

getClamps : ∀ u →
   ∃[ n ∈ ℕ₊₁ ] absᵣ u <ᵣ fromNat (ℕ₊₁→ℕ n)
getClamps = Elimℝ-Prop.go w
 where
  w : Elimℝ-Prop _
  w .Elimℝ-Prop.ratA =
    ∣_∣₁ ∘ getClampsOnQ
  w .Elimℝ-Prop.limA x p x₁ =
   PT.map (λ (1+ n , v) →
   let z' = (subst∼ {ε' = ℚ./2₊ 1} ℚ.decℚ? $ 𝕣-lim-self x p (ℚ./4₊ 1) (ℚ./4₊ 1))
       z = ∼→< (absᵣ (x (ℚ./4₊ 1))) _ v (absᵣ (lim x p)) 1
              (∼→∼' _ _ _
               (∼-monotone< (ℚ.x/2<x 1) (absᵣ-nonExpanding _ _ _ z')) )

       uu = ℤ.·IdR _ ∙ (sym $ ℤ.+Comm 1 (pos 1 ℤ.+ pos n ℤ.· pos 1))

   in (suc₊₁ (1+ n)) , subst ((absᵣ (lim x p) <ᵣ_) ∘ rat) (eq/ _ _ uu) z) $ x₁ (ℚ./4₊ 1)
  w .Elimℝ-Prop.isPropA _ = squash₁

restrSq : ∀ n → Lipschitz-ℚ→ℚ-restr (fromNat (suc n))
                  ((2 ℚ₊· fromNat (suc n)))
                  λ x → x ℚ.· x

restrSq n q r x x₁ ε x₂ =

  subst (ℚ._< 2 ℚ.· fst (fromNat (suc n)) ℚ.· fst ε)
    (ℚ.abs·abs (q ℚ.+ r) (q ℚ.- r) ∙ cong ℚ.abs (lem--040 {q} {r})) z

 where
  zz : ℚ.abs (q ℚ.+ r) ℚ.< 2 ℚ.· fst (fromNat (suc n))
  zz = subst (ℚ.abs (q ℚ.+ r) ℚ.<_)
           (sym (ℚ.·DistR+ 1 1 (fst (fromNat (suc n)))))
          (ℚ.isTrans≤< (ℚ.abs (q ℚ.+ r)) (ℚ.abs q ℚ.+ ℚ.abs r)
            _ (ℚ.abs+≤abs+abs q r)
              (ℚ.<Monotone+ (ℚ.abs q) _ (ℚ.abs r) _ x x₁ ))

  z : ℚ.abs (q ℚ.+ r) ℚ.· ℚ.abs (q ℚ.- r) ℚ.<
        2 ℚ.· fst (fromNat (suc n)) ℚ.· fst ε
  z = ℚ.<Monotone·-onPos _ _ _ _
      zz x₂ (ℚ.0≤abs (q ℚ.+ r)) ((ℚ.0≤abs (q ℚ.- r)))


0<ℕ₊₁ : ∀ n m → 0 ℚ.< ([ ℚ.ℕ₊₁→ℤ n / m ])
0<ℕ₊₁ n m = ℚ.0<→< ([ ℚ.ℕ₊₁→ℤ n / m ]) tt

1/n<sucK : ∀ m n → ℚ.[ 1 / (suc₊₁ m) ] ℚ.< ([ ℚ.ℕ₊₁→ℤ n / 1 ])
1/n<sucK m n =
 subst (1 ℤ.<_) (ℤ.pos·pos _ _) (ℤ.suc-≤-suc (ℤ.suc-≤-suc ℤ.zero-≤pos ))

<Δ : ∀ n → [ 1 / 4 ] ℚ.< ([ pos (suc n) / 1 ])
<Δ n = 1/n<sucK 3 (1+ n)


clampedSq : ∀ (n : ℕ) → Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (2 ℚ₊· fromNat (suc n)))
clampedSq n =
  let ex = Lipschitz-ℚ→ℚ-extend _
             _ _ (ℚ.[ (1 , 4) ] , _) (<Δ n) (restrSq n)
  in fromLipschitz _ (_ , Lipschitz-rat∘ _ _ ex)

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

openPred : (P : ℝ → hProp ℓ-zero) → hProp ℓ-zero
openPred P = (∀ x → ⟨ P x ⟩ → ∃[ δ ∈ ℚ₊ ] (∀ y → x ∼[ δ ] y → ⟨ P y ⟩ ) )
   , isPropΠ2 λ _ _ → squash₁


<min-rr : ∀ p q r → p <ᵣ (rat q) → p <ᵣ (rat r) → p <ᵣ minᵣ (rat q) (rat r)
<min-rr p =
 ℚ.elimBy≤ (λ x y R a b → subst (p <ᵣ_) (minᵣComm (rat x) (rat y)) (R b a))
   λ x y x≤y p<x _ → subst ((p <ᵣ_) ∘ rat)
    (sym (ℚ.≤→min _ _ x≤y) ) (p<x)


m·n/m : ∀ m n → [ pos (suc m) / 1 ] ℚ.· [ pos n / 1+ m ] ≡ [ pos n / 1 ]
m·n/m m n =
  eq/ _ _ ((λ i → ℤ.·IdR (ℤ.·Comm (pos (suc m)) (pos n) i) i)
       ∙ cong ((pos n ℤ.·_) ∘ ℚ.ℕ₊₁→ℤ) (sym (·₊₁-identityˡ (1+ m))))

3·x≡x+[x+x] : ∀ x → 3 ℚ.· x ≡ x ℚ.+ (x ℚ.+ x)
3·x≡x+[x+x] x = ℚ.·Comm _ _ ∙
  distℚ! x ·[ ge[ 3 ] ≡ ge1 +ge (ge1 +ge ge1) ]

abs'q≤Δ₁ : ∀ q n → absᵣ (rat q) <ᵣ rat [ pos (suc n) / 1+ 0 ]
     →  ℚ.abs' q ℚ.≤ ([ pos (suc (suc (n))) / 1 ] ℚ.- [ 1 / 4 ])
abs'q≤Δ₁ q n n< = (ℚ.isTrans≤ (ℚ.abs' q) (fromNat (suc n)) _
          (ℚ.<Weaken≤ _ _ (<ᵣ→<ℚ _ _ n<))
           (subst2 ℚ._≤_
             ((ℚ.+IdR _))
               ((cong {x = [ 3 / 4 ]} {y = 1 ℚ.- [ 1 / 4 ]}
                         ([ pos (suc n) / 1 ] ℚ.+_)
                         (𝟚.toWitness
                          {Q = ℚ.discreteℚ [ 3 / 4 ] (1 ℚ.- [ 1 / 4 ])}
                           _ ))
                          ∙∙ ℚ.+Assoc _ _ _ ∙∙
                            cong (ℚ._- [ pos 1 / 1+ 3 ])
                             (ℚ.+Comm [ pos (suc n) / 1 ]
                               1 ∙
                                ℚ.ℤ+→ℚ+ 1 (pos (suc n)) ∙
                                  cong [_/ 1 ]
                                   (sym (ℤ.pos+ 1 (suc n)))))
             (ℚ.≤-o+ 0 [ 3 / 4 ] (fromNat (suc n))
               (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 3 / 4 ]} _ ))))

abs'q≤Δ₁' : ∀ q n → ℚ.abs' q ℚ.≤ [ pos (suc n) / 1+ 0 ]
     →  ℚ.abs' q ℚ.≤ ([ pos (suc (suc (n))) / 1 ] ℚ.- [ 1 / 4 ])
abs'q≤Δ₁' q n n< = (ℚ.isTrans≤ (ℚ.abs' q) (fromNat (suc n)) _
          (n<)
           (subst2 ℚ._≤_
             ((ℚ.+IdR _))
               ((cong {x = [ 3 / 4 ]} {y = 1 ℚ.- [ 1 / 4 ]}
                         ([ pos (suc n) / 1 ] ℚ.+_)
                         (𝟚.toWitness
                          {Q = ℚ.discreteℚ [ 3 / 4 ] (1 ℚ.- [ 1 / 4 ])}
                           _ ))
                          ∙∙ ℚ.+Assoc _ _ _ ∙∙
                            cong (ℚ._- [ pos 1 / 1+ 3 ])
                             (ℚ.+Comm [ pos (suc n) / 1 ]
                               1 ∙
                                ℚ.ℤ+→ℚ+ 1 (pos (suc n)) ∙
                                  cong [_/ 1 ]
                                   (sym (ℤ.pos+ 1 (suc n)))))
             (ℚ.≤-o+ 0 [ 3 / 4 ] (fromNat (suc n))
               (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 3 / 4 ]} _ ))))


ℚabs-abs≤abs- : (x y : ℚ) → (ℚ.abs x ℚ.- ℚ.abs y) ℚ.≤ ℚ.abs (x ℚ.- y)
ℚabs-abs≤abs- x y =
 subst2 ℚ._≤_
   (cong ((ℚ._+ (ℚ.- (ℚ.abs y))) ∘ ℚ.abs) lem--00 )
   (sym lem--034)
  (ℚ.≤-+o
   (ℚ.abs ((x ℚ.- y) ℚ.+ y))
   (ℚ.abs (x ℚ.- y) ℚ.+ ℚ.abs y) (ℚ.- (ℚ.abs y)) (ℚ.abs+≤abs+abs (x ℚ.- y) y))

IsContinuousAbsᵣ : IsContinuous absᵣ
IsContinuousAbsᵣ = Lipschitz→IsContinuous _ (fst absᵣL) (snd absᵣL)


IsContinuousMaxR : ∀ x → IsContinuous (λ u → maxᵣ u x)
IsContinuousMaxR x u ε =
 ∣ ε , (λ v → NonExpanding₂.go∼L maxR _ _ _ ε) ∣₁

IsContinuousMaxL : ∀ x → IsContinuous (maxᵣ x)
IsContinuousMaxL x u ε =
 ∣ ε , (λ v → NonExpanding₂.go∼R maxR _ _ _ ε) ∣₁

IsContinuousMinR : ∀ x → IsContinuous (λ u → minᵣ u x)
IsContinuousMinR x u ε =
 ∣ ε , (λ v → NonExpanding₂.go∼L minR _ _ _ ε) ∣₁

IsContinuousMinL : ∀ x → IsContinuous (minᵣ x)
IsContinuousMinL x u ε =
 ∣ ε , (λ v → NonExpanding₂.go∼R minR _ _ _ ε) ∣₁



IsContinuous-ᵣ : IsContinuous (-ᵣ_)
IsContinuous-ᵣ = Lipschitz→IsContinuous _ (fst -ᵣR) (snd -ᵣR)

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



cont₂+ᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
  → IsContinuous (λ x → f x +ᵣ g x)
cont₂+ᵣ = contDiagNE₂ sumR

cont₂maxᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
  → IsContinuous (λ x → maxᵣ (f x) (g x))
cont₂maxᵣ = contDiagNE₂ maxR

cont₂minᵣ : ∀ f g → (IsContinuous f) → (IsContinuous g)
  → IsContinuous (λ x → minᵣ (f x) (g x))
cont₂minᵣ = contDiagNE₂ minR



IsContinuous+ᵣR : ∀ x → IsContinuous (_+ᵣ x)
IsContinuous+ᵣR x u ε =
 ∣ ε , (λ v → NonExpanding₂.go∼L sumR _ _ _ ε) ∣₁

IsContinuous+ᵣL : ∀ x → IsContinuous (x +ᵣ_)
IsContinuous+ᵣL x u ε =
 ∣ ε , (λ v → NonExpanding₂.go∼R sumR _ _ _ ε) ∣₁


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
              (subst2 ℚ._≤_ (ℚ.abs'≡abs _)
                (cong₂ ℚ._+_ (ℚ.abs'≡abs _) (ℚ.abs'≡abs _))
               (ℚ.abs+≤abs+abs r r') ) )) y) x


<ᵣWeaken≤ᵣ : ∀ m n → m <ᵣ n → m ≤ᵣ n
<ᵣWeaken≤ᵣ m n = PT.rec (isSetℝ _ _)
 λ ((q , q') , x , x' , x'')
   → isTrans≤ᵣ _ _ _ x (isTrans≤ᵣ _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ x')) x'')

≡ᵣWeaken≤ᵣ : ∀ m n → m ≡ n → m ≤ᵣ n
≡ᵣWeaken≤ᵣ m n p = cong (flip maxᵣ n) p ∙ ≤ᵣ-refl n

IsContinuousId : IsContinuous (λ x → x)
IsContinuousId u ε = ∣ ε , (λ _ x → x) ∣₁

IsContinuousConst : ∀ x → IsContinuous (λ _ → x)
IsContinuousConst x u ε = ∣ ε , (λ _ _ → refl∼ _ _ ) ∣₁

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



≤ᵣ-+o : ∀ m n o →  m ≤ᵣ n → (m +ᵣ o) ≤ᵣ (n +ᵣ o)
≤ᵣ-+o m n o p = sym (+ᵣMaxDistr m n o) ∙ cong (_+ᵣ o) p

≤ᵣ-o+ : ∀ m n o →  m ≤ᵣ n → (o +ᵣ m) ≤ᵣ (o +ᵣ n)
≤ᵣ-o+ m n o = subst2 _≤ᵣ_ (+ᵣComm _ _) (+ᵣComm _ _)  ∘ ≤ᵣ-+o m n o


≤ᵣMonotone+ᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s → (m +ᵣ o) ≤ᵣ (n +ᵣ s)
≤ᵣMonotone+ᵣ m n o s m≤n o≤s =
  isTrans≤ᵣ _ _ _ (≤ᵣ-+o m n o m≤n) (≤ᵣ-o+ o s n o≤s)




lem--05ᵣ : ∀ δ q →  δ +ᵣ (q +ᵣ (-ᵣ δ)) ≡ q
lem--05ᵣ δ q = cong (δ +ᵣ_) (+ᵣComm _ _) ∙∙
   +ᵣAssoc _ _ _  ∙∙
    (cong (_+ᵣ q) (+-ᵣ δ) ∙ +IdL q)

abs-max : ∀ x → absᵣ x ≡ maxᵣ x (-ᵣ x)
abs-max = ≡Continuous _ _
  IsContinuousAbsᵣ
   (cont₂maxᵣ _ _ IsContinuousId IsContinuous-ᵣ)
    λ r → cong rat (sym (ℚ.abs'≡abs r))

absᵣNonNeg : ∀ x → 0 ≤ᵣ x → absᵣ x ≡ x
absᵣNonNeg x p = abs-max x ∙∙ maxᵣComm _ _ ∙∙ z
 where
   z : (-ᵣ x) ≤ᵣ x
   z = subst2 _≤ᵣ_
     (+IdL (-ᵣ x))
     (sym (+ᵣAssoc _ _ _) ∙∙ cong (x +ᵣ_) (+-ᵣ x) ∙∙ +IdR x)
     (≤ᵣ-+o 0 (x +ᵣ x) (-ᵣ x)
      (≤ᵣMonotone+ᵣ 0 x 0 x p p))

absᵣPos : ∀ x → 0 <ᵣ x → absᵣ x ≡ x
absᵣPos x = absᵣNonNeg x ∘ <ᵣWeaken≤ᵣ _ _
