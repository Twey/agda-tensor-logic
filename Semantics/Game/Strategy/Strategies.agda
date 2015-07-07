{-# OPTIONS --copatterns #-}

module Semantics.Game.Strategy.Strategies where

import Semantics.Game as G
open import Semantics.Game.Strategy

open import Data.Sum

open import Data.Unit as ⊤ using (tt)

⊤ : Strategy G.⊤
react ⊤ ()

infix 4 ¬_
¬_ : ∀ {A} → Strategy′ A → Strategy (G.¬ A)
react (¬ ¬A) tt = ¬A

infix 5 _⊗_
_⊗_ : ∀ {A B} → Strategy A → Strategy B → Strategy (A G.⊗ B)
react (sA ⊗ sB) (inj₁ a)
  = strat′ (response (react sA a)) (followup (react sA a) ⊗ sB)
react (sA ⊗ sB) (inj₂ b)
  = strat′ (response (react sB b)) (sA ⊗ followup (react sB b))

⊥ : Strategy′ G.⊥
response ⊥ = tt
followup ⊥ = ⊤

swap : ∀ {A B} → Strategy (A G.⊗ B) → Strategy (B G.⊗ A)
react (swap s) (inj₁ b)
  = strat′ (response (react s (inj₂ b))) (swap (followup (react s (inj₂ b))))
react (swap s) (inj₂ a)
  = strat′ (response (react s (inj₁ a))) (swap (followup (react s (inj₁ a))))

copycat′ : ∀ {A} a → Strategy′ (G.play A a G.⊗ A)
response (copycat′ a) = inj₂ a
followup (copycat′ a) = strat (λ a′ → strat′ (inj₁ a′) (strat copycat′))

copycat : ∀ {A} → Strategy (A G.⊸ A)
copycat = ¬ strat′ (inj₁ tt) (strat copycat′)
