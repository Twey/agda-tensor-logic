{-# OPTIONS --copatterns #-}

module Logic.Tensor.Semantics where

data Formula : Set where
  ⊤   : Formula
  ¬_  : Formula → Formula
  _⊗_ : Formula → Formula → Formula

⊥ = ¬ ⊤

record Game : Set₁ where
  coinductive
  constructor game
  field
    {move} : Set
    play : move → Game

import Data.Unit

boring : Game
Game.move boring = Data.Unit.⊤
Game.play boring = λ tt → boring

mutual
  record Strategy (g : Game) : Set₁ where
    coinductive
    constructor strat
    open Game g
    field
      react : (m : move) → Strategy′ (play m)

  record Strategy′ (g : Game) : Set₁ where
    coinductive
    constructor strat′
    open Game g
    field
      response : move
      followup : Strategy (play response)

open Game
open Strategy
open Strategy′

open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function     using (_∘_)

-- l for ludum
-- shut up, I don't have subscript g ☹
_×ₗ_ : Game → Game → Game
move (A ×ₗ B) = move A ⊎ move B
play (A ×ₗ B) =
  λ { (inj₁ a) → game λ a′ → play (play A a) a′ ×ₗ B
    ; (inj₂ b) → game λ b′ → A ×ₗ play (play B b) b′
    }

⟦_⟧ : Formula → Game
⟦   ⊤   ⟧ = game ⊥-elim
⟦  ¬ A  ⟧ = game λ { tt → ⟦ A ⟧ }
⟦ A ⊗ B ⟧ = ⟦ A ⟧ ×ₗ ⟦ B ⟧

Provable    = Strategy  ∘ ⟦_⟧
Disprovable = Strategy′ ∘ ⟦_⟧

⊤-defn : Provable ⊤
⊤-defn = strat λ {()}

⊥-defn : Disprovable ⊥
⊥-defn = strat′ tt ⊤-defn

¬-defn : {A : Formula} → Disprovable A → Provable (¬ A)
¬-defn ¬A = strat λ { tt → ¬A }

_×ₛ_ : ∀ {A B} → Strategy A → Strategy B → Strategy (A ×ₗ B)
react (sA ×ₛ sB) =
  λ { (inj₁ a) →
        strat′ (response (react sA a)) (followup (react sA a) ×ₛ sB)
    ; (inj₂ b) →
        strat′ (response (react sB b)) (sA ×ₛ followup (react sB b))
    }

⊗-defn : ∀ {A B} → Provable A × Provable B → Provable (A ⊗ B)
⊗-defn (sA , sB) = sA ×ₛ sB
