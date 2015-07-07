module Logic.Tensor.Lambda.Syntax where

open import Logic.Tensor.Syntax

Type = Formula

data Term : Type → Set where
  var : (τ : Type) → Term τ
  app : ∀ {τ τ′} → Term (τ ⇒ τ′) → Term τ → Term τ′
  abs : ∀ {τ τ′} → Term 
