/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Batteries.Control.LawfulMonadState
import LeanTrees.Control.Monad.MonadLift
import LeanTrees.Tactic.MonadReassoc

/-!
# Additions to Batteries' lawful-state-monad API

The 2023 version of this file defined its own `LawfulMonadStateOf` class. Batteries
now provides that class, with an equivalent axiomatization: where this development
stated the `get` laws as equations between closed computations (`get_get_pair`,
`get_set`), Batteries states them with an arbitrary continuation baked in
(`get_bind_get_bind`, `get_bind_set_bind`). The two are interderivable; the bridge
is uncurrying, and it is packaged here as `LawfulMonadStateOf.ofClosed`.

Batteries also supplies `modify_eq`, `getModify_eq`, and `LawfulMonadStateOf`
instances for `StateT`, `StateCpsT`, `EStateM`, `ReaderT` and `StateRefT'`, all of
which this file used to prove by hand.

What remains here is what Batteries does not provide:

* `ofClosed`, the closed-form constructor for the class;
* `modifyThenGet` / `modifyThenGetThe` and their defining equation;
* `get_set_pure_eq_get` (Batteries' `get_bind_set` discards the state rather than
  returning it);
* `reassocM` variants of the state laws, for rewriting under a bind;
* transfer of lawfulness along an arbitrary `LawfulMonadLift` (Batteries covers
  only the specific `ReaderT` / `StateRefT'` cases).
-/

universe u v w

namespace MonadStateOf

@[always_inline, inline]
abbrev modifyThenGetThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m]
  (f : σ → σ) : m σ := modifyGet fun s => (f s, f s)

end MonadStateOf

namespace MonadState

@[always_inline, inline]
def modifyThenGet {σ : Type u} {m : Type u → Type v} [MonadState σ m]
  (f : σ → σ) : m σ := modifyGet fun s => (f s, f s)

end MonadState

export MonadState (modifyThenGet)

attribute [reassocM]
  LawfulMonadStateOf.modifyGet_eq
  LawfulMonadStateOf.set_bind_get
  LawfulMonadStateOf.set_bind_set

namespace LawfulMonadStateOf

/-- Build Batteries' `LawfulMonadStateOf` from the closed-form state laws — that is,
equations between complete computations rather than ones with a continuation baked in.

This is the axiomatization the original development used. It is equivalent to
Batteries': the continuation-form `get` laws are recovered by binding the
`Prod`-valued `get_get_pair` against `Function.uncurry k`, and `get_bind_const`
follows by duplicating the `get` and collapsing the inner `get >>= set`. -/
def ofClosed {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [MonadStateOf σ m]
    (set_set : ∀ (s₁ s₂ : σ), (do set s₁; set s₂ : m PUnit) = set s₂)
    (set_get : ∀ (s : σ), (do set s; get : m σ) = (do set s; pure s))
    (get_set : (do let s ← (get : m σ); set s) = pure PUnit.unit)
    (get_get_pair : (do let s₁ ← (get : m σ); let s₂ ← get; pure (s₁, s₂))
                  = (do let s ← (get : m σ); pure (s, s)))
    (modifyGet_def : ∀ {α : Type u} (f : σ → α × σ),
      (modifyGet f : m α) = (do let p := f (← get); set p.snd; pure p.fst)) :
    LawfulMonadStateOf σ m := by
  -- Continuation form of `get_get_pair`, by uncurrying.
  have get_get : ∀ {α : Type u} (k : σ → σ → m α),
      (do let s ← get; let s' ← get; k s s') = (do let s ← get; k s s) := by
    intro α k
    have h := congrArg (· >>= Function.uncurry k) get_get_pair
    simpa [bind_assoc, Function.uncurry] using h
  -- Continuation form of `get_set`: duplicate the `get`, collapse the inner one.
  have gbsb : ∀ {α : Type u} (mx : σ → PUnit → m α),
      (do let s ← get; let u ← set s; mx s u) = (do let s ← get; mx s PUnit.unit) := by
    intro α mx
    rw [← get_get (fun s s' => set s' >>= fun u => mx s u)]
    refine bind_congr fun s => ?_
    rw [← bind_assoc, get_set, pure_bind]
  exact
    { modifyGet_eq := fun f => by
        rw [modifyGet_def]
        simp only [map_eq_pure_bind, bind_assoc, pure_bind, Function.comp_apply]
      get_bind_const := fun mx => by
        rw [← gbsb (fun _ _ => mx), ← bind_assoc, get_set, pure_bind]
      get_bind_get_bind := get_get
      get_bind_set_bind := gbsb
      set_bind_get := set_get
      set_bind_set := set_set }

section

variable {σ : Type u} {m : Type u → Type v} [Monad m] [MonadStateOf σ m]
  [LawfulMonadStateOf σ m]

/-- Getting the state, setting it to itself, and returning it is just `get`.
Batteries' `get_bind_set` is the variant that discards the state. -/
@[simp] theorem get_set_pure_eq_get : (do let s ← get; set s; pure s) = (get : m σ) := by
  rw [get_bind_set_bind (σ := σ) (m := m) (fun s _ => pure s), bind_pure]

@[simp] theorem modifyThenGet_def (f : σ → σ) :
    (modifyThenGet f : m σ) = (do modify f; get) := by
  simp [modifyThenGet, modifyGet_eq, modify_eq, map_eq_pure_bind, bind_assoc, -bind_pure_comp]

end

/-- Lawfulness of the state operations transfers along any `LawfulMonadLift`.

Deliberately not an instance: as a global instance over an arbitrary `MonadLift`
it would apply to every monad pair and blow up typeclass search. Batteries instead
registers the individual `ReaderT` / `StateRefT'` cases. Use this to build the
instance for a specific lifted monad. -/
def ofLift {σ : Type u} {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] [LawfulMonad n] [MonadStateOf σ m]
    [MonadLift m n] [LawfulMonadLift m n] [LawfulMonadStateOf σ m] :
    LawfulMonadStateOf σ n :=
  -- Each closed law is the image under `liftM` of the corresponding law in `m`.
  -- `liftM_get`/`liftM_set`/`liftM_modifyGet` are `rfl`-lemmas tagged `@[simp]`,
  -- so `simpa` turns the lifted operations back into `n`'s own state operations.
  ofClosed
    (set_set := fun s₁ s₂ => by
      have h := congrArg (liftM (n := n)) (set_bind_set (m := m) s₁ s₂)
      rw [liftM_bind] at h; simpa using h)
    (set_get := fun s => by
      have h := congrArg (liftM (n := n)) (set_bind_get (m := m) s)
      simp only [liftM_bind, liftM_pure] at h; simpa using h)
    (get_set := by
      have h := congrArg (liftM (n := n)) (get_bind_set (σ := σ) (m := m))
      rw [liftM_bind, liftM_pure] at h; simpa using h)
    (get_get_pair := by
      have h := congrArg (liftM (n := n))
        (get_bind_get_bind (σ := σ) (m := m) (fun s s' => pure (s, s')))
      simp only [liftM_bind, liftM_pure] at h; simpa using h)
    (modifyGet_def := fun f => by
      have h := congrArg (liftM (n := n)) (modifyGet_eq (m := m) f)
      simp only [liftM_bind, liftM_pure, liftM_map] at h
      simpa [map_eq_pure_bind, bind_assoc, -bind_pure_comp] using h)

end LawfulMonadStateOf
