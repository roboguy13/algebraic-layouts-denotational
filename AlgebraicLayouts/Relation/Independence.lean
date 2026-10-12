/-
  Layout independence, as a corollary of the fundamental lemma.

  Generic in the backend, the worlds and the admissibility candidate: it uses
  only `Requirements θ` plus an `Adequacy θ` (how to observe a result, and why
  related results are observed equally).

  Checked against the repo at e94d475 (Relation/ as committed), with Mathlib
  (Lean 4.35.0-rc4, relaxedAutoImplicit = false).
-/

import AlgebraicLayouts.Relation.Fundamental

section Independence

variable {P : Type} [Backend P] {Sig : Adt → Type}
variable {sigSem : ∀ {T : Adt}, Sig T → SemLayout P T}
variable {W : Type} [Preorder W]

/-! ### Observations -/

/-- How results are observed, and why related results look the same.
For SL: `top v` is `⌜result = v⌝`, and `obs p` is e.g. the set of
observable results of `p`. -/
structure Adequacy (θ : RelParams P sigSem W) where
  Obs : Type
  obs : P → Obs
  /-- The top-level continuation for a program of base type. -/
  top : (b : Base) → Backend.Val P b → P
  /-- Related values give related results. -/
  top_rel : ∀ {w : W} {b : Base} {v₁ v₂}, θ.RVal w b v₁ v₂ → θ.RP w (top b v₁) (top b v₂)
  /-- Related results are observed equally. -/
  adequate : ∀ {w : W} {p₁ p₂}, θ.RP w p₁ p₂ → obs p₁ = obs p₂

/-- Run a computation of base type with the top-level continuation. -/
def Adequacy.run {θ : RelParams P sigSem W} (adeq : Adequacy θ) {b : Base}
    (c : Comp P (ULift (Backend.Val P b))) : P :=
  (c fun v => ⟨adeq.top b v.down⟩).down

/-- The observation of a related pair of base computations. -/
theorem Adequacy.run_eq {θ : RelParams P sigSem W} (adeq : Adequacy θ) {b : Base} {w : W}
    {c₁ c₂ : Comp P (ULift (Backend.Val P b))}
    (h : CompRel θ (fun w (x y : ULift (Backend.Val P b)) => θ.RVal w b x.down y.down) w c₁ c₂) :
    adeq.obs (adeq.run c₁) = adeq.obs (adeq.run c₂) :=
  adeq.adequate (h w le_rfl _ _ fun _ _ _ _ hxy => adeq.top_rel hxy)

/-! ### Empty environments -/

def LEnv.empty : LEnv P .empty := fun l => nomatch l

def Env.empty {lenv : LEnv P .empty} : Env P sigSem (Sig := Sig) .empty lenv := fun x => nomatch x

def RelEnv.empty : RelEnv (P := P) (W := W) .empty where
  lenv₁ := LEnv.empty
  lenv₂ := LEnv.empty
  rel := fun l => nomatch l

/-! ### Layout independence -/

/-- **Layout independence (open programs).** A program of base type, run in
two related layout environments with related inputs, is observed equally. -/
theorem layout_independence {θ : RelParams P sigSem W} (req : Requirements θ) (adeq : Adequacy θ)
    {Δ : LCtx} {Γ : Ctx Sig Δ} {b : Base} (e : Expr Γ (.base b))
    (ρ : RelEnv (P := P) (W := W) Δ) (hρ : ρ.Related θ) (w : W)
    (env₁ : Env P sigSem Γ ρ.lenv₁) (env₂ : Env P sigSem Γ ρ.lenv₂)
    (henv : Env.rel θ ρ w env₁ env₂) :
    adeq.obs (adeq.run (Expr.interp P sigSem e ρ.lenv₁ env₁)) =
      adeq.obs (adeq.run (Expr.interp P sigSem e ρ.lenv₂ env₂)) :=
  adeq.run_eq (Expr.fundamental θ req e ρ hρ w env₁ env₂ henv)

/-- The type `∀ α : T. α → b` of a layout-polymorphic consumer. -/
abbrev ConsumerTy (Sig : Adt → Type) (T : Adt) (b : Base) : Ty Sig .empty :=
  .forallLayout T (.arr (.atL T (.var .here)) (.base b))

/-- Instantiate a closed polymorphic consumer at `L` and apply it to `d`. -/
def runConsumer {θ : RelParams P sigSem W} (adeq : Adequacy θ) {T : Adt} {b : Base}
    (e : Expr (Sig := Sig) .empty (ConsumerTy Sig T b)) (L : SemLayout P T) (d : L.Rep) : P :=
  adeq.run
    (Comp.bind P (Expr.interp P sigSem e LEnv.empty Env.empty) fun F =>
      Comp.bind P (F L) fun f => f ⟨d⟩)

/-- **Layout independence (closed consumers).** A closed layout-polymorphic
consumer, given related layouts and related inputs, is observed equally. -/
theorem layout_independence_consumer {θ : RelParams P sigSem W} (req : Requirements θ)
    (adeq : Adequacy θ) {T : Adt} {b : Base} (e : Expr (Sig := Sig) .empty (ConsumerTy Sig T b))
    {L₁ L₂ : SemLayout P T} {R : RepRel W L₁.Rep L₂.Rep} (hR : θ.Related L₁ L₂ R)
    {w : W} {d₁ : L₁.Rep} {d₂ : L₂.Rep} (hd : R w d₁ d₂) :
    adeq.obs (runConsumer adeq e L₁ d₁) = adeq.obs (runConsumer adeq e L₂ d₂) := by
  apply adeq.run_eq (w := w)
  refine CompRel.bind
    (Expr.fundamental θ req e RelEnv.empty (fun l => nomatch l) w Env.empty Env.empty
      (fun x => nomatch x)) ?_
  intro w' hle F G hFG
  refine CompRel.bind (hFG L₁ L₂ R hR) ?_
  intro w'' hle' f g hfg
  exact hfg w'' le_rfl ⟨d₁⟩ ⟨d₂⟩ (req.related_mono hR (le_trans hle hle') hd)

/-- **Via a reference layout** (candidate A, with `M := Abs T`): if each
layout is related to `M`, and both inputs represent the same `a : M.Rep`,
the observations agree. -/
theorem layout_independence_via {θ : RelParams P sigSem W} (req : Requirements θ)
    (adeq : Adequacy θ) {T : Adt} {b : Base} (e : Expr (Sig := Sig) .empty (ConsumerTy Sig T b))
    {L₁ L₂ M : SemLayout P T} {R₁ : RepRel W L₁.Rep M.Rep} {R₂ : RepRel W L₂.Rep M.Rep}
    (hR₁ : θ.Related L₁ M R₁) (hR₂ : θ.Related L₂ M R₂)
    {w : W} {d₁ : L₁.Rep} {d₂ : L₂.Rep} {a : M.Rep} (hd₁ : R₁ w d₁ a) (hd₂ : R₂ w d₂ a) :
    adeq.obs (runConsumer adeq e L₁ d₁) = adeq.obs (runConsumer adeq e L₂ d₂) :=
  (layout_independence_consumer req adeq e hR₁ hd₁).trans
    (layout_independence_consumer req adeq e hR₂ hd₂).symm

end Independence
