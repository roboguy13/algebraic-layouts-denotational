/-
  Toy symbolic backend, an `sll` dictionary, and two `#eval`s.
  Checked against the repo at commit 916c688 ("refactor to backend values"),
  Lean 4.35.0-rc4, with ONE fix to Syntax.lean (`Stable` needs explicit
  binders; see below). Output:

    nilProg:  ∃x0. x0 = null * result = x0
    openProg: ∃x0. x0 = null * (x0 = null * result = 1)
                 ∨ (∃x1. ∃x2. x0 ↦ x1 * (x0+1) ↦ x2 * result = 2)

  Required fix in Syntax.lean. The current constructors mention no term that
  fixes the layout context, so auto-bound implicits turn it into a function
  `{x : {b : Base} → LCtx}` and the constructors can't be used at a concrete
  context:

    inductive Stable : {Δ : LCtx} → Ty Sig Δ → Prop where
    | base {Δ : LCtx} {b : Base} : Stable (Δ := Δ) (.base b)
    | atL {Δ : LCtx} {T : Adt} {l : LayoutRef Sig Δ T} : Stable (.atL T l)
    | arr {Δ : LCtx} {a b : Ty Sig Δ} : Stable a → Stable b → Stable (.arr a b)
    | forallLayout {Δ : LCtx} {T : Adt} {body : Ty Sig (Δ.extend T)} :
        Stable body → Stable (.forallLayout T body)

  Note: this `sll.open_` emits heaplets on open (design-decisions entry 14).
-/

import AlgebraicLayouts.ExprInterp

/-! ## Toy symbolic backend -/

/-- Assertions, with HOAS binders over location/value names. -/
inductive Asn where
  | emp
  | pure (s : String)
  | pt (loc : String) (off : Nat) (val : String)
  | sep (a b : Asn)
  | or (a b : Asn)
  | ex (body : String → Asn)

def Asn.render : Nat → Asn → String
  | _, .emp => "emp"
  | _, .pure s => s
  | _, .pt l 0 v => s!"{l} ↦ {v}"
  | _, .pt l o v => s!"({l}+{o}) ↦ {v}"
  | n, .sep a b => s!"{a.render n} * {b.render n}"
  | n, .or a b => s!"({a.render n}) ∨ ({b.render n})"
  | n, .ex body => s!"∃x{n}. " ++ (body s!"x{n}").render (n + 1)

def renderBase : (b : Base) → b.interp → String
  | .int, v => toString v
  | .bool, v => toString v
  | .unit, _ => "()"

instance : Backend Asn where
  Val _ := String
  const {b} v := renderBase b v
  add x y := s!"({x} + {y})"
  eq x y := s!"({x} = {y})"
  cond c p q := .or (.sep (.pure c) p) (.sep (.pure s!"¬{c}") q)
  unit := .emp
  op := .sep

/-- Singly-linked list layout: head at +0, tail at +1, Nil = null. -/
def sll : SemLayout Asn intList where
  Rep := String
  dict :=
    { put := fun layer dest => match layer with
        | .inl _ => .pure s!"{dest} = null"
        | .inr (h, t) => .sep (.pt dest 0 h.down) (.pt dest 1 t.down)
      open_ := fun k dest =>
        .or (.sep (.pure s!"{dest} = null") (k (.inl ⟨"()"⟩)))
            (.ex fun h => .ex fun t =>
              .sep (.sep (.pt dest 0 h) (.pt dest 1 t)) (k (.inr (⟨h⟩, ⟨t⟩))))
      fresh := fun f => .ex f }

inductive Names : Adt → Type where
  | sll : Names intList

def sigSemToy : {T : Adt} → Names T → SemLayout Asn T
  | _, .sll => sll

def topK {B : Type 1} (show_ : B → String) : B → ULift.{1} Asn := fun v => ⟨.pure s!"result = {show_ v}"⟩

-- close Nil at sll
def nilProg : Expr (Sig := Names) (Δ := .empty) .empty (.atL intList (.concrete .sll)) :=
  .close (.inl (.lit (b := .unit) ()))

def emptyEnv : Env Asn (Sig := Names) sigSemToy (Δ := .empty) .empty (fun l => nomatch l) :=
  fun x => nomatch x

#eval ((nilProg.interp Asn sigSemToy (fun l => nomatch l) emptyEnv)
         (topK fun v => v.down)).down.render 0

-- build Nil, then open it and return 1 if Nil else 2
def openProg : Expr (Sig := Names) (Δ := .empty) .empty (.base .int) :=
  .open_ (r := .concrete .sll) nilProg
    (.matchSum (.var .here) (.lit (b := .int) 1) (.lit (b := .int) 2)) (by constructor)

#eval ((openProg.interp Asn sigSemToy (fun l => nomatch l) emptyEnv)
         (topK fun v => v.down)).down.render 0
