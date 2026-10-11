-- Abstract layouts --
-- This is used to compare other backends to

import AlgebraicLayouts.Syntax
import AlgebraicLayouts.TyInterp

variable (P : Type) [Backend P]

inductive AVal (body : Poly 1) : Poly 1 → Type where
  | base {b : Base} (x : Backend.Val P b) : AVal body (.base b)
  | roll {i : Fin 1} (v : AVal body body) : AVal body (.var i)
  | inl {a b : Poly 1} (v : AVal body a) : AVal body (.sum a b)
  | inr {a b : Poly 1} (v : AVal body b) : AVal body (.sum a b)
  | pair {a b : Poly 1} (v : AVal body a) (w : AVal body b) : AVal body (.prod a b)

/-- One layer (with abstract values at recursive positions) to an abstract value. -/
def AVal.ofLayer {body : Poly 1} :
    (p : Poly 1) → p.interp1 P (fun _ => ULift (AVal P body body)) → AVal P body p
  | .base _, x => .base x.down
  | .var _, v => .roll v.down
  | .sum a _, .inl x => .inl (AVal.ofLayer a x)
  | .sum _ b, .inr y => .inr (AVal.ofLayer b y)
  | .prod a b, (x, y) => .pair (AVal.ofLayer a x) (AVal.ofLayer b y)

/-- An abstract value to one layer. -/
def AVal.toLayer {body : Poly 1} :
    (p : Poly 1) → AVal P body p → p.interp1 P (fun _ => ULift (AVal P body body))
  | .base _, .base x => ⟨x⟩
  | .var _, .roll v => ⟨v⟩
  | .sum _ _, .inl x => .inl (AVal.toLayer _ x)
  | .sum _ _, .inr y => .inr (AVal.toLayer _ y)
  | .prod _ _, .pair x y => (AVal.toLayer _ x, AVal.toLayer _ y)

/-- Non-recursive shapes: values with backend leaves. -/
def Poly.interpV : Poly 0 → Type
  | .base b => Backend.Val P b
  | .var i => i.elim0
  | .sum a b => a.interpV ⊕ b.interpV
  | .prod a b => a.interpV × b.interpV

def Poly.ofLayer0 : (p : Poly 0) → p.interp1 P Fin.elim0 → p.interpV P
  | .base _, x => x.down
  | .var i, _ => i.elim0
  | .sum a _, .inl x => .inl (Poly.ofLayer0 a x)
  | .sum _ b, .inr y => .inr (Poly.ofLayer0 b y)
  | .prod a b, (x, y) => (Poly.ofLayer0 a x, Poly.ofLayer0 b y)

def Poly.toLayer0 : (p : Poly 0) → p.interpV P → p.interp1 P Fin.elim0
  | .base _, x => ⟨x⟩
  | .var i, _ => i.elim0
  | .sum a _, .inl x => .inl (Poly.toLayer0 a x)
  | .sum _ b, .inr y => .inr (Poly.toLayer0 b y)
  | .prod a b, (x, y) => (Poly.toLayer0 a x, Poly.toLayer0 b y)

def Abs (T : Adt) : SemLayout P T :=
  match T with
  | .plain p =>
      { Rep := p.interpV P
      , dict :=
          { close_ := fun u k => k (Poly.ofLayer0 P p u)
          , open_ := fun k v => k (Poly.toLayer0 P p v)
          }
      }

  | .mu body =>
      { Rep := AVal P body body
      , dict :=
          { close_ := fun u k => k (AVal.ofLayer P body u)
          , open_ := fun k v => k (AVal.toLayer P body v)
          }
      }

theorem AVal.toLayer_ofLayer {body : Poly 1} :
    (p : Poly 1) → (u : p.interp1 P (fun _ => ULift (AVal P body body))) →
      AVal.toLayer P p (AVal.ofLayer P p u) = u
  | .base _, _ => rfl
  | .var _, _ => rfl
  | .sum a _, .inl x => by
      show Sum.inl (AVal.toLayer P a (AVal.ofLayer P a x)) = _
      rw [AVal.toLayer_ofLayer a x]
  | .sum _ b, .inr y => by
      show Sum.inr (AVal.toLayer P b (AVal.ofLayer P b y)) = _
      rw [AVal.toLayer_ofLayer b y]
  | .prod a b, (x, y) => by
      show (AVal.toLayer P a (AVal.ofLayer P a x), AVal.toLayer P b (AVal.ofLayer P b y)) = _
      rw [AVal.toLayer_ofLayer a x, AVal.toLayer_ofLayer b y]
