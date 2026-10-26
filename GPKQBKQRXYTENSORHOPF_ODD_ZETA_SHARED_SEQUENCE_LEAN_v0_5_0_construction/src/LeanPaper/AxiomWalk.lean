import Lean

/-!
Independent transitive axiom walk for the Leaned Paper audit.

This uses a visited-only dependency traversal, never the exported per-constant
axiom table. See leanprover/lean4 issue 15226 (imported inductive axiom-cache
under-reporting). The traversal shape follows Lean 4.29.1
`src/Lean/Util/CollectAxioms.lean` (Apache-2.0, Microsoft Corporation,
Leonardo de Moura); this implementation additionally records missing constants
and traverses mutual inductive members and recursor rules.

The union over all roots is the audit result. Visited nodes are never assigned
an intermediate per-node axiom set, so a cycle cannot create an empty cached
answer for another root. This is executable audit machinery, not a theorem
proving the auditor correct.
-/

namespace LeanPaper.AxiomWalk

open Lean

structure Result where
  visited : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}
  deriving Inhabited

/-- Traverse full constant expressions in a private environment. A missing
constant is recorded so the caller can reject incomplete inspection. -/
partial def visit (env : Environment) (decl : Name) : StateM Result Unit := do
  if (← get).visited.contains decl then
    return
  modify fun s => { s with visited := s.visited.insert decl }
  let visitExpr (e : Expr) : StateM Result Unit :=
    e.getUsedConstants.forM (visit env)
  match env.find? decl with
  | some (.axiomInfo v) =>
      modify fun s => { s with axioms := s.axioms.insert decl }
      visitExpr v.type
  | some (.defnInfo v) => visitExpr v.type *> visitExpr v.value
  | some (.thmInfo v) => visitExpr v.type *> visitExpr v.value
  | some (.opaqueInfo v) => visitExpr v.type *> visitExpr v.value
  | some (.quotInfo v) => visitExpr v.type
  | some (.ctorInfo v) => visitExpr v.type *> visit env v.induct
  | some (.inductInfo v) =>
      visitExpr v.type
      v.all.forM (visit env)
      v.ctors.forM (visit env)
  | some (.recInfo v) =>
      visitExpr v.type
      v.all.forM (visit env)
      v.rules.forM fun rule => do
        visit env rule.ctor
        visitExpr rule.rhs
  | none => modify fun s => { s with missing := s.missing.insert decl }

/-- One complete graph union for all roots, independent of root order. -/
def collect (env : Environment) (roots : Array Name) : Result :=
  ((roots.forM (visit (env.setExporting false))).run {}).2

/-- Reject an incomplete graph or any axiom outside the caller's allowlist. -/
def check (result : Result) (allowed : List Name) : Except String Unit := do
  let missing := result.missing.toArray.qsort Name.lt
  if !missing.isEmpty then
    throw s!"AXIOM_WALK_MISSING_CONSTANTS {missing.toList}"
  let extras := (result.axioms.toArray.filter fun ax => !(allowed.contains ax)).qsort Name.lt
  if !extras.isEmpty then
    throw s!"AXIOM_WALK_UNTRUSTED_AXIOMS {extras.toList}"

end LeanPaper.AxiomWalk

