/-
# Fail-closed transitive proof-integrity audit

Unlike a list of `#print axioms` commands, this audit rejects any project declaration
whose transitive axioms are not on the logical whitelist. It checks every declaration
in the project's mathematical namespace reachable through the root import, including
auxiliary declarations, rather than a manually selected theorem list.

Run with `lake env lean GUEStrongConvergence/Verification/Integrity.lean` after `lake build`.
This is metaprogramming for verification only; it introduces no mathematical axioms.
-/
import GUEStrongConvergence
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`GUEStrongConvergence).isPrefixOf name then
      match info with
      | .axiomInfo _ => throwError "Project axiom declaration rejected: {name}"
      | _ => pure ()
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      count := count + 1
  logInfo m!"Integrity audit passed: {count} project declarations; only propext, Classical.choice, Quot.sound allowed."
