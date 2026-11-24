/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Verification.TraceHash
public meta import Lean

/-! Internal dispatch for weighted trace hashes with checked coefficient evidence. -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command EllipticCurve

/-- Check the reported hash when the caller proves all coefficients in its source vector. -/
def certifyTraceHash (base : Name) : CommandElabM Unit := do
  let some claim ← bindStored base `traceHash `trace_hash (← `(Int)) | return
  let attachment := base ++ `integral_proofs
  let proof ← if (← getEnv).contains attachment then
    attachedFact (some (rootIdent attachment)) `traceHashCoefficients
  else pure none
  let some proof := proof | do
    logInfo m!"Unverified {base} trace_hash: supply all prescribed arithmetic coefficients"
    return
  let curve := rootIdent (base ++ `curve)
  let evidence := base ++ `trace_hash_coefficients
  let source := rootIdent evidence
  emit (← `(def $source : TraceHashCoefficients $curve := $proof))
  auditAxioms evidence
  let valid := base ++ `trace_hash_value_valid
  withScope (fun scope => { scope with opts := scope.opts.set `maxRecDepth (6000 : Nat) }) do
    checked valid (← `(computeLmfdbTraceHash ($source).coefficients = $claim))
      (← `(by first | rfl | exact of_decide_eq_true rfl | decide +kernel))
  let hash := base ++ `trace_hash_fact
  emit (← `(def $(rootIdent hash) : TraceHashFact $curve :=
    Certification.traceHashFact $curve $source $claim $(rootIdent valid)))

end VerifiedLcalc.CertifyEC
