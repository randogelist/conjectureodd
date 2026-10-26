# ZH shared-sequence induction: v0.5.0 construction

This package formalizes the proposed weaker base-and-step interface.
Read CONJECTURE.txt for its exact quantifiers and remaining inputs.

Mode: A_TIER_LEAN. Target: LOCAL_COMPILER. Native Lean: 4.33.0.
New source compilation and independent dependency audit remain pending.
No Lean, leanchecker, Lake, or Windows executable ran on the authoring host.

The construction uses one strictly increasing sample sequence across all
weights. An increasingly strong exponential base bound and eventual
positive-power comparisons at those sampled indices yield denominator
squeezes. The source also states the logarithmic invariant using Filter.Tendsto:
the negative log of each sampled product, divided by its sampled time,
tends to positive infinity. These new proofs await native compilation/audit.
The endpoint concerns conditional irrationality, with zeta(3)
separate. It does not construct the base sequence or induction estimates,
and it does not assert quadratic decay or a separated ProfileGap.

All 44 Lean sources present in v0.4.0 are preserved byte-for-byte, including
historical audit sources. The active plan retains its first 40 modules and adds:
  ZHPreprint.SequenceRates
  ZHPreprint.SharedSequence
  ZHPreprint.SharedSequenceAudit

The LEAN_ANCHORINGS location, receipt schema, environment fingerprints,
compiler options, and per-module dependency keys are unchanged. With
matching successful v0.4.0 receipts, the expected run reuses 40 modules,
compiles 3, and performs no historical kernel replay. Prior audit receipts
remain untouched. User-reported console evidence is recorded separately;
reuse still requires matching native source/dependency/toolchain fingerprints.

The independent audit walks actual declaration dependencies and rejects
axioms outside propext/Classical.choice/Quot.sound. Every open estimate
remains explicit. The passed old source files are never rewritten.

Run the single run.cmd from native Windows CMD. It uses compatible cached
Mathlib and project anchorings, cscript/JScript, and the offline batch hash
helper. It installs nothing and uses no Python, PowerShell, WSL, or Lake.
Keep prior packages and the native cache. Do not run two copies concurrently
against the same anchor directory.

Canonical log: GOODWORKFLOWFRONTIER_v0_5_0.log.
Previous router documentation is archived under history/v0_4_0_*.
Static preparation checks and mock simulations are not native Lean passes.
