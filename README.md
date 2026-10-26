# Odd-zeta conjecture: Lean formalization

This repository contains the [endpoint manuscript](ZH_Odd_Zeta_Endpoints_v0_1_construction.pdf) and the shared-sequence Lean construction.

## Lean package

[Open the complete v0.5.0 package](GPKQBKQRXYTENSORHOPF_ODD_ZETA_SHARED_SEQUENCE_LEAN_v0_5_0_construction/).

The package formalizes a conditional induction on actual primitive polynomial values: a base estimate and adjacent positive-power comparisons along one common sampling sequence imply a logarithmic divergence invariant and irrationality of odd zeta values from weight five onward. The all-odd endpoint takes irrationality of zeta(3) as a separate input.

The successful base sequence and actual induction-transfer estimates remain open. The new v0.5.0 sources have static review and runner mock checks; native Lean compilation and axiom audit are pending. The retained v0.4.0 router has a user-reported native Windows build and axiom-audit PASS. This repository does not claim unconditional irrationality of all odd zeta values.

Main files:

- [SequenceRates.lean](GPKQBKQRXYTENSORHOPF_ODD_ZETA_SHARED_SEQUENCE_LEAN_v0_5_0_construction/src/ZHPreprint/SequenceRates.lean): abstract sampled estimates, induction, and the exact logarithmic limit.
- [SharedSequence.lean](GPKQBKQRXYTENSORHOPF_ODD_ZETA_SHARED_SEQUENCE_LEAN_v0_5_0_construction/src/ZHPreprint/SharedSequence.lean): actual ZH profiles, explicit inputs, and conditional irrationality endpoints.
- [SharedSequenceAudit.lean](GPKQBKQRXYTENSORHOPF_ODD_ZETA_SHARED_SEQUENCE_LEAN_v0_5_0_construction/src/ZHPreprint/SharedSequenceAudit.lean): declaration dependency and axiom audit.
- [CONJECTURE.txt](GPKQBKQRXYTENSORHOPF_ODD_ZETA_SHARED_SEQUENCE_LEAN_v0_5_0_construction/CONJECTURE.txt): exact input quantifiers and proof scope.
- [Package README](GPKQBKQRXYTENSORHOPF_ODD_ZETA_SHARED_SEQUENCE_LEAN_v0_5_0_construction/README.md): native runner and cache requirements.

## Native Windows verification

Use the existing offline Lean 4.33.0 installation, compatible cached Mathlib, and LEAN_ANCHORINGS described in the package README. From the repository root in Windows CMD:

```cmd
call "GPKQBKQRXYTENSORHOPF_ODD_ZETA_SHARED_SEQUENCE_LEAN_v0_5_0_construction\run.cmd"
```

The runner validates source, dependency, and toolchain fingerprints before cache reuse. With matching v0.4.0 receipts, it is expected to reuse 40 modules and compile the three additions. No Lean execution target has been changed by publishing these sources, and no GitHub Actions workflow is included.
