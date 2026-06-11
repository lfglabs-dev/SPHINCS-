# WIP axiom-discharge probes (2026-06-11)

Standalone probe files validating discharges of the four remaining
composition-glue axioms in `SphincsMinusVerifiers/Proofs.lean` before the
proofs are folded in. Compile from `verity/` with:

```
LEAN_NUM_THREADS=2 lake env lean probes/<probe>.lean
```

(High RAM: ~22 GB RSS each. Run under an RSS watchdog on constrained hosts.)

- `probe_inputs_layer0.lean` — discharges
  `c13_ok_beforeAuthOff_wotsPk_lightweight_chain_inputs_layer0`
  (Proofs.lean:11296). Per-fact private lemmas (seed0/d0/adrs0/wptr0/cd0 at
  the layer-0 `c13BeforeWotsPkLightState`), each under a fresh
  `maxHeartbeats 2000000` budget, consumed via syntactic `rw` against rfl
  shape lemmas to avoid whnf blowup of the 64-iteration digit fold.
- `probe_reverted_layer0.lean` — discharges
  `c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual`
  (Proofs.lean:12014) by reusing the same per-fact lemmas and feeding a
  `C13WotsOuterEntry` into
  `c13RevertedLayer0_copyFold43_wotsChainsEnd_cells_of_inputs`.

Once both probes compile with clean `#print axioms`, the helper lemmas and
proofs are folded into Proofs.lean, replacing the two `axiom` declarations,
and this directory is removed.
