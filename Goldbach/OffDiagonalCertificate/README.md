# Public Lean extraction: Off-Diagonal Certificate

This directory is a deliberately small public formalization of the structural
logic used in the accompanying paper.

It proves, over the *actual prime-generated displacement support* `k = p+q-N`:

1. `k = 0` is exactly the Goldbach representation fiber `p+q=N`;
2. every populated displacement satisfies `|k| < N` for even `N >= 4`;
3. for `Q=N/3` and `M=2`, the lobe-pair window contains the full populated support;
4. for any real signed displacement weight `τ`, positivity of the residue imbalance
   `Δ_r = positive mass - negative-magnitude mass` is equivalent to strict
   positive-over-negative domination;
5. consequently, for even `N >= 56`, `Δ_r > 0` implies that the negative mass is
   strictly smaller than the intrinsic favorable core.

## Scope

The public extraction is intentionally structural. It does **not** formalize:
- the Ramaré–Rumely analytic estimates;
- the Python-FLINT/Arb finite certificate;
- the proprietary derivation of the concrete displacement-weight formula.

The paper supplies the concrete analytic displacement weight. The Lean theorem is
stated for an arbitrary real displacement weight `τ`, so the structural result is
stronger than the single concrete specialization while disclosing no unnecessary
research-path implementation details.

Run:

```bash
lake build Goldbach.OffDiagonalCertificate.Audit
```

and inspect the `#print axioms` output.
