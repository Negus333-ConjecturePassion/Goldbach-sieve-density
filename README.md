# Sieve-Density Framework for the Goldbach Conjecture (Lean 4)

**This repository does NOT prove Goldbach's Conjecture.**

It contains a machine-verified Lean 4 formalization of a sieve-density
and singular-series scaffold for the Binary Goldbach Conjecture, built
against [Mathlib](https://github.com/leanprover-community/mathlib4).

## What is actually proved (unconditionally, kernel-verified)

- Base cases for small even integers (`goldbach_4`, `goldbach_6`, `goldbach_10`)
- Non-emptiness of a `{2,3}`-filtered candidate offset set for all even `n ≥ 8`
  (`uneliminated_offsets_nonempty`)
- A uniform lower bound on the Hardy–Littlewood singular series,
  `S(n) ≥ 2·C₂` (`singular_series_lower_bound`)

## What is explicitly NOT proved

The file states a hypothesis, `AnalyticDensityBridge`, connecting the
above sieve/density facts to the *pointwise* existence of a prime
offset for every `n`. **No proof of this hypothesis exists in this
repository, or anywhere else** — it is, in the precise sense discussed
in the accompanying paper, equivalent in strength to the Goldbach
Conjecture itself. The main theorem,
`goldbach_conjecture_from_bridge`, is explicitly *conditional* on this
unproven hypothesis, which is visible directly in its type signature.

See the [accompanying paper](paper/Goldbach_Sieve_Density_Framework.pdf) for the full discussion, including why this gap corresponds to an open minor-arc estimate in
the Hardy–Littlewood circle method.

## Build status

[![Lean Build](https://github.com/YOUR-USERNAME/goldbach-sieve-density/actions/workflows/lean_build.yml/badge.svg)](https://github.com/YOUR-USERNAME/goldbach-sieve-density/actions/workflows/lean_build.yml)

Built with `lake build` against Mathlib. Verified: 1944/1944 jobs,
exit code 0, zero uses of `sorry`.

## Building locally

```sh
lake exe cache get   # fetch Mathlib's prebuilt cache
lake build
```

## License

MIT (see `LICENSE`).

## Author

Dr. Gregory C. Stamp, Independent Researcher.
