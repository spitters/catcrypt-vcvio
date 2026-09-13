# Contributing

Contributions to CatCrypt VCVio are welcome.

## Building

See [BUILDING.md](BUILDING.md). Install
[elan](https://github.com/leanprover/elan), clone CatCrypt Core as the sibling
directory `../CatCrypt-core`, then

```
lake exe cache get
lake build
```

## Ground rules

- **No `sorry`/`admit`.** The package is built under `-E hasSorry`, so a
  declaration whose proof reaches `sorry` fails the build and CI.
- **No axioms, no `native_decide`.** The package declares no axioms; CI rejects
  `native_decide`, which adds the `Lean.ofReduceBool` trust edge. A new trust edge
  needs an issue first, with a justification.
- **`autoImplicit false`** is set package-wide; keep it.
- Every file carries the standard copyright header (MIT, "CatCrypt
  Contributors") and a `/-! ... -/` module docstring stating what is proved and,
  where relevant, what is not.
- Results that belong to CatCrypt alone, without VCV-io, go to
  [CatCrypt Core](https://github.com/spitters/CatCrypt-core) rather than here.

## Pull requests

Keep PRs focused. A PR that adds a lemma should not also reformat
neighbouring proofs. CI must pass; please run `lake build` locally before
submitting.

## Reporting issues

Use the GitHub issue tracker. For suspected unsoundness (an axiom that
proves too much, a vacuous statement), please mark the issue as
such; these take priority.
