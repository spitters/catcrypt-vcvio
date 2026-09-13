# Building

## The library

Requires [elan](https://github.com/leanprover/elan). The pinned toolchain is
`leanprover/lean4:v4.33.1` (see `lean-toolchain`).

`lakefile.lean` requires CatCrypt Core from the sibling directory
`../CatCrypt-core`, so clone it next to this repository first:

```
git clone https://github.com/spitters/CatCrypt-core ../CatCrypt-core
```

Then, from the repository root:

```
lake exe cache get    # pull the Mathlib olean cache
lake build
```

`lake build` builds the default target, the `CatCryptVCVio` library. The package
passes `-E hasSorry` to Lean (see `lakefile.lean`), so a declaration whose proof
reaches `sorry` fails the build. The Mathlib cache covers Mathlib only; VCV-io and
CatCrypt Core are compiled from source on the first build.

## The documentation

**API reference** (`docbuild/`, doc-gen4) — per-declaration HTML for every module
of the library. The documentation build is its own package, so doc-gen4 does not
become a dependency of code that requires the library:

```
cd docbuild && lake update && lake exe cache get && lake build CatCryptVCVio:docs
```

Output in `docbuild/.lake/build/doc/` (open `index.html`). The library's
`.andSubmodules` glob makes the `CatCryptVCVio` umbrella module the documentation
root. The hosted copy at <https://spitters.github.io/catcrypt-vcvio/> is this
build, published by `.github/workflows/docs.yml`.
