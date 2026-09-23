# Installation and verification

## Requirements and fixed versions

Install [elan](https://lean-lang.org/install/), Git, and Python 3.9 or later.
Open a terminal in the project root, the directory containing `lakefile.lean`.
The supplied `lean-toolchain` selects Lean `v4.35.0-rc2`; `lake-manifest.json`
locks mathlib and all transitive dependencies. Preserve these files and use
the pinned versions when reproducing the proof.

The proof sources work in a Git clone or an extracted source archive. They do
not require Git history, a particular username, an editor, or a parent workspace.

## Obtain dependencies

Check the selected tools and download the dependency cache:

```bash
elan --version
lean --version
lake --version
lake exe cache get
```

The first run can download the pinned compiler and dependencies. Mathlib is
fixed at `0a6c8e0355da0405d616f80b9f8232c4fab2cc5b`. Routine verification does
not require `lake update` or a version upgrade.

## Build and audit

Run the verification script:

```bash
python3 scripts/verify.py --output-dir .verification/run-01
```

Choose a new output directory for each run. The script checks dependency
revisions, builds the root, runs the full axiom audit and both independent
checks, and validates the actual compiler output. It rejects missing audit
entries, unexpected axioms, failed independence checks, and changed sources.
The generated logs and `run.json` are local outputs ignored by Git.

The underlying Lean commands are:

```bash
lake --no-cache build
lake --no-cache env lean Khachiyan/Audit.lean
lake --no-cache env lean audit/Independence.lean
lake --no-cache env lean audit/StatementComparison.lean
```

`--no-cache` prevents Lake from downloading caches during verification; it can
still use dependency artifacts obtained during setup. For a source-only cold
build, prepare the pinned dependency source repositories without compiled Lean
artifacts and add `--require-cold` to the Python command.

`Khachiyan/Audit.lean` inspects all 598 audit entries. The standalone independence
check imports only the resolvent route and rejects project dependencies beyond
the foundational, spectral, M02, and resolvent modules. It covers all 43 public
resolvent declarations. The statement comparison imports both routes and
checks that the final M04/M04R hypotheses and conclusions agree after aligning
implicit binder order.

A successful `lake build` alone does not enforce the axiom policy. The Python
runner validates the axiom output and reports success only when every step
passes. Existing linter warnings in some modules do not indicate proof gaps.

## Editing and sharing

For a small change, check the affected module with `lake env lean` and then run
the complete verification script. Keep `.lake/`, `.verification/`, generated
Lean artifacts, and Python caches out of version control. Public source uploads
need only the supplied files, including the hidden `.gitignore`; maintain their
directory structure.

Fill the copyright-holder placeholder in [LICENSE](LICENSE) with the intended
public name or pseudonym before publishing.
