# Finite-range Gaussian thermal reservoirs

**Publicly accessible AI-assisted research candidate. Not peer reviewed, accepted, or formally released for submission.** This checkout does not imply a priority finding, an authorship decision, or a license grant. See [release gates](RELEASE_GATES.md).

- [Manuscript (PDF)](manuscript.pdf), [LaTeX source](manuscript.tex)
- [Exact range-two proof](RANGE2_EXACT_PROOF.md), [formal model and theorem map](THEOREM_MODEL_AUDIT.md), [range-two Lean theorem](RangeTwoClosure.lean)
- [Prior-art review](PRIOR_ART.md), [range-two addendum](PRIOR_ART_RANGE2_ADDENDUM.md), [scope and archive notes](ARCHIVE_AND_SCOPE.md)
- [Evidence and limitations](ENGINEERING_ACCEPTANCE.json), [verifier accounting](VERIFIER_ACCOUNTING.md), [latest checked Windows evidence](RangeTwoClosureWindowsEvidence_2026-11-26.zip)

The main additions to the known scalar majorant relaxation are the strict physical gap for $r\ge2$, a sharp constructive physical critical coefficient at fixed range, and the attained all-mass $r=2$ optimum with three distinct positive temperatures and three real FIR channels. The result concerns **degree-bounded individual rates**, not all microscopic local bath models. The exact general SDP characterizes the physical infimum; existence of an SDP minimum does not prove that a physical optimum is attained for $r\ge3$. The scalar relaxation and its critical coefficient, and the nearest-neighbor optimum, are prior results; the general spectral-factorization and matrix-moment machinery is classical. The literature review is targeted, not proof of priority.

## Replay on a fresh checkout

Python 3.11 or newer and Git are required. Install Lean/Lake **4.28.0** (for example using [elan](https://github.com/leanprover/elan)); both commands must resolve to that version. Prepare a separate Mathlib checkout once:

```sh
git clone https://github.com/leanprover-community/mathlib4.git mathlib4
git -C mathlib4 checkout 8f9d9cff6bd728b17a24e163c9402775d9e6a365
cd mathlib4
lake exe cache get
cd ..
```

From this repository, substitute the actual location of that checkout:

```sh
python -m pip install -r requirements-replay.txt
python reproduce.py --mathlib /path/to/mathlib4 --run-tests
```

Windows PowerShell equivalent: `./reproduce.ps1 -Mathlib C:\path\to\mathlib4 -RunTests`. Specify `-LeanBin` or `--lean-bin` if Lean and Lake are not on PATH. To run only the 17 Python verifiers, use `python reproduce.py --python-only`. The runner refuses an incorrect Lean or Mathlib revision and writes a new isolated evidence directory (use `--output NEW-DIRECTORY` to choose its name). Python verifiers run on copies so tracked JSON is not overwritten.

The pinned historical record is a staged project replay of 45 Lean modules (32+2+2+5+3+1), not one all-45 invocation or a clean rebuild of Mathlib itself. It reports 87 representative axiom audits, 43,300 historical finite test units, and 10 additional universal symbolic certificate groups reported separately. Lean proves the specified discrete Fourier/FIR theorem statements; the physical interpretation, limits obtained by squeeze, and the general finite-dimensional SDP-coordinate/compactness argument also use analytic reasoning. The full historical archive is not included in this checkout. To check a copy of that full archive, run `python verify_package.py FULL_ARCHIVE.zip`; this is an **integrity check**, not a fresh scientific replay.

To check this GitHub snapshot locally: `sha256sum -c GITHUB_SHA256SUMS.txt` (or `python reproduce.py --check-manifest`).
