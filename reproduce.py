"""Pinned, out-of-tree replay of the public Gaussian thermal study."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
LEAN_VERSION = "4.28.0"
MATHLIB_COMMIT = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULES = ('Core',
 'Entropy',
 'FourierBridge',
 'Integrated',
 'Compression',
 'Boundary',
 'CompressionExistence',
 'PhysicalCompression',
 'PhysicalInfimum',
 'PathConstruction',
 'PathSpectrumCore',
 'PathSpectralLink',
 'PathResidual',
 'RelaxationAlgebra',
 'RelaxationPower',
 'FinalAudit',
 'RealFactorBase',
 'RealFactorization',
 'TrigSymmetry',
 'RateEquivalence',
 'RelaxationGap',
 'MajorantBridge',
 'MajorantExact',
 'FullAudit',
 'PointwiseBarrier',
 'PointwiseBound',
 'FiniteGapBound',
 'FiniteGapStrict',
 'FiniteGapAudit',
 'CriticalEnergy',
 'CriticalRealization',
 'CriticalScaling',
 'TemperatureCount',
 'ThreeTemperature',
 'TemperatureResourceLower',
 'TemperatureResource',
 'SDPSpectral',
 'SDPMoments',
 'SDPRealization',
 'SDPReference',
 'SDPExact',
 'RangeTwoCoordinates',
 'RangeTwoAlgebra',
 'RangeTwoExact',
 'RangeTwoClosure')
VERIFIERS = ('verify_window_v2',
 'verify_rational_window',
 'verify_cyclic_coefficients',
 'verify_compression',
 'verify_path_exact',
 'verify_new_compression',
 'verify_relaxation',
 'verify_schur_physical',
 'verify_real_factorization',
 'verify_finite_gap',
 'verify_finite_gap_path',
 'verify_critical_limit',
 'verify_temperature_count',
 'verify_temperature_resource',
 'verify_exact_sdp',
 'verify_range2_algebraic',
 'verify_range2_closure')


def capture(cmd, *, cwd=None, env=None):
    return subprocess.check_output(cmd, cwd=cwd, env=env, stderr=subprocess.PIPE, text=True).strip()


def run(cmd, log, *, cwd, env=None):
    print(log.stem, flush=True)
    with log.open("wb") as out:
        result = subprocess.run(cmd, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT)
    log.with_suffix(".exit.txt").write_text(f"{result.returncode}\n", encoding="ascii")
    if result.returncode:
        raise RuntimeError(f"{log.stem} failed (exit {result.returncode}); see {log}")
    return log.read_text(encoding="utf-8", errors="replace")


def verify_manifest():
    manifest = ROOT / "GITHUB_SHA256SUMS.txt"
    entries = manifest.read_text(encoding="utf-8").splitlines()
    for line in entries:
        expected, name = line.split("  ", 1)
        item = ROOT / name
        if not item.is_file() or hashlib.sha256(item.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"manifest mismatch: {name}")
    print(f"{len(entries)} manifest entries verified")


def lean_replay(args, out):
    env = os.environ.copy()
    mathlib = args.mathlib.resolve(strict=True)
    if args.lean_bin:
        env["PATH"] = str(args.lean_bin.resolve(strict=True)) + os.pathsep + env["PATH"]
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    version = capture(["lean", "--version"], cwd=mathlib, env=env)
    lake_version = capture(["lake", "--version"], cwd=mathlib, env=env)
    if not re.search(r"\bversion " + re.escape(LEAN_VERSION) + r"\b", version):
        raise RuntimeError(f"expected Lean {LEAN_VERSION}, got {version}")
    if not re.search(r"\bLean version " + re.escape(LEAN_VERSION) + r"\b", lake_version, re.IGNORECASE):
        raise RuntimeError(f"expected Lake for Lean {LEAN_VERSION}, got {lake_version}")
    rev = capture(["git", "rev-parse", "HEAD"], cwd=mathlib)
    if rev != MATHLIB_COMMIT:
        raise RuntimeError(f"expected Mathlib {MATHLIB_COMMIT}, got {rev}")
    if capture(["git", "status", "--porcelain", "--untracked-files=no"], cwd=mathlib):
        raise RuntimeError("Mathlib tracked files are modified")
    out.joinpath("versions.txt").write_text(f"{version}\n{lake_version}\n{rev}\n", encoding="utf-8")
    deps = capture(["lake", "env", "printenv", "LEAN_PATH"], cwd=mathlib, env=env) if os.name != "nt" else capture(
        ["lake", "env", "cmd.exe", "/d", "/c", "echo %LEAN_PATH%"], cwd=mathlib, env=env
    )
    if not deps or deps == "%LEAN_PATH%":
        raise RuntimeError("Lake returned no dependency path; prepare Mathlib with lake exe cache get")
    if not any((Path(entry) / "Mathlib" / "Tactic.olean").is_file() for entry in deps.split(os.pathsep) if entry):
        raise RuntimeError("Mathlib/Tactic.olean was not found; finish preparing the pinned Mathlib cache first")
    compile_dir = out / "oleans"
    compile_dir.mkdir()
    env["LEAN_PATH"] = str(compile_dir) + os.pathsep + deps
    checks = []
    for module in MODULES:
        log = run(["lean", f"--root={ROOT}", "-o", str(compile_dir / f"{module}.olean"), str(ROOT / f"{module}.lean")],
                  out / f"{module}.log", cwd=mathlib, env=env)
        if re.search(r"\b(?:error:|uses ['`]?sorry\b)", log):
            raise RuntimeError(f"Lean reported an error or admitted declaration: {module}")
        for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
            nonstandard = {n.strip() for n in axioms.split(",") if n.strip()} - STANDARD_AXIOMS
            if nonstandard:
                raise RuntimeError(f"nonstandard axiom dependency: {name}: {sorted(nonstandard)}")
            checks.append(name)
    if not {"GaussianRange.range2_complete", "GaussianRange.exact_sdp_infimum"} <= set(checks):
        raise RuntimeError("missing core axiom audit output")
    return {"modules": len(MODULES), "standard_axiom_records": len(checks)}


def python_replay(out):
    if sys.version_info < (3, 11):
        raise RuntimeError("Python 3.11 or newer is required")
    import numpy
    import sympy

    required = dict(line.split("==") for line in (ROOT / "requirements-replay.txt").read_text().splitlines() if line)
    installed = {"numpy": numpy.__version__, "sympy": sympy.__version__}
    if installed != required:
        raise RuntimeError(f"Python package versions {installed} do not match {required}")
    replay = out / "python"
    replay.mkdir()
    for script in VERIFIERS:
        shutil.copy2(ROOT / f"{script}.py", replay)
    for source in ROOT.glob("*.json"):
        shutil.copy2(source, replay)
    for script in VERIFIERS:
        run([sys.executable, f"{script}.py"], out / f"{script}.log", cwd=replay)
    return {"verifiers": len(VERIFIERS), "python": sys.version, "packages": installed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, help="path to a clean, pinned Mathlib checkout")
    parser.add_argument("--lean-bin", type=Path, help="directory containing Lean and Lake binaries")
    parser.add_argument("--output", type=Path, help="new directory for logs, objects and copied verifier inputs")
    parser.add_argument("--run-tests", action="store_true", help="also run the Python scientific verifiers")
    parser.add_argument("--python-only", action="store_true", help="skip Lean and run only the scientific verifiers")
    parser.add_argument("--check-manifest", action="store_true", help="verify the public snapshot without replay")
    args = parser.parse_args()
    if args.check_manifest:
        verify_manifest()
        return
    if not args.python_only and args.mathlib is None:
        parser.error("--mathlib is required unless --python-only or --check-manifest is specified")
    if args.output:
        out = args.output.resolve()
        out.mkdir()
    else:
        out = Path(tempfile.mkdtemp(prefix="reproduction-", dir=ROOT))
    print(f"Evidence folder: {out}", flush=True)
    report = {}
    if not args.python_only:
        report["lean"] = lean_replay(args, out)
    if args.python_only or args.run_tests:
        report["python"] = python_replay(out)
    out.joinpath("result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("REPRODUCTION_EXIT=0", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.CalledProcessError, ImportError) as exc:
        print(f"Replay failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
