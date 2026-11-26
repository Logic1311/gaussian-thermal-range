param([string]$Mathlib='D:\TheoryScienceResearch\mathlib4', [string]$LeanBin='D:\GraphReconstructionResearch\lean-4.28.0-windows\bin', [switch]$RunTests)
$ErrorActionPreference='Continue'
$root=$PSScriptRoot
$env:PATH=$LeanBin+';'+$env:PATH
$logdir=Join-Path $root 'reproduction_logs'
New-Item -ItemType Directory -Force $logdir | Out-Null
Set-Location $Mathlib
& lean --version | Tee-Object (Join-Path $logdir 'lean-version.txt')
& git rev-parse HEAD | Tee-Object (Join-Path $logdir 'mathlib-commit.txt')
$modules=@('Core','Entropy','FourierBridge','Integrated','Compression','Boundary','CompressionExistence','PhysicalCompression','PhysicalInfimum','PathConstruction','PathSpectrumCore','PathSpectralLink','PathResidual','RelaxationAlgebra','RelaxationPower','FinalAudit','RealFactorBase','RealFactorization','TrigSymmetry','RateEquivalence','RelaxationGap','MajorantBridge','MajorantExact','FullAudit','PointwiseBarrier','PointwiseBound','FiniteGapBound','FiniteGapStrict','FiniteGapAudit','CriticalEnergy','CriticalRealization','CriticalScaling','TemperatureCount','ThreeTemperature','TemperatureResourceLower','TemperatureResource','SDPSpectral','SDPMoments','SDPRealization','SDPReference','SDPExact','RangeTwoCoordinates','RangeTwoAlgebra','RangeTwoExact','RangeTwoClosure')
foreach($n in $modules){
  $file=Join-Path $root ($n+'.lean')
  $out=Join-Path $root ($n+'.olean')
  $log=Join-Path $logdir ($n+'.log')
  $cmd="`$env:LEAN_PATH='$root;'+`$env:LEAN_PATH; lean --root='$root' -o '$out' '$file'"
  & lake env powershell -NoProfile -Command $cmd 2>&1 | Tee-Object $log
  $e=$LASTEXITCODE
  [IO.File]::WriteAllText((Join-Path $logdir ($n+'.exit.txt')), "LEAN_EXIT=$e")
  if($e -ne 0){throw "Lean failed: $n (exit $e)"}
  $bad=Select-String -Path $log -Pattern 'depends on axioms:.*sorryAx|error:|error\('
  if($bad){throw "Audit failed: $n"}
}
if($RunTests){
  & python --version | Tee-Object (Join-Path $logdir 'python-version.txt')
  & python -c 'import sympy; print(sympy.__version__)' | Tee-Object (Join-Path $logdir 'sympy-version.txt')
  foreach($n in @('verify_window_v2','verify_rational_window','verify_cyclic_coefficients','verify_compression','verify_path_exact','verify_new_compression','verify_relaxation','verify_schur_physical','verify_real_factorization','verify_finite_gap','verify_finite_gap_path','verify_critical_limit','verify_temperature_count','verify_temperature_resource','verify_exact_sdp','verify_range2_algebraic','verify_range2_closure')){
    & python (Join-Path $root ($n+'.py')) 2>&1 | Tee-Object (Join-Path $logdir ($n+'.log'))
    $e=$LASTEXITCODE
    [IO.File]::WriteAllText((Join-Path $logdir ($n+'.exit.txt')), "PYTHON_EXIT=$e")
    if($e -ne 0){throw "Python failed: $n (exit $e)"}
  }
}
Write-Output 'REPRODUCTION_EXIT=0'