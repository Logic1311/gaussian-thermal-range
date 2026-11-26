param([string]$Mathlib, [string]$LeanBin, [string]$Output, [switch]$RunTests, [switch]$PythonOnly)
$ErrorActionPreference = 'Stop'
# Historical build order, retained for existing consumers. Execution delegates to reproduce.py.
$modules=@('Core','Entropy','FourierBridge','Integrated','Compression','Boundary','CompressionExistence','PhysicalCompression','PhysicalInfimum','PathConstruction','PathSpectrumCore','PathSpectralLink','PathResidual','RelaxationAlgebra','RelaxationPower','FinalAudit','RealFactorBase','RealFactorization','TrigSymmetry','RateEquivalence','RelaxationGap','MajorantBridge','MajorantExact','FullAudit','PointwiseBarrier','PointwiseBound','FiniteGapBound','FiniteGapStrict','FiniteGapAudit','CriticalEnergy','CriticalRealization','CriticalScaling','TemperatureCount','ThreeTemperature','TemperatureResourceLower','TemperatureResource','SDPSpectral','SDPMoments','SDPRealization','SDPReference','SDPExact','RangeTwoCoordinates','RangeTwoAlgebra','RangeTwoExact','RangeTwoClosure')
$replayArgs = @((Join-Path $PSScriptRoot 'reproduce.py'))
if ($Mathlib) { $replayArgs += @('--mathlib', $Mathlib) }
if ($LeanBin) { $replayArgs += @('--lean-bin', $LeanBin) }
if ($Output) { $replayArgs += @('--output', $Output) }
if ($RunTests) { $replayArgs += '--run-tests' }
if ($PythonOnly) { $replayArgs += '--python-only' }
& python @replayArgs
exit $LASTEXITCODE
