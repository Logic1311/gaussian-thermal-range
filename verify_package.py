"""Read-only integrity/evidence checks; not a new science replay."""
import hashlib, json, re, sys, zipfile
from pathlib import PurePosixPath

def digest(b): return hashlib.sha256(b).hexdigest()
def text(b): return b.decode('utf-16' if b[:2] in (b'\xff\xfe',b'\xfe\xff') else 'utf-8-sig')
def read_zip(z, normalize=False):
    assert z.testzip() is None
    out={}
    for f in z.infolist():
        if f.is_dir(): continue
        n=f.filename.replace('\\','/') if normalize else f.filename
        p=PurePosixPath(n)
        assert '\\' not in n and not p.is_absolute() and '..' not in p.parts and ':' not in n and n not in out,n
        out[n]=z.read(f)
    return out

def manifest(b):
    out={}
    for line in text(b).splitlines():
        h,n=line.split(maxsplit=1);n=n.replace('\\','/')
        assert re.fullmatch('[a-fA-F0-9]{64}',h) and n not in out,line
        out[n]=h.lower()
    return out

def verify_manifest(f):
    m=manifest(f['SHA256SUMS.txt']);assert set(m)==set(f)-{'SHA256SUMS.txt'}
    assert all(digest(f[n])==h for n,h in m.items());return len(m)

def check(path):
    import io
    with zipfile.ZipFile(path) as z:f=read_zip(z)
    nm=verify_manifest(f);assert not any(n.endswith(('.olean','.ilean')) for n in f)
    snapshot='history/pre_range2_closure_snapshot/'
    old=manifest(f[snapshot+'SHA256SUMS.txt']);assert len(old)==1108
    for n,h in old.items():
        key=snapshot+n if snapshot+n in f else n
        assert digest(f[key])==h,n
    active={n for n in f if '/' not in n and n.endswith('.lean')}
    v={n for n in f if '/' not in n and n.startswith('verify_') and n.endswith('.py')}
    assert len(active)==45 and len(v)==17
    assert active-{'RangeTwoClosure.lean'}=={n for n in old if '/' not in n and n.endswith('.lean')}
    assert v-{'verify_range2_closure.py'}=={n for n in old if '/' not in n and n.startswith('verify_') and n.endswith('.py')}
    assert all(digest(f[n])==old[n] for n in (active-{'RangeTwoClosure.lean'})|(v-{'verify_range2_closure.py'}))
    prior=json.loads(text(f[snapshot+'ENGINEERING_ACCEPTANCE.json']))
    assert prior['active_counts']=={'lean_modules':44,'verifiers':16,'representative_axioms':81}
    prefix='evidence/range2_closure/'
    raw=f[prefix+'RangeTwoClosureWindowsEvidence_2026-11-26.zip']
    with zipfile.ZipFile(io.BytesIO(raw)) as z:w=read_zip(z,True)
    raw_count=verify_manifest(w);assert raw_count==30
    assert all(w[n]==f[prefix+'windows_evidence/'+n] for n in w)
    hashes=manifest(w['clean_replay/REPLAY_INPUT_SHA256.txt']);assert set(hashes)==active
    assert all(digest(f[n])==h for n,h in hashes.items())
    assert text(w['clean_replay/STAGED_REPLAY_EXIT.txt']).strip()=='STAGED_REPLAY_EXIT=0'
    assert text(w['clean_replay/mathlib-commit.txt']).strip()=='8f9d9cff6bd728b17a24e163c9402775d9e6a365'
    assert '4.28.0' in text(w['clean_replay/lean-version.txt'])
    n='RangeTwoClosure.lean';assert f[n]==w['clean_replay/'+n]==w['development/'+n]
    assert text(w['clean_replay/RangeTwoClosure.exit.txt']).strip()=='LEAN_EXIT=0'
    assert text(w['development/compile_RangeTwoClosure_v1.exit.txt']).strip()=='LEAN_EXIT=0'
    log=text(w['clean_replay/RangeTwoClosure.log']);assert not re.search(r'\berror:|sorryAx',log,re.I)
    axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
    allowed={'propext','Classical.choice','Quot.sound'}
    assert len(axioms)==len({n for n,_ in axioms})==6
    assert all(set(re.split(r'\s*,\s*',a))==allowed for _,a in axioms)
    for n in active:
        t=re.sub(r'/-.*?-/', '', text(f[n]), flags=re.S);t=re.sub(r'--[^\n]*','',t)
        assert not re.search(r'(?m)^\s*(?:axiom|constant)\s+|\b(?:sorry|admit)\b',t),n
    for n in ['verify_exact_sdp.py','verify_range2_algebraic.py','previous_range2_certificates.json']:
        assert w['windows_verifier_replay/'+n]==f[n]
        assert len(w['development/'+n])==1
    for n in ['verify_exact_sdp','verify_range2_algebraic']:
        assert text(w['windows_verifier_replay/'+n+'.exit.txt']).strip()=='PYTHON_EXIT=0'
    for n in ['range2_exact_certificates.json','range2_algebraic_intervals.json']:
        assert json.loads(text(w['windows_verifier_replay/'+n]))==json.loads(text(f[n]))
    assert f['verify_range2_closure.py']==f[prefix+'verify_range2_closure.py']==w['development/verify_range2_closure.py']
    assert text(w['development/verify_range2_closure.exit.txt']).strip()=='PYTHON_EXIT=0'
    assert text(f[prefix+'verify_range2_closure.exit.txt']).strip()=='EXIT=0'
    for t in [text(w['development/verify_range2_closure.log']),text(f[prefix+'verify_range2_closure.log'])]:
        assert 'UNIVERSAL_SYMBOLIC_CERTIFICATE_GROUPS 10 PASS' in t and 'NEW_FINITE_SCIENTIFIC_CASES 0' in t
    n='range2_closure_bernstein.json'
    assert json.loads(text(w['development/'+n]))==json.loads(text(f[n]))==json.loads(text(f[prefix+n]))
    acc=json.loads(text(f['ENGINEERING_ACCEPTANCE.json']))
    assert acc['active_counts']=={'lean_modules':45,'verifiers':17,'representative_axioms':87}
    assert acc['formal_completion_count']==1 and acc['release_authorized'] is False
    assert acc['verification_accounting']['updated_convention_total']==43300
    assert acc['verification_accounting']['updated_exact']==35100
    assert acc['verification_accounting']['new_scientific_checks_this_turn']==0
    assert acc['range2_closure']['raw_windows_evidence_sha256']==digest(raw)
    assert acc['manuscript']['tex_sha256']==digest(f['manuscript.tex'])
    assert acc['manuscript']['pdf_sha256']==digest(f['manuscript.pdf'])
    assert f['manuscript.pdf']==f[prefix+'manuscript_compiler.pdf']
    assert text(f[prefix+'tex_exit_codes.txt']).splitlines()==['PASS=1 EXIT=0','PASS=2 EXIT=0','PASS=3 EXIT=0']
    modules=re.search(r'\$modules=@\(([^\n]*)\)',text(f['reproduce.ps1']))[1]
    scripts=re.search(r'foreach\(\$n in @\(([^\n]*)\)\)\{',text(f['reproduce.ps1']))[1]
    assert {n+'.lean' for n in re.findall("'([^']+)'",modules)}==active
    assert {n+'.py' for n in re.findall("'([^']+)'",scripts)}==v
    return dict(integrity='PASS',entries=len(f),manifest_matches=nm,predecessor_payload_matches=len(old),active_lean=45,active_verifiers=17,source_hash_matches=len(hashes),new_clean_stage=1,new_axiom_audits=6,representative_axioms=87,raw_windows_payload_matches=raw_count,new_exact_units=0,new_symbolic_groups_separate=10,total_counted_scientific_units=43300,all45_single_invocation=False,release_authorized=False,tex_sha256=digest(f['manuscript.tex']),pdf_sha256=digest(f['manuscript.pdf']))

if __name__=='__main__':print(json.dumps(check(sys.argv[1]),indent=2))
