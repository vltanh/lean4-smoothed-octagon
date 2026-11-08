#!/usr/bin/env python3
"""Exact algebra and published receipt checks for the reverse-boundary theorem.

Run from the repository root:
    python explorations/mixed_nonshort_reverse_boundary_certificate.py

Requires Python 3 and SymPy. Twenty exact identities check the b-comparison
and geometric contractors. The default also verifies the published source
and log hashes and both completed execution records in
explorations/mixed_nonshort_reverse_boundary_result.json.

Use --algebra-only for the symbolic checks without a receipt. Use
--repository DIR when this script is outside the reviewed checkout.
--artifact-directory DIR additionally verifies retained original-run files,
including the executable, against sources_and_artifacts in the receipt.
No binary is required or asserted to be checked by the default invocation.

The hand signs, integrating-factor argument and chart exhaustion are in
MIXED_NONSHORT_REVERSE_BOUNDARY_AUDIT.md. No numerical sampling, Lean,
Lake, typechecking, CI, or full interval cover is run by this checker.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sympy as s


def run_algebra_checks():
    checks=[]
    def eq(name,left,right=0):
        delta=s.factor(left-right)
        if delta!=0:
            raise AssertionError((name,delta))
        checks.append(name)
        print('PASS',name)

    a,b,c,d,r=s.symbols('a b c d r',positive=True)
    u,v=s.symbols('u v',real=True)
    K=a*a+4; S=a+b; T=a+c; Q=d*d+4; W=c+d; Z=d+r; Y=W*W-T*T
    U=1-a/S+(a/S)**2
    Ca=b+a+c-a*a*(1/S+1/T)+a**3/K+a*s.log(K/(S*T))
    h=K*(S*u+T*v-Ca)/(16*a)
    hd=h+v*Y/8
    w=(u*K*K+16*h*Y+v*Y*Y)/(Q*Q)
    Cd=c+d+r-d*d*(1/W+1/Z)+d**3/Q-d*s.log(W*Z/Q)
    Rd=Cd-W*v-Z*w+16*d*hd/Q
    Ru=s.diff(Rd,u)
    Rb=s.diff(Rd,b)
    j=u-U
    A=-K*(d*Q-Z*Y)/(a*Q*Q*Ru)
    eq('central stationarity derivative',s.diff(Ca,b),U)
    eq('partial h derivative',s.diff(h,b),K*j/(16*a))
    eq('root coefficient',Ru,K*(d*S*Q-Z*(a*K+S*Y))/(a*Q*Q))
    eq('partial root derivative',Rb,K*(d*Q-Z*Y)*j/(a*Q*Q))
    eq('negative-coefficient decomposition',d*S*Q-Z*(a*K+S*Y),Q/W*(a*(S*T-K)+S*c*(a-d))-(Z-Q/W)*(a*K+S*Y))
    eq('inhomogeneous upper-gap ODE',-Rb/Ru-s.diff(U,b),A*j-a*(b-a)/S**3)
    eq('transported outgoing norm derivative',s.diff(w,b)-s.diff(w,u)*Rb/Ru,-d*K**3*j/(a*Q**3*Ru))
    Hs=W*W-c*T
    Ds=Z*Hs-d*Q
    bstar=K/T-a
    eq('boundary root coefficient',Ru.subs(b,bstar),-K*K*Ds/(a*Q*Q*T))
    eq('positive boundary denominator identity',Hs-d*W,c*(d-a))

    m,z=s.symbols('m z',positive=True)
    dz=a+T*z
    f=(4-c*c*z-m*c*(1+z))/((c+m)*(1+z))
    eq('inactive-margin a cap',4-c*dz-m*(c+dz),(c+m)*(1+z)*(f-a))
    eq('inactive a cap c derivative',s.diff(f,c),-(4+m*m*(1+z)+c*c*z+2*c*m*z)/((c+m)**2*(1+z)))
    eq('inactive a cap delta derivative',s.diff(f,z),-(4+c*c)/((c+m)*(1+z)**2))
    f1=(4-a*c-m*T)/(T*(c+m))
    eq('inactive delta1 cap a derivative',s.diff(f1,a),-(4+c*c)/(T*T*(c+m)))
    f2=(c-m)/(a+T*z+m)
    eq('inactive delta2 cap c derivative',s.diff(f2,c),(a+m)*(1+z)/(a+T*z+m)**2)
    eq('log-concavity positive factor',c*c-a*dz,T*(c-a*(1+z)))
    z2=s.symbols('z2',nonnegative=True)
    Zz=Q*(1+z2)/W
    rz=Zz-d
    eq('r>=a positive factor',W*(rz-a),4-a*c-T*d+Q*z2)
    eq('r upper compact margin positive factor',4-d*rz-m*(d+rz),Q/W*(c-m-(d+m)*z2))
    eq('delta2 floor from r>=a',(T*d+a*c-4)/Q,(W*(d+a)-Q)/Q)
    eq('delta2 cap from r<=8',W*(d+8)/Q-1,(W*(8+d)-Q)/Q)
    L=s.symbols('L',real=True)
    zz=(d-a)/(a+r)
    code_ceiling=1+r*r/((a+r)*Z)-r/(a+r)*(L/zz)
    sec_ceiling=1+r*r/((a+r)*Z)-r/(d-a)*L
    eq('reverse upper secant formula',code_ceiling,sec_ceiling)

    print(f'All {len(checks)} exact reverse-boundary identities passed.')


RECEIPT = "explorations/mixed_nonshort_reverse_boundary_result.json"
ORIGINAL_LOG = "explorations/results/mixed_nonshort_reverse_boundary_original.log"
REPLAY_LOG = "explorations/results/mixed_nonshort_reverse_boundary_replay.log"
PUBLISHED_SOURCES = {
    "explorations/mixed_nonshort_reverse_boundary_interval_certificate.cpp":
        "984f729590c1933ad7677b0d4a7392210f36f6a49f63f607b1576a4c6b69557c",
    "explorations/certified_mpfr_interval.hpp":
        "1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76",
    "explorations/certified_lp_proposal.hpp":
        "6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454",
    "explorations/mixed_nonshort_coefficients.hpp":
        "5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d",
}
EXPECTED_ROOTS = {
    "a": ["2/15", "17/20"],
    "c": ["2/15", "2"],
    "epsilon": ["1/32", "15"],
    "l0": ["0", "0"],
    "other_weight": ["0", "1"],
}
EXPECTED_REASONS = {
    "1": 1409, "17": 35210, "19": 4405, "20": 3948,
    "22": 11, "26": 993, "27": 722, "28": 5, "60": 6365,
}
SUCCESS = ("PASS: complete two-chart reverse boundary domain excluded; "
           "interface audit still required.")


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def repo_path(repository, relative):
    require(isinstance(relative, str), "non-string published artifact path")
    path = (repository / relative).resolve()
    require(not Path(relative).is_absolute() and repository in path.parents,
            "published artifact is not repository-relative: " + relative)
    return path


def check_log(path):
    text = path.read_text()
    finals = re.findall(
        r"^FINAL branch (\d+) nodes (\d+) stack (\d+) depth (\d+) "
        r"unknown (\d+) seconds ([0-9.]+)$", text, re.M)
    require(len(finals) == 1, "expected one final record: " + str(path))
    values = tuple(map(int, finals[0][:5]))
    require(values == (1, 106134, 0, 26, 0),
            "unexpected final record: " + str((path, values)))
    rows = re.findall(r"^reason (\d+) leaves (\d+)$", text, re.M)
    reasons = {reason: int(count) for reason, count in rows}
    require(len(reasons) == len(rows), "duplicate leaf reason: " + str(path))
    require(reasons == EXPECTED_REASONS, "leaf reasons changed: " + str(path))
    require(sum(reasons.values()) == 53068, "incorrect leaf sum")
    require(values[1] == 2 * sum(reasons.values()) - 2,
            "two-root forest identity failed")
    require(text.rstrip().endswith(SUCCESS),
            "not an original-root completion record: " + str(path))
    require("INCOMPLETE:" not in text, "incomplete run present in completed log")
    print("PASS complete original-root log", path.name)
    return reasons


def check_published_record(repository, artifact_directory):
    result_path = repository / RECEIPT
    result = json.loads(result_path.read_text())
    for key, expected in {
        "root_count": 2, "charts": [1, 2], "roots": EXPECTED_ROOTS,
        "branch": 1, "nodes": 106134, "leaves": 53068,
        "pending": 0, "unresolved": 0, "maximum_depth": 26,
        "leaf_reasons": EXPECTED_REASONS,
    }.items():
        require(result.get(key) == expected, "receipt mismatch: " + key)
    require(result["nodes"] == 2 * result["leaves"] - result["root_count"],
            "receipt forest identity failed")
    published = result.get("published_artifacts")
    require(isinstance(published, dict), "missing published_artifacts mapping")
    for relative, expected in PUBLISHED_SOURCES.items():
        require(published.get(relative) == expected,
                "published source identifier changed: " + relative)
    for relative in (ORIGINAL_LOG, REPLAY_LOG):
        require(relative in published, "missing published log: " + relative)
    for relative, expected in published.items():
        require(isinstance(expected, str) and
                re.fullmatch(r"[0-9a-f]{64}", expected) is not None,
                "invalid SHA256 in published_artifacts: " + relative)
        require(sha256(repo_path(repository, relative)) == expected,
                "published artifact hash mismatch: " + relative)
        print("PASS published artifact", relative)
    check_log(repository / ORIGINAL_LOG)
    check_log(repository / REPLAY_LOG)
    replay = result.get("independent_replay")
    require(isinstance(replay, dict) and replay, "missing independent_replay metadata")
    # Both logs above are checked directly. If the replay metadata repeats
    # these facts, it must agree; ancillary command/timing keys are unrestricted.
    for key in ("branch", "nodes", "leaves", "pending", "unresolved",
                "maximum_depth", "leaf_reasons"):
        if key in replay:
            require(replay[key] == result[key], "replay metadata mismatch: " + key)
    for key in ("exit_code", "exit_status", "returncode"):
        if key in replay:
            require(replay[key] == 0, "nonzero replay exit status")
    original = result.get("sources_and_artifacts")
    require(isinstance(original, dict), "missing original artifact identifiers")
    require(original.get("reverse_boundary_cover.log") == published[ORIGINAL_LOG],
            "published original log differs from original receipt")
    require(original.get("mixed_nonshort_completion_unresolved_1.txt") ==
            hashlib.sha256(b"").hexdigest(), "original unresolved artifact was not empty")
    aliases = {
        "reverse_boundary.cpp":
            "explorations/mixed_nonshort_reverse_boundary_interval_certificate.cpp",
        "certified_mpfr_interval.hpp": "explorations/certified_mpfr_interval.hpp",
        "certified_lp_proposal.hpp": "explorations/certified_lp_proposal.hpp",
        "mixed_nonshort_coefficients.hpp": "explorations/mixed_nonshort_coefficients.hpp",
        "reverse_boundary_cover.log": ORIGINAL_LOG,
    }
    for name, relative in aliases.items():
        require(original.get(name) == published[relative],
                "original/published source identifier mismatch: " + name)
    if artifact_directory is not None:
        for name, expected in original.items():
            path = artifact_directory / name
            if not path.is_file() and name in aliases:
                path = repository / aliases[name]
            require(path.is_file(), "missing retained original artifact: " + name)
            require(sha256(path) == expected, "original artifact hash mismatch: " + name)
            print("PASS retained original artifact", name)
    print("PASS receipt and both two-root logs: 106134=2*53068-2; pending=unknown=0")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument("--artifact-directory", type=Path,
                        help="also verify retained original-run files, including its executable")
    parser.add_argument("--algebra-only", action="store_true",
                        help="run only the twenty symbolic identities")
    args = parser.parse_args()
    run_algebra_checks()
    if not args.algebra_only:
        check_published_record(args.repository.resolve(), args.artifact_directory)


if __name__ == "__main__":
    main()
