#!/usr/bin/env python3
"""Deterministic necessary-condition diagnostics on five six-piece words.

Run: python explorations/structural_case_probe.py
Requires Python >=3.11 and NumPy >=1.24.
No optimizer, random input, Lean, Lake, typechecking, or CI.

IEEE-754 complex-step derivatives, not exact/interval certificates.
The five constraints are a local chart of (frame,final state) at a fixed
initial state; they are NOT periodic closure constraints for six-windows.
All costs and gaps use physical C/sqrt(12).
"""
import math
import sys
import numpy as np

D = (
    np.array([[-1., 0.], [0., 1.]]),
    np.array([[1., -2.], [0., -1.]]),
    np.array([[1., 0.], [2., -1.]]),
)
R = np.array([[0., 1.], [-1., 1.]])


def transfer(i, z):
    q = np.exp(z)
    return ((q + 1/q)*np.eye(2) + (1/q - q)*D[i])/2


def trajectory(word, logs, initial):
    dtype = complex if np.iscomplexobj(logs) or np.iscomplexobj(initial) else float
    p = np.array(initial, dtype=dtype)
    assert len(word) == len(logs)
    F = np.eye(2, dtype=dtype)
    cost = 0
    margins = [p.copy()]
    for i, z in zip(word, logs):
        q = np.exp(z)
        a, b, c = p[i], p[(i+1)%3], p[(i-1)%3]
        cost += a*((a+b)*(q-1) + (a+c)*(1-1/q) - a*z)/8
        p[(i+1)%3] = (a+b)*q-a
        p[(i-1)%3] = (a+c)/q-a
        F = F @ transfer(i, z)
        margins.append(p.copy())
    return F, p, cost, np.asarray(margins)


def derivative(f, x):
    x = np.asarray(x, dtype=float)
    ans = np.empty((len(f(x)), len(x)))
    for j in range(len(x)):
        z = x.astype(complex)
        z[j] += 1.e-28j
        ans[:, j] = np.imag(f(z))/1.e-28
    return ans


def build_chart(word, initial, reference):
    Finv = np.linalg.inv(reference)
    def chart(logs):
        F, p, cost, _ = trajectory(word, logs, initial)
        U = F @ Finv
        return np.array((U[0,0]-1, U[0,1], U[1,0],
                         p[0], p[1], cost))
    return chart


def compensated_needle(word, logs, initial, F0, dual, cut, vertex):
    assert 0 <= cut <= len(word)
    labels = word[:cut] + (vertex,) + word[cut:]
    new = np.insert(logs, cut, 0.0)
    chart = build_chart(labels, initial, F0)
    z = new.astype(complex)
    z[cut] += 1.e-28j
    d = np.imag(chart(z))/1.e-28
    return float(d[-1] - np.dot(dual, d[:5]))


def local_screen(name, word, factors, initial):
    logs = np.log(np.array(factors, dtype=float))
    F0, pend, cost, m = trajectory(word, logs, initial)
    chart = build_chart(word, initial, F0)
    d = derivative(chart, logs)
    jac, gradient = d[:5], d[5]
    dual, *_ = np.linalg.lstsq(jac.T, gradient, rcond=None)
    stationarity = float(np.linalg.norm(jac.T @ dual - gradient))
    singular = np.linalg.svd(jac, compute_uv=False)
    full = bool(np.min(m)>0 and np.min(logs)>0)
    if stationarity > 1.e-8 or singular[-1] < 1.e-8 or not full:
        print(f"{name:12s} cost={cost*math.sqrt(12):.9f} "
              f"minSV={singular[-1]:.4g} stationarity_res={stationarity:.5g} "
              f"min_margin={np.min(m):.5g} (PMP gaps not interpreted)")
        return stationarity, None
    ends = []
    for cut in (0,len(word)):
        active = word[0] if cut==0 else word[-1]
        gaps = [(i,compensated_needle(word,logs,initial,F0,dual,cut,i))
                for i in range(3) if i!=active]
        ends.append(gaps)
    interior=[]
    for cut in range(1,len(word)):
        missing=({0,1,2}-{word[cut-1],word[cut]}).pop()
        interior.append(compensated_needle(word,logs,initial,F0,dual,cut,missing))
    midpoint=[]
    for arc,i in enumerate(word):
        halflogs=np.insert(logs,arc,logs[arc]/2)
        halflogs[arc+1]=logs[arc]/2
        two=word[:arc]+(i,i)+word[arc+1:]
        for missing in range(3):
            if missing!=i:
                midpoint.append(compensated_needle(two,halflogs,initial,
                                                    F0,dual,arc+1,missing))
    print(f"{name:12s} cost={cost*math.sqrt(12):.9f} "
          f"rank5_minSV={singular[-1]:.4g} "
          f"stationarity_res={stationarity:.5g} min_margin={np.min(m):.5g} "
          f"strict={full}")
    print("  outer gaps", [[(i,round(z,8)) for i,z in gs] for gs in ends])
    print("  interior min",round(min(interior),8),"midpoint min",
          round(min(midpoint),8))
    return stationarity, ends


def main():
    print(f"Python {sys.version.split()[0]}, NumPy {np.__version__}; "
          "normalization C/sqrt(12).")
    templates=[
        ("L1",(0,1,2,0,1,2)),
        ("L2",(0,2,1,0,2,1)),
        ("L3",(0,2,1,2,1,0)),
        ("L4",(0,1,0,2,0,1)),
        ("L5",(0,2,1,0,1,2)),
    ]
    # Determinant one: 1*1+1*(3/2)+(3/2)*1=4.
    for name,word in templates:
        local_screen(name+" generic",word,[1.08]*6,(1.,1.,1.5))
    # Existing exact stationary test inputs from LOCAL_FORWARD_SIX and
    # LOCAL_L3_STRONG_MINIMUM. The numerical screen is not a new proof.
    t=math.sqrt(1975/1684)
    local_screen("L1 known",templates[0][1],
                 [1.1,1.1,1.21,1.21,1.1,1.21],
                 tuple(t*x for x in (1,1,4761/3950)))
    # Standard forward seven-arc period: a locally full-PMP six-window
    # whose complete period exceeds the octagon cost.
    q7=2*math.cos(2*math.pi/7)
    a7=math.sqrt(4*q7/(4-q7)); b7=a7*(2/q7-1)
    local_screen("L1 standard7",templates[0][1],[q7]*6,(a7,b7,a7))
    F7,p7,J7,_=trajectory((0,1,2,0,1,2,0),
                       np.log([q7]*7),(a7,b7,a7))
    A_oct=2*math.sqrt(3)*(8-4*math.sqrt(2)-math.log(2))/(2*math.sqrt(2)-1)
    print(f"  full-period N7 cost={J7*math.sqrt(12):.9f}, "
          f"octagon={A_oct:.9f}, "
          f"frame error={np.max(abs(F7@np.linalg.inv(R)-np.eye(2))):.3g}, "
          f"state error={np.max(abs(p7-np.array([a7,a7,b7]))):.3g}")
    t=math.sqrt(448/803)
    local_screen("L3 known",templates[2][1],[1.25]*6,
                 tuple(t*x for x in (1,2,193/112)))
    print("Necessary-condition diagnostics only; generic inputs are not "
          "stationary, globally closed, or sector certified. "
          "A zero numerical gap is not an exact certificate.")


if __name__ == "__main__":
    main()
