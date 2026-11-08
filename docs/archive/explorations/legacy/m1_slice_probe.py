#!/usr/bin/env python3
"""Five fixed rational factors on a reflection-symmetric M1 slice.

Run: python explorations/m1_slice_probe.py
Requires mpmath and pmp_return_probe.py. Diagnostic only, not uniform proof.
No random sample, growing word enumeration, numerical ODE, Lean or CI.
"""
import json
import mpmath as mp
from pmp_return_probe import local_phase,continue_phase,VertexArc,first_switch,settings,safe_json


def main():
    mp.mp.dps=60
    for numerator,denominator in ((11,10),(6,5),(5,4),(13,10),(4,3)):
        f=mp.mpf(numerator)/denominator
        z=(-3*f**3+10*f**2-7*f+2)/(3*f-2)
        scale=2/mp.sqrt(2+3*z)
        output=dict(factor=f'{numerator}/{denominator}',raw_initial_third=z)
        try:
            ph,res=local_phase((0,2,1,2,1,0),[f]*6,[scale,2*scale,z*scale])
            output['stationarity']=res
            output['continuation']=continue_phase(ph)
            current=ph;active=0;matches=True
            expected=(0,2,1,2,1)
            for index in range(5):
                if active!=expected[index]:matches=False;break
                arc=VertexArc(current,active,settings().zero)
                r,nxt,status=first_switch(arc,settings())
                if status!='SWITCH' or abs(r-f)>mp.mpf('1e-30'):
                    matches=False;break
                current=arc.at(r);active=nxt
            output['first_five_prescribed_arcs_match']=matches
            if matches and active==0:
                arc=VertexArc(current,0,settings().zero)
                output['outgoing']=dict(a=arc.a,mu_minus_a2=arc.mu-arc.a**2,
                    B0=arc.B0,B1=arc.B1,exit_ratio=arc.exit_ratio,
                    next_event=first_switch(arc,settings())[2])
        except (ValueError,ZeroDivisionError) as exc:
            output['error']=str(exc)
        print(json.dumps(safe_json(output),allow_nan=False))

if __name__=='__main__':main()
