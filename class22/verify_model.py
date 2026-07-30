#!/usr/bin/env python3
import json
import pathlib
import sys

H=(1,2,4,8,15)

def kmul(a,b):
    r=0
    while b:
        if b&1:r^=a
        b>>=1;a<<=1
        if a&16:a^=31
    return r&15

def smul(a,x):return kmul(a,x&15)|(kmul(a,x>>4)<<4)

def unknown_reps():
    seen=set();reps=[]
    for v in range(1,256):
        if v in seen:continue
        o=sorted(smul(h,v) for h in H);seen.update(o);reps.append(o[0])
    return [r for r in reps if r not in (1,16)]

def read_model(path):
    values={}
    for line in pathlib.Path(path).read_text(errors='replace').splitlines():
        if not line.startswith('v '):continue
        for tok in line[2:].split():
            lit=int(tok)
            if lit:values[abs(lit)]=lit>0
    missing=[v for v in range(1,393) if v not in values]
    if missing:raise RuntimeError(f'missing semantic model variables, first={missing[:10]}')
    return values

def main():
    if len(sys.argv)!=3:raise SystemExit('usage: verify_model.py SOLVER.log OUT.json')
    val=read_model(sys.argv[1]);ys=[]
    for i in range(49):
        y=sum((1<<b) for b in range(8) if val[1+8*i+b]);ys.append(y)
    F=[None]*256;F[0]=0
    for h in H:F[smul(h,1)]=smul(h,1);F[smul(h,16)]=smul(h,16)
    for r,y in zip(unknown_reps(),ys):
        for h in H:F[smul(h,r)]=smul(h,y)
    if any(x is None for x in F):raise RuntimeError('incomplete table')
    if len(set(F))!=256:raise RuntimeError('not a permutation')
    for x in range(256):
        if F[smul(2,x)]!=smul(2,F[x]):raise RuntimeError(f'commutation failure at {x}')
    worst=0
    for a in range(1,256):
        cnt={}
        for x in range(256):
            b=F[x]^F[x^a];cnt[b]=cnt.get(b,0)+1
        m=max(cnt.values());worst=max(worst,m)
        if m>2:raise RuntimeError(f'not APN: direction {a}, multiplicity {m}')
    result={'verified':True,'permutation':True,'commutes':True,'differential_uniformity':worst,'table':F,'orbit_outputs':ys}
    pathlib.Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n')
    print('VERIFIED SAT APN PERMUTATION')

if __name__=='__main__':main()
