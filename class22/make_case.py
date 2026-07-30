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

def smul(a,x):
    return kmul(a,x&15)|(kmul(a,x>>4)<<4)

def unknown_reps():
    seen=set();reps=[]
    for v in range(1,256):
        if v in seen:continue
        orbit=sorted(smul(h,v) for h in H)
        seen.update(orbit);reps.append(orbit[0])
    return [r for r in reps if r not in (1,16)]

def decode(rep):
    xb=rep&255;yb=(rep>>8)&255
    reps=unknown_reps()
    orbit=sorted(smul(h,xb) for h in H)
    xr=orbit[0]
    i=reps.index(xr)
    hs=[h for h in H if smul(h,xb)==xr]
    if len(hs)!=1:raise RuntimeError('nonfree H orbit')
    y=smul(hs[0],yb)
    return i,xr,y,hs[0]

def main():
    if len(sys.argv)!=4:
        raise SystemExit('usage: make_case.py BASE.cnf PACKED_REP OUT.cnf')
    base=pathlib.Path(sys.argv[1]);rep=int(sys.argv[2]);out=pathlib.Path(sys.argv[3])
    i,xr,y,h=decode(rep)
    with base.open('r',encoding='ascii') as src,out.open('w',encoding='ascii') as dst:
        found=False
        for line in src:
            if line.startswith('p cnf '):
                p=line.split();dst.write(f'p cnf {p[2]} {int(p[3])+8}\n');found=True;break
            dst.write(line)
        if not found:raise RuntimeError('missing DIMACS header')
        for line in src:dst.write(line)
        for b in range(8):
            v=1+8*i+b
            dst.write(f'{v if ((y>>b)&1) else -v} 0\n')
    meta={'packed_rep':rep,'input_byte_before_H':rep&255,'output_byte_before_H':rep>>8,
          'normalizing_H_scalar':h,'semantic_orbit_index':i,'input_representative':xr,
          'fixed_output_byte':y,'unit_variables':[1+8*i+b for b in range(8)]}
    print(json.dumps(meta,sort_keys=True))

if __name__=='__main__':main()
