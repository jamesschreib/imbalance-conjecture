#!/usr/bin/env python3
import json,pathlib,sys
H=(1,2,4,8,15)
def kmul(a,b):
 r=0
 while b:
  if b&1:r^=a
  b>>=1;a<<=1
  if a&16:a^=31
 return r&15
def smul(a,x):return kmul(a,x&15)|(kmul(a,x>>4)<<4)
def all_reps():
 seen=set();r=[]
 for v in range(1,256):
  if v in seen:continue
  o=sorted(smul(h,v) for h in H);seen.update(o);r.append(o[0])
 return r
def decode(rep):
 xb,yb=rep&255,rep>>8;full=all_reps();unknown=[r for r in full if r not in (1,16)]
 xr=min(smul(h,xb) for h in H);i,fi=unknown.index(xr),full.index(xr);hs=[h for h in H if smul(h,xb)==xr]
 assert len(hs)==1
 return i,fi,xr,smul(hs[0],yb),hs[0]
def main():
 if len(sys.argv)!=4:raise SystemExit('usage: make_xcase.py BASE.xcnf PACKED_REP OUT.xcnf')
 base,rep,out=pathlib.Path(sys.argv[1]),int(sys.argv[2]),pathlib.Path(sys.argv[3]);i,fi,xr,y,h=decode(rep)
 with base.open() as src,out.open('w') as dst:
  found=False
  for line in src:
   if line.startswith('p cnf '):
    p=line.split();dst.write(f'p cnf {p[2]} {int(p[3])+9}\n');found=True;break
   dst.write(line)
  if not found:raise RuntimeError('missing DIMACS header')
  for line in src:dst.write(line)
  for b in range(8):
   v=1+8*i+b;dst.write(f'{v if y>>b&1 else -v} 0\n')
  dst.write(f'{393+3*fi} 0\n')
 print(json.dumps({'packed_rep':rep,'semantic_orbit_index':i,'full_orbit_index':fi,'input_representative':xr,'fixed_output_byte':y,'color0_selector':393+3*fi,'normalizing_H_scalar':h},sort_keys=True))
if __name__=='__main__':main()
