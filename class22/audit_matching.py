#!/usr/bin/env python3
from collections import defaultdict
import random
H=(1,2,4,8,15);NONH=tuple(a for a in range(1,16) if a not in H)
def kmul(a,b):
 r=0
 while b:
  if b&1:r^=a
  b>>=1;a<<=1
  if a&16:a^=31
 return r&15
def smul(a,x):return kmul(a,x&15)|(kmul(a,x>>4)<<4)
def repsH():
 seen=set();r=[]
 for x in range(1,256):
  if x in seen:continue
  o={smul(h,x) for h in H};seen|=o;r.append(min(o))
 return r
def line(x):return min(smul(a,x) for a in range(1,16))
R=repsH();G=defaultdict(list)
for i,r in enumerate(R):G[line(r)].append(i)
assert len(R)==51 and len(G)==17 and {len(v) for v in G.values()}=={3}
lines=sorted(G);li={q:i for i,q in enumerate(lines)};fixed=[li[line(1)],li[line(16)]]
random.seed(2205)
for _ in range(100):
 p=[None]*17;rest=[i for i in range(17) if i not in fixed];outrest=rest[:];random.shuffle(outrest)
 for i in fixed:p[i]=i
 for i,j in zip(rest,outrest):p[i]=j
 selected=[];perm=[None]*51;unused=set(range(51))
 for i,q in enumerate(lines):
  ins,outs=G[q],G[lines[p[i]]]
  if q==line(1):a=b=R.index(1)
  elif q==line(16):a=b=R.index(16)
  else:a=random.choice(ins);b=random.choice(outs)
  selected.append(a);perm[a]=b;unused.remove(b)
 remi=[i for i,x in enumerate(perm) if x is None];remo=list(unused);random.shuffle(remo)
 for a,b in zip(remi,remo):perm[a]=b
 assert sorted(perm)==list(range(51))
 assert all(sum(i in selected for i in G[q])==1 for q in lines)
 assert len({line(R[perm[i]]) for i in selected})==17
 for x in range(17):
  for y in range(x+1,17):
   u,v=R[perm[selected[x]]],R[perm[selected[y]]]
   assert all(u!=smul(a,v) for a in NONH)
print('MATCHING REDUCTION AUDIT PASSED: 100 constructed witnesses')
