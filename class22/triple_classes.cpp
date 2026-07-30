#include <bits/stdc++.h>
using namespace std;
static uint8_t mm[16][16]; static int H[5]={1,2,4,8,15};
struct V2{uint8_t a,b;}; struct V4{uint8_t x[4];};
int k4(V4 v){return v.x[0]|(v.x[1]<<4)|(v.x[2]<<8)|(v.x[3]<<12);}
V4 sm4(int h,V4 v){for(auto &z:v.x)z=mm[h][z];return v;}
uint8_t sq(uint8_t a){return mm[a][a];} uint8_t fr(uint8_t a,int f){while(f--)a=sq(a);return a;}
V4 frob(V4 v,int f){for(auto &z:v.x)z=fr(z,f);return v;}
uint8_t inv(uint8_t a){for(int b=1;b<16;b++)if(mm[a][b]==1)return b;abort();}
V2 coords(V2 u,V2 v,V2 w){uint8_t det=mm[u.a][v.b]^mm[u.b][v.a];if(!det)abort();uint8_t di=inv(det);return {(uint8_t)mm[di][mm[w.a][v.b]^mm[w.b][v.a]],(uint8_t)mm[di][mm[u.a][w.b]^mm[u.b][w.a]]};}
int canonH4(V4 v){int r=INT_MAX;for(int h:H)r=min(r,k4(sm4(h,v)));return r;}
V4 unpack(int z){return V4{{(uint8_t)(z&15),(uint8_t)(z>>4&15),(uint8_t)(z>>8&15),(uint8_t)(z>>12)}};}
bool valid3(const array<V4,3>&G){set<int>s;for(int i=0;i<3;i++){if(!s.insert(canonH4(G[i])).second)return false;for(int a=0;a<5;a++)for(int b=a+1;b<5;b++){V4 z;auto x=sm4(H[a],G[i]),y=sm4(H[b],G[i]);for(int q=0;q<4;q++)z.x[q]=x.x[q]^y.x[q];s.insert(canonH4(z));}}for(int i=0;i<3;i++)for(int j=i+1;j<3;j++)for(int h:H){V4 z;auto y=sm4(h,G[j]);for(int q=0;q<4;q++)z.x[q]=G[i].x[q]^y.x[q];if(!s.insert(canonH4(z)).second)return false;}return s.size()==24;}
int normalizeThird(const array<V4,3>&A,int i,int j,int k,int h1,int h2,int h3,int f,bool sw){
 V4 g1=frob(A[i],f),g2=frob(A[j],f),g3=frob(A[k],f);if(sw){for(V4*p:{&g1,&g2,&g3}){swap(p->x[0],p->x[2]);swap(p->x[1],p->x[3]);}}g1=sm4(h1,g1);g2=sm4(h2,g2);g3=sm4(h3,g3);
 V2 xx=coords({g1.x[0],g1.x[1]},{g2.x[0],g2.x[1]},{g3.x[0],g3.x[1]});V2 yy=coords({g1.x[2],g1.x[3]},{g2.x[2],g2.x[3]},{g3.x[2],g3.x[3]});return canonH4(V4{{xx.a,xx.b,yy.a,yy.b}});
}
int main(){auto mul=[](int a,int b){int r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&16)a^=31;}return r&15;};for(int a=0;a<16;a++)for(int b=0;b<16;b++)mm[a][b]=mul(a,b);
 V4 e1{{1,0,1,0}},e2{{0,1,0,1}};vector<int>states;map<int,int>idx;
 for(int a=1;a<16;a++)for(int b=1;b<16;b++)for(int c=1;c<16;c++)for(int d=1;d<16;d++){int q=canonH4(V4{{(uint8_t)a,(uint8_t)b,(uint8_t)c,(uint8_t)d}});if(!idx.count(q)){idx[q]=states.size();states.push_back(q);}}
 sort(states.begin(),states.end());idx.clear();for(int i=0;i<(int)states.size();i++)idx[states[i]]=i;vector<char>good(states.size());int ng=0;for(int s=0;s<(int)states.size();s++){array<V4,3>A{e1,e2,unpack(states[s])};good[s]=valid3(A);ng+=good[s];}
 vector<int>par(states.size());iota(par.begin(),par.end(),0);function<int(int)>ff=[&](int x){return par[x]==x?x:par[x]=ff(par[x]);};auto un=[&](int a,int b){a=ff(a);b=ff(b);if(a!=b)par[b]=a;};
 for(int s=0;s<(int)states.size();s++)if(good[s]){array<V4,3>A{e1,e2,unpack(states[s])};for(int f=0;f<4;f++)for(int sw=0;sw<2;sw++)for(int i=0;i<3;i++)for(int j=0;j<3;j++)if(j!=i){int k=3-i-j;if(k<0||k>2||k==i||k==j)continue;for(int h1:H)for(int h2:H)for(int h3:H){int q=normalizeThird(A,i,j,k,h1,h2,h3,f,sw);auto it=idx.find(q);if(it==idx.end()||!good[it->second])abort();un(s,it->second);}}}
 map<int,vector<int>>cls;for(int s=0;s<(int)states.size();s++)if(good[s])cls[ff(s)].push_back(states[s]);cout<<"GOOD_STATES "<<ng<<" CLASSES "<<cls.size()<<"\n";int no=0;for(auto &[r,v]:cls){sort(v.begin(),v.end());cout<<no++<<' '<<v.size()<<' '<<v[0]<<"\n";}if(cls.size()!=62)return 2;
}
