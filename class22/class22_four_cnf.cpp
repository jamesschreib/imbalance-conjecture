#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;

static constexpr std::array<uint8_t,5> H{{1,2,4,8,15}};
static uint8_t kmul[16][16], tr[16][256], lin[16][8];
static void init_field(){
 auto mul=[](int a,int b){int r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&16)a^=31;}return r&15;};
 for(int a=0;a<16;a++)for(int b=0;b<16;b++)kmul[a][b]=mul(a,b);
 for(int a=0;a<16;a++)for(int v=0;v<256;v++)tr[a][v]=kmul[a][v&15]|(kmul[a][v>>4]<<4);
 for(int a=1;a<16;a++)for(int ob=0;ob<8;ob++){uint8_t m=0;for(int ib=0;ib<8;ib++)if((tr[a][1u<<ib]>>ob)&1)m|=1u<<ib;lin[a][ob]=m;}
}
struct GDesc{uint8_t base=0,zc=0,wc=0,ar=0;std::array<uint8_t,4>idx{},sc{};};
struct Desc{uint8_t c=0,ar=0;std::array<uint8_t,4>idx{},sc{};};
class CNF {
 std::ofstream out; int next; uint64_t ncl=0;std::unordered_map<uint64_t,int>cache;
public:
 CNF(const std::string&p):out(p,std::ios::binary),next(377){if(!out)throw std::runtime_error("body open");cache.reserve(4000000);}
 int vars()const{return next-1;}uint64_t clauses()const{return ncl;}size_t gates()const{return cache.size();}
 void clause(const std::vector<int>&v){if(v.empty())throw std::runtime_error("empty clause");for(int x:v)out<<x<<' ';out<<"0\n";ncl++;}
 void c3(int a,int b,int c){out<<a<<' '<<b<<' '<<c<<" 0\n";ncl++;}
 int x2(int a,int b){if(!a)return b;if(!b)return a;if(a==b)return 0;if(a>b)std::swap(a,b);uint64_t k=(uint64_t)(uint32_t)a<<32|(uint32_t)b;auto it=cache.find(k);if(it!=cache.end())return it->second;int z=next++;cache[k]=z;c3(-a,-b,-z);c3(a,b,-z);c3(a,-b,z);c3(-a,b,z);return z;}
 int xm(std::vector<int>v){v.erase(remove(v.begin(),v.end(),0),v.end());sort(v.begin(),v.end());vector<int>r;for(size_t i=0;i<v.size();){size_t j=i+1;while(j<v.size()&&v[j]==v[i])j++;if((j-i)&1)r.push_back(v[i]);i=j;}v.swap(r);while(v.size()>1){vector<int>n;for(size_t i=0;i+1<v.size();i+=2)n.push_back(x2(v[i],v[i+1]));if(v.size()&1)n.push_back(v.back());sort(n.begin(),n.end());v.swap(n);}return v.empty()?0:v[0];}
 void close(){out.close();}
};
static int primary(int i,int b){return 1+8*i+b;}
int main(int argc,char**argv)try{
 if(argc<4){std::cerr<<"usage: Z W simple output.cnf\n";return 2;}init_field();int zfix=atoi(argv[1]),wfix=atoi(argv[2]);bool simple=atoi(argv[3]);std::string output=argc>4?argv[4]:"class22.cnf",body=output+".body";
 int oid[256];std::fill(std::begin(oid),std::end(oid),-1);std::vector<int>reps;for(int v=1;v<256;v++)if(oid[v]<0){std::array<int,5>o{};for(int k=0;k<5;k++)o[k]=tr[H[k]][v];sort(o.begin(),o.end());int id=reps.size();reps.push_back(o[0]);for(int x:o)oid[x]=id;}
 std::map<int,int>fp{{1,0},{3,1},{5,2},{16,3}};std::vector<int>unk;for(int r:reps)if(!fp.count(r))unk.push_back(r);if(unk.size()!=47)throw std::runtime_error("orbit count");
 uint8_t kind[256]{},idx[256]{},scalar[256]{};kind[0]=1;idx[0]=4;for(auto[r,j]:fp)for(uint8_t h:H){int p=tr[h][r];kind[p]=1;idx[p]=j;scalar[p]=h;}for(int i=0;i<47;i++)for(uint8_t h:H){int p=tr[h][unk[i]];kind[p]=2;idx[p]=i;scalar[p]=h;}
 std::vector<GDesc>gd;gd.reserve(138176);uint64_t all=0;for(int x=0;x<256;x++)for(int y=x+1;y<256;y++)for(int z=y+1;z<256;z++){int w=x^y^z;if(w<=z)continue;all++;std::array<int,4>f{x,y,z,w},best=f;for(uint8_t h:H){std::array<int,4>q;for(int k=0;k<4;k++)q[k]=tr[h][f[k]];sort(q.begin(),q.end());best=min(best,q);}if(f!=best)continue;GDesc d;uint8_t co[47]{};for(int p:f){uint8_t h=scalar[p];if(kind[p]==1){if(idx[p]==0)d.base^=tr[h][1];else if(idx[p]==1)d.base^=tr[h][16];else if(idx[p]==2)d.zc^=h;else if(idx[p]==3)d.wc^=h;}else co[idx[p]]^=h;}for(int i=0;i<47;i++)if(co[i]){d.idx[d.ar]=i;d.sc[d.ar]=co[i];d.ar++;}gd.push_back(d);}if(all!=690880||gd.size()!=138176)throw std::runtime_error("flat count");
 std::vector<Desc>ds;int taut0=0,contr=0;for(auto&g:gd){Desc d;d.c=g.base^tr[g.zc][zfix]^tr[g.wc][wfix];d.ar=g.ar;for(int q=0;q<g.ar;q++){d.idx[q]=g.idx[q];d.sc[q]=g.sc[q];}if(!d.ar){if(d.c)taut0++;else contr++;}else ds.push_back(d);}if(contr)throw std::runtime_error("fixed contradiction");
 CNF cnf(body);std::vector<int>L(47*16*8);auto lbit=[&](int i,int a,int b){int&c=L[(i*16+a)*8+b];if(c)return c;std::vector<int>t;for(int q=0;q<8;q++)if((lin[a][b]>>q)&1)t.push_back(primary(i,q));c=cnf.xm(t);if(!c)throw std::runtime_error("zero transform");return c;};
 uint64_t domain=0,pair=0,flat=0,taut=taut0,simpleN=0;bool forb[256]{};forb[0]=1;for(int q:{1,16,zfix,wfix})for(uint8_t h:H)forb[tr[h][q]]=1;int fc=0;for(bool b:forb)fc+=b;if(fc!=21)throw std::runtime_error("fixed output overlap");
 for(int i=0;i<47;i++)for(int v=0;v<256;v++)if(forb[v]){std::vector<int>cl;for(int b=0;b<8;b++)cl.push_back((v>>b)&1?-primary(i,b):primary(i,b));cnf.clause(cl);domain++;}
 auto neScaled=[&](int i,int j,int a){std::vector<int>cl;for(int b=0;b<8;b++)cl.push_back(cnf.x2(primary(i,b),lbit(j,a,b)));cnf.clause(cl);};
 for(int i=0;i<47;i++)for(int j=i+1;j<47;j++)for(uint8_t h:H){neScaled(i,j,h);pair++;}
 if(simple){auto proj=[&](int v){int r=999;for(int a=1;a<16;a++)r=min(r,(int)tr[a][v]);return r;};for(int i=0;i<47;i++)for(int j=i+1;j<47;j++)if(proj(unk[i])==proj(unk[j]))for(int a=1;a<16;a++)if(find(H.begin(),H.end(),a)==H.end()){neScaled(i,j,a);simpleN++;}int fl=proj(16);for(int i=0;i<47;i++)if(proj(unk[i])==fl)for(int a=1;a<16;a++){int v=tr[a][wfix];std::vector<int>cl;for(int b=0;b<8;b++)cl.push_back((v>>b)&1?-primary(i,b):primary(i,b));cnf.clause(cl);simpleN++;}}
 for(auto&d:ds){std::vector<int>cl;bool tt=0;for(int b=0;b<8;b++){std::vector<int>t;for(int q=0;q<d.ar;q++)t.push_back(lbit(d.idx[q],d.sc[q],b));int p=cnf.xm(t);bool cb=(d.c>>b)&1;if(!p){if(cb){tt=1;break;}}else cl.push_back(cb?-p:p);}if(tt)taut++;else{cnf.clause(cl);flat++;}}
 cnf.close();std::ofstream fo(output,std::ios::binary);fo<<"c Class22 four-orbit canonical case z="<<zfix<<" w="<<wfix<<" simple="<<simple<<"\n";fo<<"c primary variables 1..376 encode 47 output bytes\n";fo<<"c domain "<<domain<<" pair "<<pair<<" simple "<<simpleN<<" APN "<<flat<<" taut "<<taut<<"\n";fo<<"p cnf "<<cnf.vars()<<' '<<cnf.clauses()<<"\n";std::ifstream bi(body,std::ios::binary);fo<<bi.rdbuf();fo.close();bi.close();remove(body.c_str());std::cerr<<"vars="<<cnf.vars()<<" gates="<<cnf.gates()<<" clauses="<<cnf.clauses()<<" domain="<<domain<<" pair="<<pair<<" simple="<<simpleN<<" flat="<<flat<<" taut="<<taut<<"\n";return 0;
}catch(const std::exception&e){std::cerr<<"fatal: "<<e.what()<<"\n";return 2;}
