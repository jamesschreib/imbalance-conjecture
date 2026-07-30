#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

static int kmul(int a,int b){int r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&16)a^=31;}return r&15;}
static int smul_byte(int a,int x){return kmul(a,x&15)|(kmul(a,x>>4)<<4);}
static constexpr std::array<int,5> H{{1,2,4,8,15}};
static constexpr std::array<int,10> NONH{{3,5,6,7,9,10,11,12,13,14}};
struct Desc { uint8_t constant=0, arity=0; std::array<uint8_t,4> index{}, scalar{}; };
static std::vector<int> all_reps(){std::array<int,256> seen{};std::vector<int>r;for(int v=1;v<256;v++)if(!seen[v]){std::vector<int>o;for(int h:H){int w=smul_byte(h,v);o.push_back(w);seen[w]=1;}std::sort(o.begin(),o.end());r.push_back(o[0]);}return r;}
static std::vector<int> unknown_reps(){auto r=all_reps();std::vector<int>u;for(int x:r)if(x!=1&&x!=16)u.push_back(x);return u;}
static int canonK(int v){int r=999;for(int a=1;a<16;a++)r=std::min(r,smul_byte(a,v));return r;}
static std::vector<Desc> generate_desc(){
 auto unknown=unknown_reps();if(unknown.size()!=49)throw std::runtime_error("bad unknown count");std::array<int,256>kind{},idx{},coeff{},fixed{};kind.fill(-1);kind[0]=0;
 for(int h:H){int p=smul_byte(h,1);kind[p]=0;fixed[p]=p;p=smul_byte(h,16);kind[p]=0;fixed[p]=p;}
 for(int i=0;i<49;i++)for(int h:H){int p=smul_byte(h,unknown[i]);if(kind[p]!=-1)throw std::runtime_error("duplicate point");kind[p]=1;idx[p]=i;coeff[p]=h;}
 for(int p=0;p<256;p++)if(kind[p]<0)throw std::runtime_error("unmapped point");std::vector<Desc>out;out.reserve(138176);
 for(int x=0;x<256;x++)for(int y=x+1;y<256;y++)for(int z=y+1;z<256;z++){int w=x^y^z;if(w<=z)continue;std::array<int,4>f{{x,y,z,w}},best=f;for(int h:H){std::array<int,4>g;for(int q=0;q<4;q++)g[q]=smul_byte(h,f[q]);std::sort(g.begin(),g.end());if(g<best)best=g;}if(f!=best)continue;Desc d;int c=0;std::array<int,49>cs{};for(int p:f){if(kind[p]==0)c^=fixed[p];else cs[idx[p]]^=coeff[p];}d.constant=c;for(int i=0;i<49;i++)if(cs[i]){if(d.arity>=4)throw std::runtime_error("arity overflow");d.index[d.arity]=i;d.scalar[d.arity]=cs[i];d.arity++;}if(!d.arity)throw std::runtime_error("zero arity");out.push_back(d);}
 if(out.size()!=138176)throw std::runtime_error("bad flat orbit count");return out;
}
class CNFWriter{std::ofstream body;int next;uint64_t clauses=0;std::unordered_map<uint64_t,int>cache;public:CNFWriter(const std::string&p,int first):body(p,std::ios::binary),next(first){if(!body)throw std::runtime_error("body open");cache.reserve(5000000);}int next_var()const{return next;}uint64_t count()const{return clauses;}size_t gates()const{return cache.size();}void clause(const std::vector<int>&l){if(l.empty())throw std::runtime_error("empty clause");for(int x:l)body<<x<<' ';body<<"0\n";clauses++;}void c3(int a,int b,int c){body<<a<<' '<<b<<' '<<c<<" 0\n";clauses++;}int xor2(int a,int b){if(!a)return b;if(!b)return a;if(a==b)return 0;if(a>b)std::swap(a,b);uint64_t k=(uint64_t)(uint32_t)a<<32|(uint32_t)b;auto it=cache.find(k);if(it!=cache.end())return it->second;int z=next++;cache[k]=z;c3(-a,-b,-z);c3(a,b,-z);c3(a,-b,z);c3(-a,b,z);return z;}int xormany(std::vector<int>t){t.erase(std::remove(t.begin(),t.end(),0),t.end());std::sort(t.begin(),t.end());std::vector<int>r;for(size_t i=0;i<t.size();){size_t j=i+1;while(j<t.size()&&t[j]==t[i])j++;if((j-i)&1)r.push_back(t[i]);i=j;}t.swap(r);while(t.size()>1){std::vector<int>n;for(size_t i=0;i<t.size();i+=2)n.push_back(i+1<t.size()?xor2(t[i],t[i+1]):t[i]);std::sort(n.begin(),n.end());t.swap(n);}return t.empty()?0:t[0];}void close(){body.close();}};
static int primary(int i,int b){return 1+8*i+b;}static int selector(int full){return 393+full;}
int main(int argc,char**argv)try{
 std::string output=argc>1?argv[1]:"class22_matching.cnf",temp=output+".body";auto desc=generate_desc(),full=all_reps(),unknown=unknown_reps();if(full.size()!=51)throw std::runtime_error("bad full reps");std::array<int,256>ui{},fi{};ui.fill(-1);fi.fill(-1);for(int i=0;i<49;i++)ui[unknown[i]]=i;for(int i=0;i<51;i++)fi[full[i]]=i;
 std::array<std::array<uint8_t,8>,16>rows{};for(int a=1;a<16;a++)for(int b=0;b<8;b++){uint8_t m=0;for(int s=0;s<8;s++)if((smul_byte(a,1<<s)>>b)&1)m|=1<<s;rows[a][b]=m;}
 CNFWriter cnf(temp,444);std::vector<int>L(49*16*8);auto lbit=[&](int i,int a,int b){int&v=L[(i*16+a)*8+b];if(v)return v;std::vector<int>t;for(int s=0;s<8;s++)if((rows[a][b]>>s)&1)t.push_back(primary(i,s));v=cnf.xormany(t);if(!v)throw std::runtime_error("zero transform");return v;};auto fixed_byte=[&](int i){return full[i]==1?1:full[i]==16?16:-1;};auto uindex=[&](int i){int u=ui[full[i]];if(u<0)throw std::runtime_error("not unknown");return u;};
 uint64_t nd=0,np=0,nf=0,nmi=0,nmo=0;std::vector<int>forbidden{0};for(int h:H){forbidden.push_back(smul_byte(h,1));forbidden.push_back(smul_byte(h,16));}std::sort(forbidden.begin(),forbidden.end());forbidden.erase(std::unique(forbidden.begin(),forbidden.end()),forbidden.end());
 for(int i=0;i<49;i++)for(int x:forbidden){std::vector<int>cl;for(int b=0;b<8;b++)cl.push_back((x>>b&1)?-primary(i,b):primary(i,b));cnf.clause(cl);nd++;}
 for(int i=0;i<49;i++)for(int j=i+1;j<49;j++)for(int h:H){std::vector<int>cl;for(int b=0;b<8;b++)cl.push_back(cnf.xor2(primary(i,b),lbit(j,h,b)));cnf.clause(cl);np++;}
 std::map<int,std::vector<int>>groups;for(int i=0;i<51;i++)groups[canonK(full[i])].push_back(i);if(groups.size()!=17)throw std::runtime_error("bad projective count");for(auto&kv:groups){auto&g=kv.second;if(g.size()!=3)throw std::runtime_error("bad projective group");cnf.clause({selector(g[0]),selector(g[1]),selector(g[2])});nmi++;for(int a=0;a<3;a++)for(int b=a+1;b<3;b++){cnf.clause({-selector(g[a]),-selector(g[b])});nmi++;}}int fe1=fi[1],fe2=fi[16];cnf.clause({selector(fe1)});cnf.clause({selector(fe2)});nmi+=2;
 auto cne=[&](int li,int ri,int a){int lf=fixed_byte(li),rf=fixed_byte(ri);std::vector<int>cl{-selector(li),-selector(ri)};if(lf>=0&&rf>=0){if(lf==smul_byte(a,rf))throw std::runtime_error("fixed collision");return;}if(lf>=0){int j=uindex(ri);for(int b=0;b<8;b++){int q=lbit(j,a,b);cl.push_back((lf>>b&1)?-q:q);}}else if(rf>=0){int i=uindex(li),c=smul_byte(a,rf);for(int b=0;b<8;b++)cl.push_back((c>>b&1)?-primary(i,b):primary(i,b));}else{int i=uindex(li),j=uindex(ri);for(int b=0;b<8;b++)cl.push_back(cnf.xor2(primary(i,b),lbit(j,a,b)));}cnf.clause(cl);nmo++;};for(int i=0;i<51;i++)for(int j=i+1;j<51;j++)for(int a:NONH)cne(i,j,a);
 for(auto&d:desc){std::vector<int>cl;bool taut=false;for(int b=0;b<8;b++){std::vector<int>t;for(int q=0;q<d.arity;q++)t.push_back(lbit(d.index[q],d.scalar[q],b));int p=cnf.xormany(t),cb=(d.constant>>b)&1;if(!p){if(cb){taut=true;break;}}else cl.push_back(cb?-p:p);}if(!taut){cnf.clause(cl);nf++;}}
 cnf.close();std::ofstream out(output,std::ios::binary);out<<"c self-contained Class-22 APN permutation instance with perfect-matching witness\n"<<"c primary variables 1+8*i+b, 0<=i<49, 0<=b<8\n"<<"c selectors 393+f, 0<=f<51\n"<<"c full representatives";for(int r:full)out<<' '<<r;out<<"\n"<<"c domain "<<nd<<" orbit-distinct "<<np<<" matching-input "<<nmi<<" matching-output "<<nmo<<" APN "<<nf<<"\n"<<"p cnf "<<cnf.next_var()-1<<' '<<cnf.count()<<"\n";std::ifstream in(temp,std::ios::binary);out<<in.rdbuf();out.close();in.close();std::remove(temp.c_str());std::cerr<<"vars="<<cnf.next_var()-1<<" clauses="<<cnf.count()<<" gates="<<cnf.gates()<<" desc="<<desc.size()<<" domain="<<nd<<" pair="<<np<<" matchin="<<nmi<<" matchout="<<nmo<<" flat="<<nf<<"\n";
}catch(const std::exception&e){std::cerr<<"fatal: "<<e.what()<<'\n';return 2;}
