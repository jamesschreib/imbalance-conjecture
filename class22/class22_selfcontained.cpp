#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

static int kmul(int a,int b){int r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&16)a^=31;}return r&15;}
static int smul_byte(int a,int x){return kmul(a,x&15)|(kmul(a,x>>4)<<4);}
static constexpr std::array<int,5> H{{1,2,4,8,15}};

struct Desc { uint8_t constant=0, arity=0; std::array<uint8_t,4> index{}, scalar{}; };

static std::vector<int> unknown_reps(){
 std::array<int,256> seen{}; std::vector<int> reps;
 for(int v=1;v<256;v++)if(!seen[v]){std::vector<int>o;for(int h:H){int w=smul_byte(h,v);o.push_back(w);seen[w]=1;}std::sort(o.begin(),o.end());reps.push_back(o[0]);}
 std::vector<int> u;for(int r:reps)if(r!=1&&r!=16)u.push_back(r);return u;
}

static std::vector<Desc> generate_desc(){
 auto unknown=unknown_reps(); if(unknown.size()!=49)throw std::runtime_error("bad unknown count");
 std::array<int,256> kind{}, idx{}, coeff{}, fixed{}; kind.fill(-1);
 kind[0]=0;fixed[0]=0;
 for(int h:H){int p=smul_byte(h,1);kind[p]=0;fixed[p]=p;p=smul_byte(h,16);kind[p]=0;fixed[p]=p;}
 for(int i=0;i<49;i++)for(int h:H){int p=smul_byte(h,unknown[i]);if(kind[p]!=-1)throw std::runtime_error("duplicate point");kind[p]=1;idx[p]=i;coeff[p]=h;}
 for(int p=0;p<256;p++)if(kind[p]<0)throw std::runtime_error("unmapped point");
 std::vector<Desc> out;out.reserve(138176);
 for(int x=0;x<256;x++)for(int y=x+1;y<256;y++)for(int z=y+1;z<256;z++){
   int w=x^y^z;if(w<=z)continue;std::array<int,4> f{{x,y,z,w}},best=f;
   for(int h:H){std::array<int,4>g;for(int q=0;q<4;q++)g[q]=smul_byte(h,f[q]);std::sort(g.begin(),g.end());if(g<best)best=g;}
   if(f!=best)continue;
   Desc d;int c=0;std::array<int,49> cs{};
   for(int p:f){if(kind[p]==0)c^=fixed[p];else cs[idx[p]]^=coeff[p];}
   d.constant=c;for(int i=0;i<49;i++)if(cs[i]){if(d.arity>=4)throw std::runtime_error("arity overflow");d.index[d.arity]=i;d.scalar[d.arity]=cs[i];d.arity++;}
   if(!d.arity)throw std::runtime_error("zero arity");out.push_back(d);
 }
 if(out.size()!=138176)throw std::runtime_error("bad flat orbit count "+std::to_string(out.size()));return out;
}

class CNFWriter{
 std::ofstream body;int next=393;uint64_t clauses=0;std::unordered_map<uint64_t,int> cache;
public:
 CNFWriter(const std::string&p):body(p,std::ios::binary){if(!body)throw std::runtime_error("body open");cache.reserve(4000000);}
 int next_var()const{return next;}uint64_t count()const{return clauses;}size_t gates()const{return cache.size();}
 void clause(const std::vector<int>&l){if(l.empty())throw std::runtime_error("empty clause");for(int x:l)body<<x<<' ';body<<"0\n";clauses++;}
 void c3(int a,int b,int c){body<<a<<' '<<b<<' '<<c<<" 0\n";clauses++;}
 int xor2(int a,int b){if(!a)return b;if(!b)return a;if(a==b)return 0;if(a>b)std::swap(a,b);uint64_t k=(uint64_t)(uint32_t)a<<32|(uint32_t)b;auto it=cache.find(k);if(it!=cache.end())return it->second;int z=next++;cache[k]=z;c3(-a,-b,-z);c3(a,b,-z);c3(a,-b,z);c3(-a,b,z);return z;}
 int xormany(std::vector<int>t){t.erase(std::remove(t.begin(),t.end(),0),t.end());std::sort(t.begin(),t.end());std::vector<int>r;for(size_t i=0;i<t.size();){size_t j=i+1;while(j<t.size()&&t[j]==t[i])j++;if((j-i)&1)r.push_back(t[i]);i=j;}t.swap(r);while(t.size()>1){std::vector<int>n;for(size_t i=0;i<t.size();i+=2)n.push_back(i+1<t.size()?xor2(t[i],t[i+1]):t[i]);std::sort(n.begin(),n.end());t.swap(n);}return t.empty()?0:t[0];}
 void close(){body.close();}
};
static int primary(int i,int b){return 1+8*i+b;}

int main(int argc,char**argv)try{
 std::string output=argc>1?argv[1]:"class22.cnf";std::string temp=output+".body";auto desc=generate_desc();
 std::array<std::array<uint8_t,8>,16> rows{};
 for(int a=1;a<16;a++)for(int bit=0;bit<8;bit++){uint8_t m=0;for(int sb=0;sb<8;sb++)if((smul_byte(a,1<<sb)>>bit)&1)m|=1<<sb;rows[a][bit]=m;}
 CNFWriter cnf(temp);std::vector<int>L(49*16*8);
 auto lbit=[&](int i,int a,int b){int&v=L[(i*16+a)*8+b];if(v)return v;std::vector<int>t;for(int s=0;s<8;s++)if((rows[a][b]>>s)&1)t.push_back(primary(i,s));v=cnf.xormany(t);if(!v)throw std::runtime_error("zero transform");return v;};
 std::vector<int> forbidden{0};for(int h:H){forbidden.push_back(smul_byte(h,1));forbidden.push_back(smul_byte(h,16));}std::sort(forbidden.begin(),forbidden.end());forbidden.erase(std::unique(forbidden.begin(),forbidden.end()),forbidden.end());
 uint64_t nd=0,np=0,nf=0;
 for(int i=0;i<49;i++)for(int x:forbidden){std::vector<int>cl;for(int b=0;b<8;b++)cl.push_back((x>>b&1)?-primary(i,b):primary(i,b));cnf.clause(cl);nd++;}
 for(int i=0;i<49;i++)for(int j=i+1;j<49;j++)for(int h:H){std::vector<int>cl;for(int b=0;b<8;b++)cl.push_back(cnf.xor2(primary(i,b),lbit(j,h,b)));cnf.clause(cl);np++;}
 for(auto&d:desc){std::vector<int>cl;bool taut=false;for(int b=0;b<8;b++){std::vector<int>t;for(int q=0;q<d.arity;q++)t.push_back(lbit(d.index[q],d.scalar[q],b));int p=cnf.xormany(t),cb=(d.constant>>b)&1;if(!p){if(cb){taut=true;break;}}else cl.push_back(cb?-p:p);}if(!taut){cnf.clause(cl);nf++;}}
 cnf.close();std::ofstream out(output,std::ios::binary);out<<"c self-contained Class-22 normalized APN permutation instance\n";out<<"c primary variables 1+8*i+b, 0<=i<49, 0<=b<8\n";out<<"c domain "<<nd<<" orbit-distinct "<<np<<" APN "<<nf<<"\n";out<<"p cnf "<<cnf.next_var()-1<<' '<<cnf.count()<<"\n";std::ifstream in(temp,std::ios::binary);out<<in.rdbuf();out.close();in.close();std::remove(temp.c_str());
 std::cerr<<"vars="<<cnf.next_var()-1<<" clauses="<<cnf.count()<<" gates="<<cnf.gates()<<" desc="<<desc.size()<<" domain="<<nd<<" pair="<<np<<" flat="<<nf<<"\n";
}catch(const std::exception&e){std::cerr<<"fatal: "<<e.what()<<'\n';return 2;}
