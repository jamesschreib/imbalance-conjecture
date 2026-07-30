#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>

extern "C" {
typedef struct _Z3_config *Z3_config;
typedef struct _Z3_context *Z3_context;
typedef struct _Z3_symbol *Z3_symbol;
typedef struct _Z3_sort *Z3_sort;
typedef struct _Z3_ast *Z3_ast;
typedef struct _Z3_solver *Z3_solver;
typedef struct _Z3_model *Z3_model;
typedef struct _Z3_tactic *Z3_tactic;
typedef int Z3_lbool;
Z3_config Z3_mk_config(void); void Z3_del_config(Z3_config);
void Z3_set_param_value(Z3_config,const char*,const char*);
Z3_context Z3_mk_context(Z3_config); void Z3_del_context(Z3_context);
Z3_symbol Z3_mk_string_symbol(Z3_context,const char*);
Z3_sort Z3_mk_bool_sort(Z3_context);
Z3_ast Z3_mk_const(Z3_context,Z3_symbol,Z3_sort);
Z3_ast Z3_mk_false(Z3_context); Z3_ast Z3_mk_not(Z3_context,Z3_ast);
Z3_ast Z3_mk_or(Z3_context,unsigned,Z3_ast const[]);
Z3_ast Z3_mk_xor(Z3_context,Z3_ast,Z3_ast);
Z3_tactic Z3_mk_tactic(Z3_context,const char*);
Z3_solver Z3_mk_solver_from_tactic(Z3_context,Z3_tactic);
void Z3_solver_inc_ref(Z3_context,Z3_solver); void Z3_solver_dec_ref(Z3_context,Z3_solver);
void Z3_solver_assert(Z3_context,Z3_solver,Z3_ast);
Z3_lbool Z3_solver_check(Z3_context,Z3_solver);
Z3_model Z3_solver_get_model(Z3_context,Z3_solver);
void Z3_model_inc_ref(Z3_context,Z3_model); void Z3_model_dec_ref(Z3_context,Z3_model);
int Z3_model_eval(Z3_context,Z3_model,Z3_ast,int,Z3_ast*);
Z3_lbool Z3_get_bool_value(Z3_context,Z3_ast);
const char* Z3_solver_get_reason_unknown(Z3_context,Z3_solver);
void Z3_global_param_set(const char*,const char*);
}

static constexpr std::array<uint8_t,5> H{{1,2,4,8,15}};
static uint8_t kmul[16][16];
static uint8_t tr[16][256];
static uint8_t lin[16][8];

static void init_field() {
    auto mul=[](int a,int b){int r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&16)a^=31;}return r&15;};
    for(int a=0;a<16;a++) for(int b=0;b<16;b++) kmul[a][b]=mul(a,b);
    for(int a=0;a<16;a++) for(int v=0;v<256;v++)
        tr[a][v]=kmul[a][v&15] | (kmul[a][v>>4]<<4);
    for(int a=1;a<16;a++) for(int ob=0;ob<8;ob++) {
        uint8_t mask=0;
        for(int ib=0;ib<8;ib++) if((tr[a][1u<<ib]>>ob)&1u) mask|=1u<<ib;
        lin[a][ob]=mask;
    }
}

struct GenericDesc {
    uint8_t base=0, zcoef=0, wcoef=0, arity=0;
    std::array<uint8_t,4> index{}, scalar{};
};
struct Desc {
    uint8_t constant=0, arity=0;
    std::array<uint8_t,4> index{}, scalar{};
};

static double elapsed(const std::chrono::steady_clock::time_point& t) {
    return std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
}

int main(int argc,char**argv) {
    if(argc<3) {
        std::cerr << "usage: " << argv[0] << " Z W [initial_arity=4] [max_rounds=1] [prefix=case] [add_cap=0] [simple=0]\n";
        return 2;
    }
    const int zfix=std::atoi(argv[1]), wfix=std::atoi(argv[2]);
    const int initial=argc>3?std::atoi(argv[3]):4;
    const int maxround=argc>4?std::atoi(argv[4]):1;
    const std::string prefix=argc>5?argv[5]:"case";
    const int addcap=argc>6?std::atoi(argv[6]):0;
    const bool simple=argc>7?std::atoi(argv[7])!=0:false;
    if(zfix<=0||zfix>255||wfix<=0||wfix>255) return 2;
    init_field();

    int orbit_id[256]; std::fill(std::begin(orbit_id),std::end(orbit_id),-1);
    std::vector<int> reps;
    for(int v=1;v<256;v++) if(orbit_id[v]<0) {
        std::array<int,5> o{}; for(int k=0;k<5;k++) o[k]=tr[H[k]][v];
        std::sort(o.begin(),o.end());
        int id=reps.size(); reps.push_back(o[0]); for(int x:o) orbit_id[x]=id;
    }
    std::map<int,int> fixed_pos{{1,0},{3,1},{5,2},{16,3}};
    std::vector<int> unknown;
    for(int r:reps) if(!fixed_pos.count(r)) unknown.push_back(r);
    if(reps.size()!=51 || unknown.size()!=47) return 2;

    uint8_t point_kind[256]{}, point_index[256]{}, point_scalar[256]{};
    point_kind[0]=1; point_index[0]=4;
    for(auto [r,j]:fixed_pos) for(uint8_t h:H) {
        int p=tr[h][r]; point_kind[p]=1; point_index[p]=j; point_scalar[p]=h;
    }
    for(int i=0;i<47;i++) for(uint8_t h:H) {
        int p=tr[h][unknown[i]]; point_kind[p]=2; point_index[p]=i; point_scalar[p]=h;
    }
    for(int p=0;p<256;p++) if(!point_kind[p]) return 2;

    std::vector<GenericDesc> generic; generic.reserve(138176);
    uint64_t flat_count=0;
    for(int x=0;x<256;x++) for(int y=x+1;y<256;y++) for(int z=y+1;z<256;z++) {
        int w=x^y^z; if(w<=z) continue;
        std::array<int,4> f{{x,y,z,w}}, best=f;
        for(uint8_t h:H) {
            std::array<int,4> q{}; for(int k=0;k<4;k++) q[k]=tr[h][f[k]];
            std::sort(q.begin(),q.end()); if(q<best) best=q;
        }
        flat_count++; if(f!=best) continue;
        GenericDesc d; uint8_t coef[47]{};
        for(int p:f) {
            uint8_t h=point_scalar[p];
            if(point_kind[p]==1) {
                int j=point_index[p];
                if(j==0) d.base ^= tr[h][1];
                else if(j==1) d.base ^= tr[h][16];
                else if(j==2) d.zcoef ^= h;
                else if(j==3) d.wcoef ^= h;
            } else coef[point_index[p]] ^= h;
        }
        for(int i=0;i<47;i++) if(coef[i]) {
            d.index[d.arity]=i; d.scalar[d.arity]=coef[i]; d.arity++;
        }
        generic.push_back(d);
    }
    if(flat_count!=690880 || generic.size()!=138176) return 2;

    std::vector<Desc> desc; desc.reserve(generic.size());
    std::array<int,5> arity_count{}; int taut=0, contradiction=0;
    for(const auto& g:generic) {
        Desc d; d.constant=g.base ^ tr[g.zcoef][zfix] ^ tr[g.wcoef][wfix]; d.arity=g.arity;
        for(int q=0;q<g.arity;q++){d.index[q]=g.index[q];d.scalar[q]=g.scalar[q];}
        if(!d.arity) { if(d.constant) taut++; else contradiction++; }
        else { desc.push_back(d); arity_count[d.arity]++; }
    }
    std::cerr << "z="<<zfix<<" w="<<wfix<<" arity "
              <<arity_count[1]<<' '<<arity_count[2]<<' '<<arity_count[3]<<' '<<arity_count[4]
              <<" taut="<<taut<<" contradiction="<<contradiction<<"\n";
    if(contradiction) { std::cout<<"UNSAT fixed contradiction\n"; return 20; }

    Z3_global_param_set("model","true");
    Z3_config cfg=Z3_mk_config(); Z3_set_param_value(cfg,"model","true");
    Z3_context ctx=Z3_mk_context(cfg); Z3_del_config(cfg);
    Z3_sort bool_sort=Z3_mk_bool_sort(ctx);
    auto mkvar=[&](const std::string& n){return Z3_mk_const(ctx,Z3_mk_string_symbol(ctx,n.c_str()),bool_sort);};
    auto mkxor=[&](const std::vector<Z3_ast>& v){if(v.empty())return Z3_mk_false(ctx);Z3_ast r=v[0];for(size_t i=1;i<v.size();i++)r=Z3_mk_xor(ctx,r,v[i]);return r;};
    auto mkor=[&](const std::vector<Z3_ast>& v){if(v.empty())return Z3_mk_false(ctx);if(v.size()==1)return v[0];return Z3_mk_or(ctx,v.size(),v.data());};
    Z3_solver solver=Z3_mk_solver_from_tactic(ctx,Z3_mk_tactic(ctx,"sat")); Z3_solver_inc_ref(ctx,solver);
    Z3_ast y[47][8];
    for(int i=0;i<47;i++) for(int b=0;b<8;b++) y[i][b]=mkvar("y_"+std::to_string(i)+"_"+std::to_string(b));
    Z3_ast L[47][16][8]{};
    for(int i=0;i<47;i++) for(int a=1;a<16;a++) for(int b=0;b<8;b++) {
        std::vector<Z3_ast> terms; for(int q=0;q<8;q++) if((lin[a][b]>>q)&1u) terms.push_back(y[i][q]);
        L[i][a][b]=mkxor(terms);
    }
    uint64_t assertions=0;
    auto add=[&](Z3_ast a){Z3_solver_assert(ctx,solver,a);assertions++;};
    auto ne_const=[&](int i,uint8_t v){std::vector<Z3_ast> bits;for(int b=0;b<8;b++)bits.push_back((v>>b)&1?Z3_mk_not(ctx,y[i][b]):y[i][b]);return mkor(bits);};
    auto ne_scaled=[&](int i,int j,int a){std::vector<Z3_ast> bits;for(int b=0;b<8;b++)bits.push_back(Z3_mk_xor(ctx,y[i][b],L[j][a][b]));return mkor(bits);};
    auto flat_ast=[&](const Desc& d){std::vector<Z3_ast> bits;for(int b=0;b<8;b++){std::vector<Z3_ast> terms;for(int q=0;q<d.arity;q++)terms.push_back(L[d.index[q]][d.scalar[q]][b]);Z3_ast r=mkxor(terms);if((d.constant>>b)&1u)r=Z3_mk_not(ctx,r);bits.push_back(r);}return mkor(bits);};

    auto t0=std::chrono::steady_clock::now();
    bool forbidden[256]{}; forbidden[0]=true;
    for(int f:{1,16,zfix,wfix}) for(uint8_t h:H) forbidden[tr[h][f]]=true;
    int forbidden_count=0;for(bool b:forbidden)forbidden_count+=b;
    if(forbidden_count!=21) return 2;
    for(int i=0;i<47;i++) for(int v=0;v<256;v++) if(forbidden[v]) add(ne_const(i,v));
    for(int i=0;i<47;i++) for(int j=i+1;j<47;j++) for(uint8_t h:H) add(ne_scaled(i,j,h));

    uint64_t simple_extra=0;
    if(simple) {
        auto projective=[&](int v){int r=999;for(int a=1;a<16;a++)r=std::min(r,(int)tr[a][v]);return r;};
        for(int i=0;i<47;i++) for(int j=i+1;j<47;j++) if(projective(unknown[i])==projective(unknown[j]))
            for(int a=1;a<16;a++) if(std::find(H.begin(),H.end(),a)==H.end()) {add(ne_scaled(i,j,a));simple_extra++;}
        int fixed_line=projective(16);
        for(int i=0;i<47;i++) if(projective(unknown[i])==fixed_line)
            for(int a=1;a<16;a++) { add(ne_const(i,tr[a][wfix])); simple_extra++; }
    }

    std::vector<uint8_t> added(desc.size()); std::vector<uint32_t> used;
    uint64_t nflat=0;
    for(uint32_t q=0;q<desc.size();q++) if(desc[q].arity<=initial) {add(flat_ast(desc[q]));added[q]=1;used.push_back(q);nflat++;}
    std::cerr<<"simple="<<simple<<" simple-extra="<<simple_extra<<" assertions="<<assertions<<" flats="<<nflat<<" build="<<elapsed(t0)<<"\n";

    for(int round=0;round<maxround;round++) {
        auto tc=std::chrono::steady_clock::now(); Z3_lbool result=Z3_solver_check(ctx,solver); double check_time=elapsed(tc);
        if(result==-1) {
            std::cerr<<"UNSAT round="<<round<<" flats="<<nflat<<" check="<<check_time<<" total="<<elapsed(t0)<<"\n";
            std::ofstream f(prefix+".unsat_indices",std::ios::binary);uint32_t n=used.size();f.write((char*)&n,4);f.write((char*)used.data(),4*n);
            return 20;
        }
        if(result==0) {std::cerr<<"UNKNOWN "<<Z3_solver_get_reason_unknown(ctx,solver)<<"\n";return 0;}
        Z3_model model=Z3_solver_get_model(ctx,solver); Z3_model_inc_ref(ctx,model);
        uint8_t value[47]{};
        for(int i=0;i<47;i++)for(int b=0;b<8;b++){Z3_ast v=nullptr;if(!Z3_model_eval(ctx,model,y[i][b],1,&v))return 3;if(Z3_get_bool_value(ctx,v)==1)value[i]|=1u<<b;}
        Z3_model_dec_ref(ctx,model);
        std::vector<uint32_t> bad; std::array<int,5> by_arity{};
        for(uint32_t q=0;q<desc.size();q++) if(!added[q]) {
            const auto& d=desc[q];uint8_t r=d.constant;for(int k=0;k<d.arity;k++)r^=tr[d.scalar[k]][value[d.index[k]]];
            if(!r){bad.push_back(q);by_arity[d.arity]++;}
        }
        std::cerr<<"round="<<round<<" check="<<check_time<<" bad="<<bad.size()<<" ["<<by_arity[1]<<','<<by_arity[2]<<','<<by_arity[3]<<','<<by_arity[4]<<"] flats="<<nflat<<" total="<<elapsed(t0)<<"\n";
        if(bad.empty()) {
            std::ofstream f(prefix+".witness");f<<"1 1\n3 16\n5 "<<zfix<<"\n16 "<<wfix<<"\n";for(int i=0;i<47;i++)f<<unknown[i]<<' '<<(int)value[i]<<'\n';
            std::cout<<"SAT witness "<<prefix<<".witness\n";return 10;
        }
        if(addcap>0 && (int)bad.size()>addcap){std::stable_sort(bad.begin(),bad.end(),[&](uint32_t a,uint32_t b){return desc[a].arity<desc[b].arity;});bad.resize(addcap);}
        for(uint32_t q:bad){add(flat_ast(desc[q]));added[q]=1;used.push_back(q);nflat++;}
    }
    return 6;
}
