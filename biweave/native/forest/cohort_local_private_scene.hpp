#pragma once

struct CohortLocalPrivateScene {
    static constexpr U MEMORY_BUDGET = 64ULL * 1024 * 1024;
     
    static constexpr U LABEL_CHARGE = 512, ACTOR_CHARGE = 128, BASE_CHARGE = 4096;
    struct Entry { uint8_t arity=0; int actor=-1; I weight=0; };
    struct Private { int label=-1, actor=-1; I weight=0; };
    struct Witness {
        std::vector<int> actors;
        std::vector<Private> records;
        U scan_bound=0, label_bound=0, estimated_bytes=0, scanned=0;
        bool qualified=false;
        std::string reason;
    };
    static int vertex(const Graph&g,int o,int actor) { return o?g.nr+actor:actor; }
    static int actor_of(const Edge&e,int o) { return o?e.c:e.r; }
    static int label_of(const Edge&e,int o) { return o?e.r:e.c; }
    static Witness collect(const Graph&g,int o,int root) {
        if(g.D) throw std::runtime_error("local cohort needs returned exact margins");
        if(o!=0&&o!=1) throw std::runtime_error("local cohort orientation");
        const int rv=o?root:g.nr+root;
        if(rv<0||rv>=g.nr+g.nc||g.target_degree[rv]<2)
            throw std::runtime_error("local cohort root outside fixed pool");
        if(g.adj[rv].size()!=U(g.target_degree[rv]))
            throw std::runtime_error("local cohort root support degree");
        Witness result;
        for(int id:g.adj[rv]) {
            const int actor=actor_of(g.edges[id],o), av=vertex(g,o,actor);
            if(g.adj[av].size()!=U(g.target_degree[av]))
                throw std::runtime_error("local cohort actor degree");
            const U d=U(g.target_degree[av]);
            if(result.scan_bound>std::numeric_limits<U>::max()-d)
                throw std::runtime_error("local cohort scan bound overflow");
            result.scan_bound+=d;
        }
        const U nr=g.adj[rv].size(), opposite=o?U(g.nr):U(g.nc);
        result.label_bound=std::min(opposite-1,result.scan_bound-nr);
        const __uint128_t charge=__uint128_t(result.label_bound)*LABEL_CHARGE+
                                 __uint128_t(nr)*ACTOR_CHARGE+BASE_CHARGE;
        result.estimated_bytes=charge>std::numeric_limits<U>::max()?
                               std::numeric_limits<U>::max():U(charge);
        if(charge>MEMORY_BUDGET) { result.reason="local_collection_payload_guard"; return result; }
        result.actors.reserve(nr);
        for(int id:g.adj[rv]) result.actors.push_back(actor_of(g.edges[id],o));
        std::sort(result.actors.begin(),result.actors.end());
        if(std::adjacent_find(result.actors.begin(),result.actors.end())!=result.actors.end())
            throw std::runtime_error("local cohort duplicate actor");
        std::map<int,Entry> support;
        for(int actor:result.actors) for(int id:g.adj[vertex(g,o,actor)]) {
            ++result.scanned;
            const Edge&e=g.edges[id]; const int label=label_of(e,o);
            if(label==root) continue;
            auto&slot=support[label];
            if(!slot.arity) { slot.actor=actor; slot.weight=e.w; }
            if(slot.arity<2) ++slot.arity;  
        }
        if(result.scanned!=result.scan_bound||support.size()>result.label_bound)
            throw std::runtime_error("local cohort preflight support bound");
        result.records.reserve(support.size());
        for(const auto&[label,slot]:support) if(slot.arity==1) {
            if(slot.weight<=0) throw std::runtime_error("local cohort nonpositive carried weight");
            result.records.push_back({label,slot.actor,slot.weight});
        }
        result.qualified=true; result.reason="exact_local_singleton_support";
        return result;
    }
};
