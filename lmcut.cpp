//
// Created by Ondrej Prenek on 2019-03-23.
//
#include <iostream>
#include <stdio.h>
#include <map>
#include <set>
#include <queue>
#include <vector>
#include <sstream>
#include <algorithm>
#include <cstdint>
#include <unordered_set>
#include <unordered_map>
#include <sstream>
#include <bitset>
#include "problem.h"

//#define DEBUG_MODE

#include <cstdio>

class ComparePair {
public:
    bool operator()(std::pair<int, int> n1, std::pair<int, int> n2) {
        return n1.first > n2.first;
    }
};

class ComparePair2 {
public:
    bool operator()(std::pair<int, std::bitset<128>> n1, std::pair<int, std::bitset<128>> n2) {
        return n1.first > n2.first;
    }
};

struct strips_bit_operator {
    std::string name;
    int cost;
    std::bitset<128> pre;
    std::bitset<128> add_eff;
    std::bitset<128> del_eff;
};
typedef struct strips_bit_operator strips_bit_operator_t;

struct bit_strips {
    int num_facts;
    std::vector<std::string> fact_names;
    std::bitset<128> init;
    std::bitset<128> goal;
    int num_operators;
    std::vector<strips_bit_operator_t> operators;
};

typedef struct bit_strips bit_strips_t;

// return list of operators which has given key fact in precondition
std::vector<int> *o_pre_fact;

strips_t init_lmcut_strips(strips_t p) {

    strips_t p2;

    int *f_init = new int[1];
    f_init[0] = p.num_facts;
    int *f_goal = new int[1];
    f_goal[0] = p.num_facts + 1;


    p2.init = f_init;
    p2.init_size = 1;

    p2.goal = f_goal;
    p2.goal_size = 1;

    p2.num_operators = p.num_operators + 2;
    p2.num_facts = p.num_facts + 2;

    p2.fact_names = (char **) malloc(sizeof(char *) * p2.num_facts);
    for (int j = 0; j < p.num_facts; ++j) {
        p2.fact_names[j] = p.fact_names[j];
    }
    p2.fact_names[p2.num_facts - 2] = "I";
    p2.fact_names[p2.num_facts - 1] = "G";

    p2.operators = new strips_operator_t[p2.num_operators];
    for (int i = 0; i < p2.num_operators - 2; ++i) {
        p2.operators[i] = p.operators[i];
    }

    strips_operator_t o_init;

    o_init.pre = (int *) calloc(1, sizeof(int));
    o_init.pre[0] = p2.num_facts - 2;
    o_init.pre_size = 1;
    auto s_vec = *new std::vector<int>;

//    for (int k = 0; k < p.num_facts; ++k) {
//        if (s.test(k)) {
//            s_vec.push_back(k);
//        }
//    }
//    o_init.add_eff_size = s_vec.size();
//    o_init.add_eff = (int*)malloc(o_init.add_eff_size * sizeof(int));
//
//    for(int i = 0; i < o_init.add_eff_size; i++){
//        o_init.add_eff[i] = s_vec[i];
//    }
    o_init.del_eff_size = 0;
    o_init.cost = 0;
    o_init.name = "o_init";
    p2.operators[p2.num_operators - 2] = o_init;

    // add o_goal
    strips_operator_t o_goal;

    o_goal.pre_size = p.goal_size;
    o_goal.pre = p.goal;
    o_goal.cost = 0;
    o_goal.del_eff_size = 0;
    o_goal.del_eff = (int *) calloc(1, sizeof(int));

    o_goal.add_eff = (int *) malloc(sizeof(int) * 1);
    o_goal.add_eff[0] = p2.num_facts - 1;
    o_goal.add_eff_size = 1;
    o_goal.name = "o_goal";

    p2.operators[p2.num_operators - 1] = o_goal;

    return p2;
}

bit_strips init_bit_strips(strips p) {
    bit_strips_t p2;
    p2.num_facts = p.num_facts;
    p2.num_operators = p.num_operators;
    p2.fact_names = *new std::vector<std::string>;
    o_pre_fact = new std::vector<int>[p2.num_facts + 2];
    o_pre_fact[p2.num_facts].push_back(p2.num_operators);

    for (int i = 0; i < p2.num_facts; ++i) {
        p2.fact_names.emplace_back(p.fact_names[i]);
    }
    p2.operators = *new std::vector<strips_bit_operator>;

    for (int i = 0; i < p.init_size; ++i) {
        p2.init[p.init[i]] = true;
    }
    for (int i = 0; i < p.goal_size; ++i) {
        p2.goal[p.goal[i]] = true;
        o_pre_fact[p.goal[i]].push_back(p2.num_operators + 1);
    }
    for (int i = 0; i < p2.num_operators; ++i) {
        strips_bit_operator o2;
        auto o1 = p.operators[i];


        o2.cost = o1.cost;
        o2.name = o1.name;

        for (int j = 0; j < o1.pre_size; ++j) {
            o2.pre[o1.pre[j]] = true;
            o_pre_fact[o1.pre[j]].push_back(i);
        }
        for (int j = 0; j < o1.add_eff_size; ++j) {
            o2.add_eff[o1.add_eff[j]] = true;
        }
        for (int j = 0; j < o1.del_eff_size; ++j) {
            o2.del_eff[o1.del_eff[j]] = true;
        }
        p2.operators.push_back(o2);
    }
    return p2;
}

bool is_goal(std::bitset<128> s, std::bitset<128> goal) {
    return (s & goal) == goal;
}


std::vector<int> succ(std::bitset<128> &s1, bit_strips_t &p) {
    auto succ_list = *new std::vector<int>;
    for (int i = 0; i < p.num_operators; ++i) {
        auto op = p.operators[i];
        if ((p.operators[i].pre & s1) == p.operators[i].pre) {
            succ_list.push_back(i);
        }
    }
    return succ_list;
}

std::pair<int, std::vector<int>> h_max(std::bitset<128> &s, strips_t &p) {
    std::vector<int> delta(p.num_facts, INT32_MAX); 
    for (int i = 0; i < p.num_facts; ++i) {
        if (s[i] == 0) continue;
        delta[i] = 0;
    }

    for (int i = 0; i < p.num_operators; ++i) {
        if (p.operators[i].pre_size > 0) continue;
        auto op = p.operators[i];
        for (int j = 0; j < op.add_eff_size; ++j) {
            delta[op.add_eff[j]] = std::min(delta[op.add_eff[j]], op.cost);
        }
    }

    std::vector<int> U(p.num_operators, 0);

    for (int i = 0; i < p.num_operators; ++i) {
        U[i] = p.operators[i].pre_size;
    }

    std::set<int> goal;
    for (int i = 0; i < p.goal_size; ++i) {
        goal.insert(p.goal[i]);
    }

    std::vector<int> C = *new std::vector<int>();
    std::set<int> closed;
    int hmax = 0;

    std::priority_queue<std::pair<int, int>, std::vector<std::pair<int, int>>, ComparePair> q;
    for (int i = 0; i < p.num_facts; ++i) {
        q.push(std::make_pair(delta[i], i));
    }

    std::pair<int, int> q_min;
    int c, d, f;
    while (!goal.empty()) {
        q_min = q.top();
        d = q_min.first;
        c = q_min.second;
        q.pop();

        while (closed.find(c) != closed.end()) {
            q_min = q.top();
            d = q_min.first;
            c = q_min.second;
            q.pop();
        }

        closed.insert(c);
        C.push_back(c);
        delta[c] = d;

        if (goal.find(c) != goal.end()) {
            goal.erase(c);
            hmax = std::max(d, hmax);
        };

        for (int i: o_pre_fact[c]) {
            auto o = p.operators[i];
            U[i]--;
            if (U[i] == 0) {
                for (int k = 0; k < o.add_eff_size; ++k) {
                    f = o.add_eff[k];
                    q.push(std::make_pair(o.cost + delta[c], f));
                    delta[f] = std::min(delta[f], o.cost + delta[c]);
                    if (delta[f] < 0) delta[f] = INT32_MAX;
                }
            }

        }
    }
    return std::make_pair(hmax, delta);
}

std::vector<int> compute_deltas(std::bitset<128> &s, strips_t &p) {
    return h_max(s, p).second;
}

int h_max_value(std::bitset<128> &s, strips_t &p) {
    return h_max(s, p).first;
}

std::vector<std::string>
construct_path(std::bitset<128> s, std::unordered_map<std::bitset<128>, std::bitset<128>> &pred,
               std::unordered_map<std::bitset<128>, int> &action,
               bit_strips &p) {
    auto path = *new std::vector<std::string>;
    while (pred.find(s) != pred.end()) {
        path.push_back(p.operators[action[s]].name);
        s = pred[s];
    }

    std::reverse(std::begin(path), std::end(path));

    return path;
}

std::pair<int, std::bitset<128>> create_state(std::bitset<128> s, strips_bit_operator succ) {
    std::bitset<128> s_new;

    s_new = s_new | s;
    s_new = s_new | succ.add_eff;
    s_new = s_new & ~succ.del_eff;

    return std::make_pair(succ.cost, s_new);
}

int h_lm_cut(std::bitset<128> s_init, strips_t p_ai, std::vector<int> &o_cost) {
    int h_lm = 0;

//    auto p_ai = init_lmcut_strips(p, s_init);

    auto s_vec = *new std::vector<int>;

    int o_init_add_eff_size = 0;
    for (int k = 0; k < p_ai.num_facts; ++k) {
        if (s_init.test(k)) {
            s_vec.push_back(k);
            o_init_add_eff_size++;
        }
    }
    auto o_init = &p_ai.operators[p_ai.num_operators - 2];
    o_init->add_eff_size = o_init_add_eff_size;
    o_init->add_eff = (int *) malloc(o_init_add_eff_size * sizeof(int));

    for (int i = 0; i < o_init->add_eff_size; i++) {
        o_init->add_eff[i] = s_vec[i];
    }

    auto hm = h_max(s_init, p_ai);
    int hmax = hm.first;
    std::vector<int> delta = hm.second;
    std::vector<int> supp(p_ai.num_operators, 0);

    if (hmax == INT32_MAX) {
        return INT32_MAX;
    }
    while (hmax != 0) {
        // update sup after each iteration
        for (int i = 0; i < p_ai.num_operators; ++i) {
            auto o = p_ai.operators[i];
            int max_val = INT16_MIN;
            for (int j = 0; j < o.pre_size; ++j) {
                if (delta[o.pre[j]] > max_val) {
                    supp[i] = o.pre[j];
                    max_val = delta[o.pre[j]];
                }
            }
        }

        // Justification graph
        std::vector<int> adj_matrix[p_ai.num_facts][p_ai.num_facts];
        for (int i = 0; i < p_ai.num_operators; ++i) {
            auto n1 = supp[i];
            for (int j = 0; j < p_ai.operators[i].add_eff_size; ++j) {
                auto n2 = p_ai.operators[i].add_eff[j];
                adj_matrix[n1][n2].push_back(i);
            }
        }

//        Construct an s-t-cut C
//         N* all nodes from which t can be reach with zero cost
        std::unordered_set<int> n_star;
        std::queue<int> q_star;
        q_star.push(p_ai.goal[0]);

        while (!q_star.empty()) {
            int n = q_star.front();
            q_star.pop();
            if (n_star.find(n) != n_star.end()) continue;
            n_star.insert(n);

            for (int i = 0; i < p_ai.num_facts; ++i) {
                for (int j = 0; j < adj_matrix[i][n].size(); ++j) {
                    if (p_ai.operators[adj_matrix[i][n][j]].cost == 0) {
                        q_star.push(i);
                    }
                }
            }
        }

        // N0 all nodes reachable from s
        std::unordered_set<int> n_0;
        std::unordered_set<int> L;
        int mi = INT32_MAX;
        std::queue<int> q_0;
        q_0.push(p_ai.init[0]);
        while (!q_0.empty()) {
            int n = q_0.front();
            q_0.pop();
            if (n_0.find(n) != n_0.end()) continue;
            n_0.insert(n);

            for (int i = 0; i < p_ai.num_facts; ++i) {
                if (adj_matrix[n][i].empty()) continue;
                if (n_star.find(i) == n_star.end()) {
                    q_0.push(i);
                } else {
                    for (int o: adj_matrix[n][i]) {
                        L.insert(o);
                        mi = std::min(mi, p_ai.operators[o].cost);
                    }
                }
            }
        }

        h_lm += mi;

        // set justification graph i+1
        // ci+1(o) = ci(o) - mi, if o in L
        for (int o: L) {
            p_ai.operators[o].cost -= mi;
        }
//
//        //go through adj matrix using DAG to update delta (considering delta for init = hmax)
//        // propagate the updated values down the edges
//        std::queue<int> q;
//        for (int o: L) {
//            for (int i = 0; i < p_ai.operators[o].add_eff_size; ++i) {
//                q.push(p_ai.operators[o].add_eff[i]);
//            }
//        }

//        std::unordered_set<int> closed;
//        while (!q.empty()) {
//            int n = q.front();
//            q.pop();
//            if (closed.find(n) != closed.end()) continue;
//            closed.insert(n);
//
//            for (int i = 0; i < p_ai.num_facts; ++i) {
//                if (!adj_matrix[n][i].empty()) {
//                    q.push(i);
//                }
//                if (adj_matrix[i][n].empty()) continue;
//                delta[n] = delta[i] + p_ai.operators[adj_matrix[i][n][0]].cost;
//
//                for (int o: adj_matrix[i][n]) {
//                    if (n == p_ai.goal[0]) {
//                        delta[n] = std::max(delta[n], delta[i] + p_ai.operators[o].cost);
//                    } else {
//                        delta[n] = std::min(delta[n], delta[i] + p_ai.operators[o].cost);
//                    }
//                }
//
//            }
//        }

        delta = compute_deltas(s_init, p_ai);

        hmax = delta[p_ai.goal[0]];

    }

    for (int i = 0; i < p_ai.num_operators; ++i) {
        p_ai.operators[i].cost = o_cost[i];
    }


    return h_lm;
}


std::pair<int, std::vector<std::string>> astar_strips(bit_strips_t &p, strips_t &p_ai, std::vector<int> &o_cost) {
    std::priority_queue<std::pair<int, std::bitset<128>>, std::vector<std::pair<int, std::bitset<128>>>, ComparePair2> q;
    std::unordered_set<std::bitset<128>> closed;
    std::unordered_map<std::bitset<128>, std::bitset<128>> pred;
    std::unordered_map<std::bitset<128>, int> dist;
    std::unordered_map<std::bitset<128>, int> action;
    std::unordered_map<std::bitset<128>, int> hmax_map;

    q.push(std::make_pair(0, p.init));
    dist[p.init] = 0;
    int nodes_c = 0;
    while (!q.empty()) {
        auto _s1 = q.top();
        auto s1 = _s1.second;
        int s1_c = dist[s1];
        nodes_c++;
        q.pop();

#ifdef DEBUG_MODE
        if (nodes_c % 1000 == 0) {
            std::cout << "Nodes count: " << nodes_c << std::endl;
        }
#endif

        if (closed.find(s1) == closed.end()) {
            closed.insert(s1);

            if (is_goal(s1, p.goal)) {
#ifdef DEBUG_MODE
                std::cout << "Nodes count: " << nodes_c << std::endl;
#endif
                return std::make_pair(s1_c, construct_path(s1, pred, action, p));
            }

            auto b = succ(s1, p);
            for (int i: succ(s1, p)) {
                auto succ1 = p.operators[i];
                auto _s2 = create_state(s1, succ1);
                int c = _s2.first;
                auto s2 = _s2.second;
                int s2_c = s1_c + c;

                // if not closed
                if (closed.find(s2) == closed.end()) {
                    if (hmax_map.find(s2) != hmax_map.end()) {
                        if (s2_c < dist[s2]) {
                            pred[s2] = s1;
                            dist[s2] = s2_c;
                            action[s2] = i;
                            q.push(std::make_pair(s2_c + hmax_map[s2], s2));
                        }
                    } else {
                        pred[s2] = s1;
                        dist[s2] = s2_c;
                        action[s2] = i;
                        int s2_h = h_lm_cut(s2, p_ai, o_cost);
                        q.push(std::make_pair(s2_c + s2_h, s2));
                        hmax_map[s2] = s2_h;
                    }
                }
            }
        }
    }

    std::pair<int, std::vector<std::string>> path;
    return path;
}

int main(int argc, char *argv[]) {
    std::ios::sync_with_stdio(false);

#ifdef DEBUG_MODE
    clock_t begin = clock();
#endif
    strips_t strips;
//    fdr_t fdr;

    if (argc != 3) {
        fprintf(stderr, "Usage: %s problem.strips problem.fdr\n", argv[0]);
        return -1;
    }

    // Load the planning problem in STRIPS or FDR
    stripsRead(&strips, argv[1]);
    bit_strips p2 = init_bit_strips(strips);
    strips_t p_ai = init_lmcut_strips(strips);
    // compute ai operator cost
    std::vector<int> o_cost(p_ai.num_operators, 0);
    for (int m = 0; m < p_ai.num_operators; ++m) {
        o_cost[m] = p_ai.operators[m].cost;
    }
//    fdrRead(&fdr, argv[2]);

    // Implement the search here
    int hmax_init = h_max_value(p2.init, p_ai);
    std::cout << ";; h^max for init: " << hmax_init << std::endl;
//    int hlmcut = h_lm_cut(p2.init, strips);
//    std::cout << ";; h^lmcut for init: " << hlmcut << std::endl;
    auto plan = astar_strips(p2, p_ai, o_cost);
    std::cout << ";; Cost: " << plan.first << std::endl;
    for (std::string &action: plan.second) {
        std::cout << action << std::endl;
    }
#ifdef DEBUG_MODE
    clock_t end = clock();
    double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
    std::cout << "Elapsed time: " << elapsed_secs << "s" << std::endl;
#endif
    stripsFree(&strips);
//    fdrFree(&fdr);

}