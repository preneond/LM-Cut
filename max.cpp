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
#include "problem.h"

#define DEBUG_MODE

class ComparePair {
public:
    bool operator()(std::pair<int, int> n1, std::pair<int, int> n2) {
        return n1.first > n2.first;
    }
};

class ComparePair2 {
public:
    bool operator()(std::pair<int, std::vector<int>> n1, std::pair<int, std::vector<int>> n2) {
        return n1.first > n2.first;
    }
};

bool is_goal(std::vector<int> s, int *goal, int goal_size) {
    for (int i = 0; i < goal_size; ++i) {
        if (std::find(s.begin(), s.end(), goal[i]) == s.end()) return false;
    }
    return true;
}

std::vector<int> succ(std::vector<int> &s1, strips_t &p) {
//    succ_list = list()
//    for i, op in enumerate(p.operators):
//    if all(map(lambda o: o in s, op.pre)):
//    succ_list.append(i)
    bool pre_node_found, pre_satisfied;
    auto succ_list = *new std::vector<int>;
    for (int i = 0; i < p.num_operators; ++i) {
        // set flag to true to indicate that all states s1 match conditions in pre
        pre_satisfied = true;
        auto op = p.operators[i];
        for (int j = 0; j < op.pre_size; ++j) {
            // set flag to false to indicate that
            if (std::find(s1.begin(), s1.end(), op.pre[j]) == s1.end()) {
                pre_satisfied = false;
                break;
            }
        }
        if (pre_satisfied) {
            succ_list.push_back(i);
        }
    }
    return succ_list;
}

std::string create_key(std::vector<int> s1) {
    std::stringstream ss;
    for (int i = 0; i < s1.size(); ++i) {
        if (i != 0)
            ss << ",";
        ss << s1[i];
    }
    return ss.str();
}

int h_max(std::vector<int> &s, strips_t &p) {
    std::vector<int> delta(p.num_facts, INT32_MAX);
    for (int i = 0; i < s.size(); ++i) {
        delta[s[i]] = 0;
    }

    for (int i = 0; i < p.num_operators; ++i) {
        if (p.operators[i].pre_size > 0) continue;
        auto op = p.operators[i];
        for (int j = 0; j < op.add_eff_size; ++j) {
            delta[op.add_eff[j]] = std::min(delta[op.add_eff[j]], op.cost);
        }
    }

    std::unordered_map<int, int> U;

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

        if (goal.erase(c) > 0) {
            hmax = std::max(d, hmax);
        };

        for (int i = 0; i < p.num_operators; ++i) {
            auto o = p.operators[i];
            for (int j = 0; j < p.operators[i].pre_size; ++j) {
                if (o.pre[j] != c) continue;
                U[i]--;
                if (U[i] == 0) {
                    for (int k = 0; k < o.add_eff_size; ++k) {
                        f = o.add_eff[k];
                        q.push(std::make_pair(o.cost + delta[c], f));
                        delta[f] = std::min(delta[f], o.cost + delta[c]);
                    }
                }
            }
        }
    }
    return hmax;
}

std::vector<std::string>
construct_path(std::string s, std::unordered_map<std::string, std::string> &pred, std::unordered_map<std::string, int> &action,
               strips_t &p) {
    auto path = *new std::vector<std::string>;
    while (pred.find(s) != pred.end()) {
        path.push_back(p.operators[action[s]].name);
        s = pred[s];
    }

    std::reverse(std::begin(path), std::end(path));

    return path;
}

std::pair<int, std::vector<int>> create_state(std::vector<int> s, strips_operator_t succ) {
    std::unordered_set<int> set_new(s.begin(), s.end());

    for (int i = 0; i < succ.add_eff_size; ++i) {
        set_new.insert(succ.add_eff[i]);
    }
    for (int i = 0; i < succ.del_eff_size; ++i) {
        set_new.erase(succ.del_eff[i]);
    }

    std::vector<int> vec_new(set_new.begin(), set_new.end());
    std::sort(vec_new.begin(), vec_new.end());

    return std::make_pair(succ.cost, vec_new);
}

std::pair<int, std::vector<std::string>> astar_strips(strips_t &p) {
    std::priority_queue<std::pair<int, std::vector<int>>, std::vector<std::pair<int, std::vector<int>>>, ComparePair2> q;
    std::unordered_set<std::string> closed;
    std::unordered_map<std::string, std::string> pred;
    std::unordered_map<std::string, int> dist;
    std::unordered_map<std::string, int> action;
    std::unordered_map<std::string, int> hmax_map;

    std::vector<int> vec_init(p.init, p.init + p.init_size);
    q.push(std::make_pair(0, vec_init));
    dist[create_key(vec_init)] = 0;
    int nodes_c = 0;
    while (!q.empty()) {
        auto _s1 = q.top();
        auto s1 = _s1.second;
        auto s1_key = create_key(s1);
        int s1_c = dist[s1_key];
        nodes_c++;
        q.pop();

#ifdef DEBUG_MODE
        if (nodes_c % 1000 == 0) {
            std::cout << "Nodes count: " << nodes_c << std::endl;
        }
#endif

        if (closed.find(s1_key) == closed.end()) {
            closed.insert(s1_key);

            if (is_goal(s1, p.goal, p.goal_size)) {
#ifdef DEBUG_MODE
                std::cout << "Nodes count: " << nodes_c << std::endl;
#endif
                return std::make_pair(s1_c, construct_path(s1_key, pred, action, p));
            }

            auto b = succ(s1, p);
            for (int i: succ(s1, p)) {
                auto succ1 = p.operators[i];
                auto _s2 = create_state(s1, succ1);
                int c = _s2.first;
                auto s2 = _s2.second;
                auto s2_key = create_key(s2);
                int s2_c = s1_c + c;

                // if not closed
                if (closed.find(s2_key) == closed.end()) {
                    if (hmax_map.find(s2_key) != hmax_map.end()) {
                        if (s2_c < dist[s2_key]) {
                            pred[s2_key] = s1_key;
                            dist[s2_key] = s2_c;
                            action[s2_key] = i;
                            q.push(std::make_pair(s2_c + hmax_map[s2_key], s2));
                        }
                    } else {
                        pred[s2_key] = s1_key;
                        dist[s2_key] = s2_c;
                        action[s2_key] = i;
                        int s2_h = h_max(s2, p);
                        q.push(std::make_pair(s2_c + s2_h, s2));
                        hmax_map[s2_key] = s2_h;
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
//    fdrRead(&fdr, argv[2]);

    // Implement the search here
    std::vector<int> init(strips.init, strips.init + strips.init_size);
    int hmax_init = h_max(init, strips);
    auto plan = astar_strips(strips);
    std::cout << ";; Cost: " << plan.first << std::endl;
    std::cout << ";; h^max for init: " << hmax_init << std::endl;
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