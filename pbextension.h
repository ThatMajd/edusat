#pragma once
#include <iostream>
#include <algorithm>
#include <iterator>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <set>
#include <string>
#include <sstream>
#include <fstream>
#include <cassert>
#include <ctime>
#include "options.h"
using namespace std;

typedef int Var;
typedef int Lit;
typedef vector<Lit> clause_t;
typedef clause_t::iterator clause_it;
typedef vector<Lit> trail_t;

#define Assert(exp) AssertCheck(exp, __func__, __LINE__)


#define Neg(l) (l & 1)
#define Restart_multiplier 1.1f
#define Restart_lower 100
#define Restart_upper 1000
#define Max_bring_forward 10
#define var_decay 0.99
#define Rescale_threshold 1e100
#define Assignment_file "assignment.txt"

int verbose = 0;
double begin_time;
double timeout = 0.0;


void Abort(string s, int i);

enum class VAR_DEC_HEURISTIC {
	MINISAT
	// add other decision heuristics here. Add an option to choose between them.
 } ;

VAR_DEC_HEURISTIC VarDecHeuristic = VAR_DEC_HEURISTIC::MINISAT;

enum class VAL_DEC_HEURISTIC {
	/* Same as last value. Initially false*/
	PHASESAVING,
	/* Choose literal with highest frequency */
	LITSCORE
} ;

VAL_DEC_HEURISTIC ValDecHeuristic = VAL_DEC_HEURISTIC::PHASESAVING;


unordered_map<string, option*> options = {
	{"v",           new intoption(&verbose, 0, 2, "Verbosity level")},
	{"timeout",     new doubleoption(&timeout, 0.0, 36000.0, "Timeout in seconds")},
	{"valdh",       new intoption((int*)&ValDecHeuristic, 0, 1, "{0: phase-saving, 1: literal-score}")}
};


enum class LitState {
	L_UNSAT,
	L_SAT,
	L_UNASSIGNED
};

enum class VarState {
	V_FALSE,
	V_TRUE,
	V_UNASSIGNED
};

enum class ClauseState {
	C_UNSAT,
	C_SAT,
	C_UNIT,
	C_UNDEF
};

enum class SolverState{
	UNSAT,
	SAT,
	CONFLICT,
	UNDEF,
	TIMEOUT
} ;
/***************** service functions **********************/

#ifdef _MSC_VER
#include <ctime>

static inline double cpuTime(void) {
    return (double)clock() / CLOCKS_PER_SEC; }
#else

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }
#endif

// For production wrap with #ifdef _DEBUG
void AssertCheck(bool cond, string func_name, int line, string msg = "") {
	if (cond) return;
	cout << "Assertion fail" << endl;
	cout << msg << endl;
	cout << func_name << " line " << line << endl;
	exit(1);
}


bool match(ifstream& in, const char* str) {
    for (; *str != '\0'; ++str)
        if (*str != in.get())
            return false;
    return true;
}

unsigned int Abs(int x) { // because the result is compared to an unsigned int. unsigned int are introduced by size() functions, that return size_t, which is defined to be unsigned.
	if (x < 0) return (unsigned int)-x;
	else return (unsigned int)x;
}

unsigned int v2l(int i) { // maps a literal as it appears in the cnf to literal
	if (i < 0) return ((-i) << 1) - 1;
	else return i << 1;
}

Var l2v(Lit l) {
	return (l+1) / 2;
}

Lit negate(Lit l) {
	if (Neg(l)) return l + 1;  // odd
	return l - 1;
}

int l2rl(int l) {
	return Neg(l)? -((l + 1) / 2) : l / 2;
}


/********** classes ******/

class Clause {
	clause_t c;
	int lw,rw; //watches;
public:
	Clause(){};
	void insert(int i) {c.push_back(i);}
	void lw_set(int i) {lw = i; /*assert(lw != rw);*/}
	void rw_set(int i) {rw = i; /*assert(lw != rw);*/}
	clause_t& cl() {return c;}
	int get_lw() {return lw;}
	int get_rw() {return rw;}
	int get_lw_lit() {return c[lw];}
	int get_rw_lit() {return c[rw];}
	int  lit(int i) {return c[i];}
	inline ClauseState next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc);
	size_t size() {return c.size();}
	void reset() { c.clear(); }
	void print() {for (clause_it it = c.begin(); it != c.end(); ++it) {cout << *it << " ";}; }
	void print_real_lits() {
		Lit l;
		cout << "(";
		for (clause_it it = c.begin(); it != c.end(); ++it) {
			l = l2rl(*it);
			cout << l << " ";} cout << ")";
	}
	void print_with_watches() {
		for (clause_it it = c.begin(); it != c.end(); ++it) {
			cout << l2rl(*it);
			int j = distance(c.begin(), it); //also could write "int j = i - c.begin();"  : the '-' operator is overloaded to allow such things. but distance is more standard, as it works on all standard containers.
			if (j == lw) cout << "L";
			if (j == rw) cout << "R";
			cout << " ";
		};
	}
};

class PBClause {
    clause_t literals;       // List of literals (e.g., [1, -2, 3])
    std::vector<int> coefficients; // Coefficients for each literal (e.g., [2, 3, 1])
    int degree;              // Threshold (e.g., 4 for 2x₁ + 3x₂ + x₃ ≥ 4)
    int lw, rw;              // Watched literals (for efficient propagation)

public:
    PBClause() : degree(0) {}

    // Add a literal with its coefficient
    void insert(int lit, int coeff) {
        literals.push_back(lit);
        coefficients.push_back(coeff);
    }

    // Set watched literals
    void lw_set(int i) { lw = i; }
    void rw_set(int i) { rw = i; }

	void print_real_lits() {
    	Lit l;
    	cout << "(";
    	for (clause_it it = literals.begin(); it != literals.end(); ++it) {
    		l = l2rl(*it);
    		cout << l << " ";} cout << ")";
    }

    // Accessors
    clause_t& get_literals() { return literals; }
    std::vector<int>& get_coefficients() { return coefficients; }
    int get_degree() const { return degree; }
	// Setter for degree (threshold)
	void set_degree(int d) { degree = d; }
    int get_lw() const { return lw; }
    int get_rw() const { return rw; }
    int get_lw_lit() const { return literals[lw]; }
    int get_rw_lit() const { return literals[rw]; }
    int lit(int i) const { return literals[i]; }
	void reset() { literals.clear(), coefficients.clear(); }
    size_t size() const { return literals.size(); }

	void sort() {
    	std::vector<std::pair<int, int>> pairs;
    	for (size_t i = 0; i < coefficients.size(); ++i) {
    		pairs.emplace_back(coefficients[i], literals[i]);
    	}

    	// Explicitly define parameter types for lambda function
    	std::sort(pairs.begin(), pairs.end(), [](const std::pair<int, int>& a, const std::pair<int, int>& b) {
			return a.first > b.first; // Sort by coefficient descending
		});

    	for (size_t i = 0; i < pairs.size(); ++i) {
    		coefficients[i] = pairs[i].first;
    		literals[i] = pairs[i].second;
    	}
    }

    // Check if the PB clause is satisfied under a given assignment
    bool is_satisfied(const std::unordered_map<Var, VarState>& assignment) {
        int total = 0;
        for (size_t i = 0; i < literals.size(); ++i) {
            Var v = l2v(literals[i]);
            auto it = assignment.find(v);
            if (it != assignment.end()) {
                bool lit_sign = Neg(literals[i]);
                bool var_assign = (it->second == VarState::V_TRUE);
                if (lit_sign != var_assign) {
                    total += coefficients[i];
                }
            }
        }
        return total >= degree;
    }

    // Propagate assignments to detect conflicts/implied literals
    // Returns:
    // - "conflict" if the constraint is unsatisfiable.
    // - A vector of implied literals if assignments are required.
    // - An empty vector if no implications exist.
    std::pair<std::string, std::vector<Lit>> propagate(
        const std::unordered_map<Var, VarState>& assignment
    ) {
        int current_sum = 0;
        int unassigned_sum = 0;
        std::vector<Lit> unassigned_lits;

        for (size_t i = 0; i < literals.size(); ++i) {
            Var v = l2v(literals[i]);
            auto it = assignment.find(v);
            if (it != assignment.end()) {
                bool lit_sign = Neg(literals[i]);
                bool var_assign = (it->second == VarState::V_TRUE);
                if (lit_sign != var_assign) {
                    current_sum += coefficients[i];
                }
            } else {
                unassigned_sum += coefficients[i];
                unassigned_lits.push_back(literals[i]);
            }
        }

        // Conflict detection
        if (current_sum + unassigned_sum < degree) {
            return std::make_pair("conflict", std::vector<Lit>());
        }

        // Check for implied literals
        std::vector<Lit> implied;
        int threshold = degree - current_sum;
        for (size_t i = 0; i < unassigned_lits.size(); ++i) {
            if (coefficients[i] >= threshold) {
                implied.push_back(unassigned_lits[i]);
            }
        }

        return implied.empty() ? std::make_pair("no_imp", std::vector<Lit>())
                               : std::make_pair("implied", implied);
    }

    // Print the PB clause
    void print() const {
        for (size_t i = 0; i < literals.size(); ++i) {
            std::cout << coefficients[i] << "*" << l2v(literals[i]) << " + ";
        }
        std::cout << ">= " << degree << std::endl;
    }

    // Print with watched literals
    void print_with_watches() const {
        for (size_t i = 0; i < literals.size(); ++i) {
            std::cout << l2rl(literals[i]);
            if (i == lw) std::cout << "L";
            if (i == rw) std::cout << "R";
            std::cout << " ";
        }
        std::cout << ">= " << degree << std::endl;
    }
};

class Solver {
	vector<Clause> cnf; // clause DB.
	vector<int> unaries;
	trail_t trail;  // assignment stack
	vector<int> separators; // indices into trail showing increase in dl
	vector<int> LitScore; // literal => frequency of this literal (# appearances in all clauses).
	vector<vector<int> > watches;  // Lit => vector of clause indices into CNF
	vector<VarState> state;  // current assignment
	vector<VarState> prev_state; // for phase-saving: same as state, only that it is not reset to 0 upon backtracking.
	vector<int> antecedent; // var => clause index in the cnf vector. For variables that their value was assigned in BCP, this is the clause that gave this variable its value.
	vector<bool> marked;	// var => seen during analyze()
	vector<int> dlevel; // var => decision level in which this variable was assigned its value.
	vector<int> conflicts_at_dl; // decision level => # of conflicts under it. Used for local restarts.

	// Used by VAR_DH_MINISAT:
	map<double, unordered_set<Var>, greater<double>> m_Score2Vars; // 'greater' forces an order from large to small of the keys
	map<double, unordered_set<Var>, greater<double>>::iterator m_Score2Vars_it;
	unordered_set<Var>::iterator m_VarsSameScore_it;
	vector<double>	m_activity; // Var => activity
	double			m_var_inc;	// current increment of var score (it increases over time)
	double			m_curr_activity;
	bool			m_should_reset_iterators;

	unsigned int
		nvars,			// # vars
		nclauses, 		// # clauses
		nlits,			// # literals = 2*nvars
		qhead;			// index into trail. Used in BCP() to follow the propagation process.
	int
		num_learned,
		num_decisions,
		num_assignments,
		num_restarts,
		dl,				// decision level
		max_dl,			// max dl seen so far since the last restart
		conflicting_clause_idx, // holds the index of the current conflicting clause in cnf[]. -1 if none.
		restart_threshold,
		restart_lower,
		restart_upper;

	Lit 		asserted_lit;

	float restart_multiplier;

	// access
	int get_learned() { return num_learned; }
	void set_nvars(int x) { nvars = x; }
	int get_nvars() { return nvars; }
	void set_nclauses(int x) { nclauses = x; }
	size_t cnf_size() { return cnf.size(); }
	VarState get_state(int x) { return state[x]; }

	// misc.
	void add_to_trail(int x) { trail.push_back(x); }

	void reset(); // initialization that is invoked initially + every restart
	void initialize();
	void reset_iterators(double activity_key = 0.0);

	// solving
	SolverState decide();
	void test();
	SolverState BCP();
	int  analyze(const Clause);
	inline int  getVal(Var v);
	inline void add_clause(Clause& c, int l, int r);
	inline void add_unary_clause(Lit l);
	inline void assert_lit(Lit l);
	void m_rescaleScores(double& new_score);
	inline void backtrack(int k);
	void restart();

	// scores
	inline void bumpVarScore(int idx);
	inline void bumpLitScore(int lit_idx);

public:
	Solver():
		nvars(0), nclauses(0), num_learned(0), num_decisions(0), num_assignments(0),
		num_restarts(0), m_var_inc(1.0), qhead(0),
		restart_threshold(Restart_lower), restart_lower(Restart_lower),
		restart_upper(Restart_upper), restart_multiplier(Restart_multiplier)	 {};

	// service functions
	inline LitState lit_state(Lit l) {
		VarState var_state = state[l2v(l)];
		return var_state == VarState::V_UNASSIGNED ? LitState::L_UNASSIGNED : (Neg(l) && var_state == VarState::V_FALSE || !Neg(l) && var_state == VarState::V_TRUE) ? LitState::L_SAT : LitState::L_UNSAT;
	}
	inline LitState lit_state(Lit l, VarState var_state) {
		return var_state == VarState::V_UNASSIGNED ? LitState::L_UNASSIGNED : (Neg(l) && var_state == VarState::V_FALSE || !Neg(l) && var_state == VarState::V_TRUE) ? LitState::L_SAT : LitState::L_UNSAT;
	}
	void read_cnf(ifstream& in);

	void read_opb(ifstream& in);

	SolverState _solve();
	void solve();




// debugging
	void print_cnf(){
		for(vector<Clause>::iterator i = cnf.begin(); i != cnf.end(); ++i) {
			i -> print_with_watches();
			cout << endl;
		}
	}

	void print_real_cnf() {
		for(vector<Clause>::iterator i = cnf.begin(); i != cnf.end(); ++i) {
			i -> print_real_lits();
			cout << endl;
		}
	}

	void print_state(const char *file_name) {
		ofstream out;
		out.open(file_name);
		out << "State: ";
		for (vector<VarState>::iterator it = state.begin() + 1; it != state.end(); ++it) {
			char sign = (*it) == VarState::V_FALSE ? -1 : (*it) == VarState::V_TRUE ? 1 : 0;
			out << sign * (it - state.begin()) << " "; out << endl;
		}
	}

	void print_state() {
		cout << "State: ";
		for (vector<VarState>::iterator it = state.begin() + 1; it != state.end(); ++it) {
			char sign = (*it) == VarState::V_FALSE ? -1 : (*it) == VarState::V_TRUE ? 1 : 0;
			cout << sign * (it - state.begin()) << " "; cout << endl;
		}
	}

	void print_watches() {
		for (vector<vector<int> >::iterator it = watches.begin() + 1; it != watches.end(); ++it) {
			cout << distance(watches.begin(), it) << ": ";
			for (vector<int>::iterator it_c = (*it).begin(); it_c != (*it).end(); ++it_c) {
				cnf[*it_c].print();
				cout << "; ";
			}
			cout << endl;
		}
	};


	void print_stats() {cout << endl << "Statistics: " << endl << "===================" << endl <<
		"### Restarts:\t\t" << num_restarts << endl <<
		"### Learned-clauses:\t" << num_learned << endl <<
		"### Decisions:\t\t" << num_decisions << endl <<
		"### Implications:\t" << num_assignments - num_decisions << endl <<
		"### Time:\t\t" << cpuTime() - begin_time << endl;
	}

	void validate_assignment();
};

class PBSolver {
	vector<PBClause> opb; // clause DB.
	// vector<int> unaries; // TODO for the time being I don't think there are unaries here
	trail_t trail;  // assignment stack
	vector<int> separators; // indices into trail showing increase in dl
	vector<int> LitScore; // literal => frequency of this literal (# appearances in all clauses).
	vector<vector<int> > watches;  // Lit => vector of clause indices into CNF
	vector<VarState> state;  // current assignment
	vector<VarState> prev_state; // for phase-saving: same as state, only that it is not reset to 0 upon backtracking.
	vector<int> antecedent; // var => clause index in the cnf vector. For variables that their value was assigned in BCP, this is the clause that gave this variable its value.
	vector<bool> marked;	// var => seen during analyze()
	vector<int> dlevel; // var => decision level in which this variable was assigned its value.
	vector<int> conflicts_at_dl; // decision level => # of conflicts under it. Used for local restarts.

	// Used by VAR_DH_MINISAT:
	map<double, unordered_set<Var>, greater<double>> m_Score2Vars; // 'greater' forces an order from large to small of the keys
	map<double, unordered_set<Var>, greater<double>>::iterator m_Score2Vars_it;
	unordered_set<Var>::iterator m_VarsSameScore_it;
	vector<double>	m_activity; // Var => activity
	double			m_var_inc;	// current increment of var score (it increases over time)
	double			m_curr_activity;
	bool			m_should_reset_iterators;

	unsigned int
		nvars,			// # vars
		nclauses, 		// # clauses
		nlits,			// # literals = 2*nvars
		qhead;			// index into trail. Used in BCP() to follow the propagation process.
	int
		num_learned,
		num_decisions,
		num_assignments,
		num_restarts,
		dl,				// decision level
		max_dl,			// max dl seen so far since the last restart
		conflicting_clause_idx, // holds the index of the current conflicting clause in cnf[]. -1 if none.
		restart_threshold,
		restart_lower,
		restart_upper;

	Lit 		asserted_lit;

	float restart_multiplier;

	// access
	int get_learned() { return num_learned; }
	void set_nvars(int x) { nvars = x; }
	int get_nvars() { return nvars; }
	void set_nclauses(int x) { nclauses = x; }
	size_t get_size() { return opb.size(); }
	VarState get_state(int x) { return state[x]; }

	// misc.
	void add_to_trail(int x) { trail.push_back(x); }

	void reset(); // initialization that is invoked initially + every restart
	void initialize();
	void reset_iterators(double activity_key = 0.0);

	// solving
	SolverState decide();
	void test();
	SolverState BCP();
	int  analyze(const Clause);
	inline int  getVal(Var v);
	inline void add_clause(PBClause &c, int l, int r);
	inline void add_unary_clause(Lit l);
	inline void assert_lit(Lit l);
	void m_rescaleScores(double& new_score);
	inline void backtrack(int k);
	void restart();

	// scores
	inline void bumpVarScore(int idx);
	inline void bumpLitScore(int lit_idx);

public:
	PBSolver():
		nvars(0), nclauses(0), num_learned(0), num_decisions(0), num_assignments(0),
		num_restarts(0), m_var_inc(1.0), qhead(0),
		restart_threshold(Restart_lower), restart_lower(Restart_lower),
		restart_upper(Restart_upper), restart_multiplier(Restart_multiplier)	 {};

	// service functions
	inline LitState lit_state(Lit l) {
		VarState var_state = state[l2v(l)];
		return var_state == VarState::V_UNASSIGNED ? LitState::L_UNASSIGNED : (Neg(l) && var_state == VarState::V_FALSE || !Neg(l) && var_state == VarState::V_TRUE) ? LitState::L_SAT : LitState::L_UNSAT;
	}
	inline LitState lit_state(Lit l, VarState var_state) {
		return var_state == VarState::V_UNASSIGNED ? LitState::L_UNASSIGNED : (Neg(l) && var_state == VarState::V_FALSE || !Neg(l) && var_state == VarState::V_TRUE) ? LitState::L_SAT : LitState::L_UNSAT;
	}
	void read_cnf(ifstream& in);

	void read_opb(ifstream& in);

	SolverState _solve();
	void solve();




// debugging
	void print_cnf(){
		for(vector<PBClause>::iterator i = opb.begin(); i != opb.end(); ++i) {
			i -> print_with_watches();
			cout << endl;
		}
	}

	void print_real_cnf() {
		for(vector<PBClause>::iterator i = opb.begin(); i != opb.end(); ++i) {
			i -> print_real_lits();
			cout << endl;
		}
	}

	void print_state(const char *file_name) {
		ofstream out;
		out.open(file_name);
		out << "State: ";
		for (vector<VarState>::iterator it = state.begin() + 1; it != state.end(); ++it) {
			char sign = (*it) == VarState::V_FALSE ? -1 : (*it) == VarState::V_TRUE ? 1 : 0;
			out << sign * (it - state.begin()) << " "; out << endl;
		}
	}

	void print_state() {
		cout << "State: ";
		for (vector<VarState>::iterator it = state.begin() + 1; it != state.end(); ++it) {
			char sign = (*it) == VarState::V_FALSE ? -1 : (*it) == VarState::V_TRUE ? 1 : 0;
			cout << sign * (it - state.begin()) << " "; cout << endl;
		}
	}

	void print_watches() {
		for (vector<vector<int> >::iterator it = watches.begin() + 1; it != watches.end(); ++it) {
			cout << distance(watches.begin(), it) << ": ";
			for (vector<int>::iterator it_c = (*it).begin(); it_c != (*it).end(); ++it_c) {
				opb[*it_c].print();
				cout << "; ";
			}
			cout << endl;
		}
	};


	void print_stats() {cout << endl << "Statistics: " << endl << "===================" << endl <<
		"### Restarts:\t\t" << num_restarts << endl <<
		"### Learned-clauses:\t" << num_learned << endl <<
		"### Decisions:\t\t" << num_decisions << endl <<
		"### Implications:\t" << num_assignments - num_decisions << endl <<
		"### Time:\t\t" << cpuTime() - begin_time << endl;
	}

	void validate_assignment();
};

