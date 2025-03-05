// #include "edusat.h"
#include "pbextension.h"

Solver S;
PBSolver PB_S;

vector<Lit> decisions;

using namespace std;

inline bool verbose_now() {
	return verbose > 1;
}




/******************  Reading the CNF ******************************/
#pragma region readCNF
void skipLine(ifstream& in) {
	for (;;) {
		//if (in.get() == EOF || in.get() == '\0') return;
		if (in.get() == '\n') { return; }
	}
}

static void skipWhitespace(ifstream& in, char&c) {
	c = in.get();
	while ((c >= 9 && c <= 13) || c == 32)
		c = in.get();
}

static int parseInt(ifstream& in) {
	int     val = 0;
	bool    neg = false;
	char c;
	skipWhitespace(in, c);
	if (c == '-') neg = true, c = in.get();
	if (c < '0' || c > '9') cout << c, Abort("Unexpected char in input", 1);
	while (c >= '0' && c <= '9')
		val = val * 10 + (c - '0'),
		c = in.get();
	return neg ? -val : val;
}

void Solver::read_cnf(ifstream& in) {
	int i;
	unsigned int vars, clauses, unary = 0;
	set<Lit> s;
	Clause c;


	while (in.peek() == 'c') skipLine(in);

	if (!match(in, "p cnf")) Abort("Expecting `p cnf' in the beginning of the input file", 1);
	in >> vars; // since vars is int, it reads int from the stream.
	in >> clauses;
	if (!vars || !clauses) Abort("Expecting non-zero variables and clauses", 1);
	cout << "vars: " << vars << " clauses: " << clauses << endl;
	cnf.reserve(clauses);

	set_nvars(vars);
	set_nclauses(clauses);
	initialize();

	while (in.good() && in.peek() != EOF) {
		i = parseInt(in);


		string line;
		getline(in, line);
		cout << "Processing line: " << line << endl;  // Print the current line


		if (i == 0) {
			c.cl().resize(s.size());
			copy(s.begin(), s.end(), c.cl().begin());
			switch (c.size()) {
			case 0: {
				stringstream num;  // this allows to convert int to string
				num << cnf_size() + 1; // converting int to string.
				Abort("Empty clause not allowed in input formula (clause " + num.str() + ")", 1); // concatenating strings
			}
			case 1: {
				Lit l = c.cl()[0];
				// checking if we have conflicting unaries. Sufficiently rare to check it here rather than
				// add a check in BCP.
				if (state[l2v(l)] != VarState::V_UNASSIGNED)
					if (Neg(l) != (state[l2v(l)] == VarState::V_FALSE)) {
						S.print_stats();
						Abort("UNSAT (conflicting unaries for var " + to_string(l2v(l)) +")", 0);
					}
				assert_lit(l);
				add_unary_clause(l);
				break; // unary clause. Note we do not add it as a clause.
			}
			default: add_clause(c, 0, 1);
			}
			c.reset();
			s.clear();
			continue;
		}
		if (Abs(i) > vars) Abort("Literal index larger than declared on the first line", 1);
		if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(abs(i));
		i = v2l(i);
		if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(i);
		s.insert(i);
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
	cout << "Read " << cnf_size() << " clauses in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
}


// void PBSolver::read_opb(std::ifstream& in) {
//     std::string line;
//
// 	int left_sum = 0;
//
// 	// TODO this code is temporary and should be changed to parse from the input file
// 	int vars = 3;
// 	int clauses = 2;
// 	cout << "vars: " << vars << " clauses: " << clauses << endl;
// 	opb.reserve(clauses);
//
// 	set_nvars(vars);
// 	set_nclauses(clauses);
// 	initialize();
//
//     while (std::getline(in, line)) {
//         // Skip comments and empty lines
//         if (line.empty() || line[0] == '*') {
//             continue;
//         }
//
//         // Check for objective function (optional)
//         if (line.substr(0, 4) == "min:") {
//             std::cout << "Objective function: " << line << std::endl;
//             continue;
//         }
//
//         // Process constraint line
//         PBClause pb;
//         std::vector<std::string> tokens;
//         std::istringstream iss(line);
//         std::string token;
//
//         // Split line into tokens
//         while (iss >> token) {
//             tokens.push_back(token);
//         }
//
//         size_t i = 0;
//         bool has_terms = false;
//
//         // Process terms (coefficient and variable pairs)
//         while (i < tokens.size()) {
//             if (tokens[i] == ">=" || tokens[i] == "<=" || tokens[i] == "=") {
//                 // Parse relational operator and RHS
//                 if (i + 1 < tokens.size()) {
//                     try {
//                         int rhs = std::stoi(tokens[i + 1]);
//
//                     	// this will be constant >=
//                         // pb.setComparator(tokens[i]);
//
//                     	// left_sum used to normalize the constraint by making all coeff non-negative
//                         pb.set_degree(rhs + left_sum);
//
// 						add_clause(pb, 0, 1);
//                     } catch (const std::exception& e) {
//                         std::cerr << "Error parsing RHS: " << tokens[i + 1] << std::endl;
//                     }
//                 }
//                 break; // End of constraint
//             }
//
//             // Ensure there are enough tokens for a term (coeff + var)
//             if (i + 1 >= tokens.size()) {
//                 std::cerr << "Incomplete term in constraint: " << line << std::endl;
//                 break;
//             }
//
//             const std::string& coeff_str = tokens[i];
//             const std::string& var_str = tokens[i + 1];
//
//             try {
//                 // Parse coefficient & literal
//                 int coeff = std::stoi(coeff_str);
//             	int raw_lit = std::stoi(var_str.substr(1));
//
//             	if (coeff < 0) {
//             		left_sum += -coeff;
//             		raw_lit = -raw_lit;
//             		coeff = -coeff;
//             	}
//
//                 // Parse variable (format: xN)
//                 if (var_str.empty() || var_str[0] != 'x') {
//                     throw std::runtime_error("Invalid variable: " + var_str);
//                 }
//
//                 int lit = v2l(raw_lit);
//
//                 // Add to PBClause
//                 pb.insert(lit, coeff);
//                 has_terms = true;
//             } catch (const std::exception& e) {
//                 std::cerr << "Error parsing term '" << coeff_str << " " << var_str
//                           << "': " << e.what() << std::endl;
//             }
//
//             i += 2; // Move to next term
//         }
//
//         if (has_terms) {
//             // Add the constraint to the solver
//             // (e.g., addConstraint(pb);)
//             std::cout << "Parsed constraint: ";
//         	pb.sort();
//             pb.print(); // For debugging
//         }
//     }
// 	cout << "Read " << get_size() << " clauses in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
// }

void PBSolver::read_opb(std::ifstream& in) {
	int vars, clauses;

	// First line we extract variables and clauses
	if (!match(in, "* #variable=")) Abort("Expecting `*' in the input file", 1);
	in >> vars;
	if (!match(in, " #constraint=")) Abort("No constraints provided", 1);
	in >> clauses;

	cout << "vars: " << vars << " clauses: " << clauses << endl;
	opb.reserve(clauses);

	set_nvars(vars);
	set_nclauses(clauses);
	initialize();

	// Keep moving until we find constraints
	while (in.good() && in.peek() != '*') in.get();
	while (in.good() && in.peek() == '*') skipLine(in);

	// Read process the constraints
	std::string token1, token2;
	int coef, lit, rhs;
	int normalization_sum = 0;

	PBClause pb;

	while (in.good() && in.peek() != EOF) {
		in >> token1 >> token2;
		// cout << token1 << token2 << endl;
		if (token1 == ">=" || token2 == "=" || token1 == "<=") {
			// end of constraint
			if (token1 != ">=") Abort("only >= is supported", 1);
			rhs = std::stoi(token2);
			pb.set_degree(rhs + normalization_sum);
			pb.sort();
			add_clause(pb, 0, 1);
			pb.print_real_lits();
			pb.reset();

		} else {
			coef = std::stoi(token1);
			lit = std::stoi(token2.substr(1));

			if (lit > vars) Abort("Literal index larger than declared on the first line", 1);
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(lit);

			if (coef < 0) {
				normalization_sum += -coef;
				lit = -lit;
				coef = -coef;
			}
			pb.insert(v2l(lit), coef);

			if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(v2l(lit));
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
	cout << "Read " << get_size() << " clauses in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
}
#pragma endregion readCNF

/******************  Solving ******************************/
#pragma region solving
void Solver::reset() { // invoked initially + every restart
	dl = 0;
	max_dl = 0;
	conflicting_clause_idx = -1;	
	separators.push_back(0); // we want separators[1] to match dl=1. separators[0] is not used.
	conflicts_at_dl.push_back(0);
}

void PBSolver::reset() { // invoked initially + every restart
	dl = 0;
	max_dl = 0;
	conflicting_clause_idx = -1;
	separators.push_back(0); // we want separators[1] to match dl=1. separators[0] is not used.
	conflicts_at_dl.push_back(0);
}

inline void Solver::reset_iterators(double where) {
	m_Score2Vars_it = (where == 0) ? m_Score2Vars.begin() : m_Score2Vars.lower_bound(where);
	Assert(m_Score2Vars_it != m_Score2Vars.end());
	m_VarsSameScore_it = m_Score2Vars_it->second.begin();
	m_should_reset_iterators = false;
}

inline void PBSolver::reset_iterators(double where) {
	m_Score2Vars_it = (where == 0) ? m_Score2Vars.begin() : m_Score2Vars.lower_bound(where);
	Assert(m_Score2Vars_it != m_Score2Vars.end());
	m_VarsSameScore_it = m_Score2Vars_it->second.begin();
	m_should_reset_iterators = false;
}

void Solver::initialize() {	
	
	state.resize(nvars + 1, VarState::V_UNASSIGNED);
	prev_state.resize(nvars + 1, VarState::V_FALSE); // we set initial assignment with phase-saving to false. 
	antecedent.resize(nvars + 1, -1);	
	marked.resize(nvars+1);
	dlevel.resize(nvars+1);
	
	nlits = 2 * nvars;
	watches.resize(nlits + 1);
	LitScore.resize(nlits + 1);
	//initialize scores 	
	m_activity.resize(nvars + 1);	
	m_curr_activity = 0.0f;
	for (unsigned int v = 0; v <= nvars; ++v) {			
		m_activity[v] = 0;		
	}
	reset();
}

void PBSolver::initialize() {
	state.resize(nvars + 1, VarState::V_UNASSIGNED);
	prev_state.resize(nvars + 1, VarState::V_FALSE); // we set initial assignment with phase-saving to false.
	antecedent.resize(nvars + 1, -1);
	marked.resize(nvars+1);
	dlevel.resize(nvars+1);

	nlits = 2 * nvars;
	watches.resize(nlits + 1);
	LitScore.resize(nlits + 1);
	//initialize scores
	m_activity.resize(nvars + 1);
	m_curr_activity = 0.0f;
	for (unsigned int v = 0; v <= nvars; ++v) {
		m_activity[v] = 0;
	}
	reset();
}

inline void Solver::assert_lit(Lit l) {
	trail.push_back(l);
	int var = l2v(l);
	if (Neg(l)) prev_state[var] = state[var] = VarState::V_FALSE; else prev_state[var] = state[var] = VarState::V_TRUE;
	dlevel[var] = dl;
	++num_assignments;
	if (verbose_now()) cout << l2rl(l) <<  " @ " << dl << endl;
}

inline void PBSolver::assert_lit(Lit l) {
	trail.push_back(l);
	int var = l2v(l);
	if (Neg(l)) prev_state[var] = state[var] = VarState::V_FALSE; else prev_state[var] = state[var] = VarState::V_TRUE;
	dlevel[var] = dl;
	++num_assignments;
	if (verbose_now()) cout << l2rl(l) <<  " @ " << dl << endl;
}

void Solver::m_rescaleScores(double& new_score) {
	if (verbose_now()) cout << "Rescale" << endl;
	new_score /= Rescale_threshold;
	for (unsigned int i = 1; i <= nvars; i++)
		m_activity[i] /= Rescale_threshold;
	m_var_inc /= Rescale_threshold;
	// rebuilding the scaled-down m_Score2Vars.
	map<double, unordered_set<Var>, greater<double>> tmp_map;
	double prev_score = 0.0f;
	for (auto m : m_Score2Vars) {
		double scaled_score = m.first / Rescale_threshold;
		if (scaled_score == prev_score) // This can happen due to rounding
			tmp_map[scaled_score].insert(m_Score2Vars[m.first].begin(), m_Score2Vars[m.first].end());
		else
			tmp_map[scaled_score] = m_Score2Vars[m.first];
		prev_score = scaled_score;
	}
	tmp_map.swap(m_Score2Vars);
}

void PBSolver::m_rescaleScores(double& new_score) {
	if (verbose_now()) cout << "Rescale" << endl;
	new_score /= Rescale_threshold;
	for (unsigned int i = 1; i <= nvars; i++)
		m_activity[i] /= Rescale_threshold;
	m_var_inc /= Rescale_threshold;
	// rebuilding the scaled-down m_Score2Vars.
	map<double, unordered_set<Var>, greater<double>> tmp_map;
	double prev_score = 0.0f;
	for (auto m : m_Score2Vars) {
		double scaled_score = m.first / Rescale_threshold;
		if (scaled_score == prev_score) // This can happen due to rounding
			tmp_map[scaled_score].insert(m_Score2Vars[m.first].begin(), m_Score2Vars[m.first].end());
		else
			tmp_map[scaled_score] = m_Score2Vars[m.first];
		prev_score = scaled_score;
	}
	tmp_map.swap(m_Score2Vars);
}

void Solver::bumpVarScore(int var_idx) {
	double new_score;
	double score = m_activity[var_idx];		

	if (score > 0) {
		Assert(m_Score2Vars.find(score) != m_Score2Vars.end());
		m_Score2Vars[score].erase(var_idx);
		if (m_Score2Vars[score].size() == 0) m_Score2Vars.erase(score);
	}
	new_score = score + m_var_inc;
	m_activity[var_idx] = new_score;

	// Rescaling, to avoid overflows; 
	if (new_score > Rescale_threshold) {
		m_rescaleScores(new_score);
	}

	if (m_Score2Vars.find(new_score) != m_Score2Vars.end())
		m_Score2Vars[new_score].insert(var_idx);
	else
		m_Score2Vars[new_score] = unordered_set<int>({ var_idx });
}

void PBSolver::bumpVarScore(int var_idx) {
	double new_score;
	double score = m_activity[var_idx];

	if (score > 0) {
		Assert(m_Score2Vars.find(score) != m_Score2Vars.end());
		m_Score2Vars[score].erase(var_idx);
		if (m_Score2Vars[score].size() == 0) m_Score2Vars.erase(score);
	}
	new_score = score + m_var_inc;
	m_activity[var_idx] = new_score;

	// Rescaling, to avoid overflows;
	if (new_score > Rescale_threshold) {
		m_rescaleScores(new_score);
	}

	if (m_Score2Vars.find(new_score) != m_Score2Vars.end())
		m_Score2Vars[new_score].insert(var_idx);
	else
		m_Score2Vars[new_score] = unordered_set<int>({ var_idx });
}

void Solver::bumpLitScore(int lit_idx) {
	LitScore[lit_idx]++;
}

void PBSolver::bumpLitScore(int lit_idx) {
	LitScore[lit_idx]++;
}

void Solver::add_clause(Clause& c, int l, int r) {
	Assert(c.size() > 1) ;
	c.lw_set(l);
	c.rw_set(r);
	int loc = static_cast<int>(cnf.size());  // the first is in location 0 in cnf
	int size = c.size();

	watches[c.lit(l)].push_back(loc);
	watches[c.lit(r)].push_back(loc);
	cnf.push_back(c);
}

void PBSolver::add_clause(PBClause& c, int l, int r) {
	// Assert(c.size() > 1) ;
	//
	int loc = static_cast<int>(opb.size());
	for (auto watch: c.init_watches() ) {
		watches[c.lit(watch)].push_back(loc);
	}
	opb.push_back(c);
}

void Solver::add_unary_clause(Lit l) {		
	unaries.push_back(l);
}

int Solver :: getVal(Var v) {
	switch (ValDecHeuristic) {
	case VAL_DEC_HEURISTIC::PHASESAVING: {
		VarState saved_phase = prev_state[v];		
		switch (saved_phase) {
		case VarState::V_FALSE:	return v2l(-v);
		case VarState::V_TRUE: return v2l(v);
		default: Assert(0);
		}
	}
	case VAL_DEC_HEURISTIC::LITSCORE:
	{
		int litp = v2l(v), litn = v2l(-v);
		int pScore = LitScore[litp], nScore = LitScore[litn];
		return pScore > nScore ? litp : litn;
	}
	default: Assert(0);
	}	
	return 0;
}

int PBSolver :: getVal(Var v) {
	switch (ValDecHeuristic) {
		case VAL_DEC_HEURISTIC::PHASESAVING: {
			VarState saved_phase = prev_state[v];
			switch (saved_phase) {
				case VarState::V_FALSE:	return v2l(-v);
				case VarState::V_TRUE: return v2l(v);
				default: Assert(0);
			}
		}
		case VAL_DEC_HEURISTIC::LITSCORE:
		{
			int litp = v2l(v), litn = v2l(-v);
			int pScore = LitScore[litp], nScore = LitScore[litn];
			return pScore > nScore ? litp : litn;
		}
		default: Assert(0);
	}
	return 0;
}

SolverState Solver::decide(){
	if (verbose_now()) cout << "decide" << endl;
	Lit best_lit = 0;	
	int max_score = 0;
	Var bestVar = 0;
	switch (VarDecHeuristic) {

	case  VAR_DEC_HEURISTIC::MINISAT: {
		// m_Score2Vars_r_it and m_VarsSameScore_it are fields.
		// When we get here they are the location where we need to start looking.
		if (m_should_reset_iterators) reset_iterators(m_curr_activity);
		Var v = 0;
		int cnt = 0;
		if (m_Score2Vars_it == m_Score2Vars.end()) break;
		while (true) { // scores from high to low
			while (m_VarsSameScore_it != m_Score2Vars_it->second.end()) {
				v = *m_VarsSameScore_it;
				++m_VarsSameScore_it;
				++cnt;
				if (state[v] == VarState::V_UNASSIGNED) { // found a var to assign
					m_curr_activity = m_Score2Vars_it->first;
					assert(m_curr_activity == m_activity[v]);
					best_lit = getVal(v);
					goto Apply_decision;
				}
			}
			++m_Score2Vars_it;
			if (m_Score2Vars_it == m_Score2Vars.end()) break;
			m_VarsSameScore_it = m_Score2Vars_it->second.begin();
		}
		break;
	}
	default: Assert(0);
	}
		
	assert(!best_lit);
	S.print_state(Assignment_file);
	return SolverState::SAT;


Apply_decision:	
	dl++; // increase decision level
	if (dl > max_dl) {
		max_dl = dl;
		separators.push_back(trail.size());
		conflicts_at_dl.push_back(num_learned);
	}
	else {
		separators[dl] = trail.size();
		conflicts_at_dl[dl] = num_learned;
	}
	
	assert_lit(best_lit);
	++num_decisions;	
	return SolverState::UNDEF;
}

SolverState PBSolver::decide(){
	if (verbose_now()) cout << "decide" << endl;
	Lit best_lit = 0;
	int max_score = 0;
	Var bestVar = 0;


	best_lit = decisions.back();
	decisions.pop_back();
	goto Apply_decision;

	// for (int i = 1; i < state.size(); i++) {
	// 	if (state[i] == VarState::V_UNASSIGNED) {
	// 		best_lit = i;
	// 		goto  Apply_decision;
	// 	}
	// }

	// switch (VarDecHeuristic) {
	//
	// 	case  VAR_DEC_HEURISTIC::MINISAT: {
	// 		// m_Score2Vars_r_it and m_VarsSameScore_it are fields.
	// 		// When we get here they are the location where we need to start looking.
	// 		if (m_should_reset_iterators) reset_iterators(m_curr_activity);
	// 		Var v = 0;
	// 		int cnt = 0;
	// 		if (m_Score2Vars_it == m_Score2Vars.end()) break;
	// 		while (true) { // scores from high to low
	// 			while (m_VarsSameScore_it != m_Score2Vars_it->second.end()) {
	// 				v = *m_VarsSameScore_it;
	// 				++m_VarsSameScore_it;
	// 				++cnt;
	// 				if (state[v] == VarState::V_UNASSIGNED) { // found a var to assign
	// 					m_curr_activity = m_Score2Vars_it->first;
	// 					assert(m_curr_activity == m_activity[v]);
	// 					best_lit = getVal(v);
	// 					goto Apply_decision;
	// 				}
	// 			}
	// 			++m_Score2Vars_it;
	// 			if (m_Score2Vars_it == m_Score2Vars.end()) break;
	// 			m_VarsSameScore_it = m_Score2Vars_it->second.begin();
	// 		}
	// 		break;
	// 	}
	// 	default: Assert(0);
	// }

	assert(!best_lit);
	PB_S.print_state(Assignment_file);
	return SolverState::SAT;


	Apply_decision:
		dl++; // increase decision level
	if (dl > max_dl) {
		max_dl = dl;
		separators.push_back(trail.size());
		conflicts_at_dl.push_back(num_learned);
	}
	else {
		separators[dl] = trail.size();
		conflicts_at_dl[dl] = num_learned;
	}

	assert_lit(best_lit);
	++num_decisions;
	return SolverState::UNDEF;
}

inline ClauseState Clause::next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc) {
	if (verbose_now()) cout << "next_not_false" << endl;
	
	if (!binary)
		for (vector<int>::iterator it = c.begin(); it != c.end(); ++it) {
			LitState LitState = S.lit_state(*it);
			if (LitState != LitState::L_UNSAT && *it != other_watch) { // found another watch_lit
				loc = distance(c.begin(), it);
				if (is_left_watch) lw = loc;    // if literal was the left one 
				else rw = loc;				
				return ClauseState::C_UNDEF;
			}
		}
	switch (S.lit_state(other_watch)) {
	case LitState::L_UNSAT: // conflict
		if (verbose_now()) { print_real_lits(); cout << " is conflicting" << endl; }
		return ClauseState::C_UNSAT;
	case LitState::L_UNASSIGNED: return ClauseState::C_UNIT; // unit clause. Should assert the other watch_lit.	
	case LitState::L_SAT: return ClauseState::C_SAT; // other literal is satisfied. 
	default: Assert(0); return ClauseState::C_UNDEF; // just to supress warning. 
	}
}

inline PBClauseState PBClause::next_not_false(Lit assigned_lit) {
	if (verbose_now()) cout << "next_not_false" << endl;

	int assigned_idx = l2idx(assigned_lit);

	Assert(assigned_idx >= 0);
	watches.erase(watches.begin() + assigned_idx);
	update_sum(assigned_lit);

	std:: vector<int> unwatched;

	for (size_t i = 0, w=0; i < literals.size(); ++i) {
		if (i == watches[w]) {
			w++;
		}
		else {
			if (PB_S.lit_state(literals[i]) != LitState::L_UNSAT) {
				unwatched.push_back(i);
			}
		}
	}

	int a_max = max(coefficients[watches.front()], coefficients[unwatched.front()]);

	while (watched_sum < degree + a_max) {
		// since the constraint is sorted watches and unwatched are also sorted
		int a_s = coefficients[unwatched.front()];
		watched_sum += a_s;
		watches.push_back(unwatched.front());

		unwatched.erase(unwatched.begin());
	}
	if (watched_sum < degree)
		return  PBClauseState::PB_UNSAT;
}

void Solver::test() { // tests that each clause is watched twice. 	
	for (unsigned int idx = 0; idx < cnf.size(); ++idx) {
		Clause c = cnf[idx];
		bool found = false;
		for (int zo = 0; zo <= 1; ++zo) {
			for (vector<int>::iterator it = watches[c.cl()[zo]].begin(); !found && it != watches[c.cl()[zo]].end(); ++it) {				
				if (*it == idx) {
					found = true;
					break;
				}
			}
		}
		if (!found) {
			cout << "idx = " << idx << endl;
			c.print();
			cout << endl;
			cout << c.size();
		}
		Assert(found);
	}
}

SolverState Solver::BCP() {
	if (verbose_now()) cout << "BCP" << endl;
	if (verbose_now()) cout << "qhead = " << qhead << " trail-size = " << trail.size() << endl;
	while (qhead < trail.size()) {
		Lit NegatedLit = ::negate(trail[qhead++]);
		Assert(lit_state(NegatedLit) == LitState::L_UNSAT);
		if (verbose_now()) cout << "propagating " << l2rl(::negate(NegatedLit)) << endl;


		vector<int> new_watch_list; // The original watch list minus those clauses that changed a watch. The order is maintained.
		int new_watch_list_idx = watches[NegatedLit].size() - 1; // Since we are traversing the watch_list backwards, this index goes down.
		new_watch_list.resize(watches[NegatedLit].size());
		for (vector<int>::reverse_iterator it = watches[NegatedLit].rbegin(); it != watches[NegatedLit].rend() && conflicting_clause_idx < 0; ++it) {
			Clause& c = cnf[*it];
			Lit l_watch = c.get_lw_lit(),
				r_watch = c.get_rw_lit();
			bool binary = c.size() == 2;
			bool is_left_watch = (l_watch == NegatedLit);
			Lit other_watch = is_left_watch? r_watch: l_watch;
			int NewWatchLocation;
			ClauseState res = c.next_not_false(is_left_watch, other_watch, binary, NewWatchLocation);
			if (res != ClauseState::C_UNDEF) new_watch_list[new_watch_list_idx--] = *it; //in all cases but the move-watch_lit case we leave watch_lit where it is
			switch (res) {
			case ClauseState::C_UNSAT: { // conflict
				if (verbose_now()) print_state();
				if (dl == 0) return SolverState::UNSAT;
				conflicting_clause_idx = *it;  // this will also break the loop
				 int dist = distance(it, watches[NegatedLit].rend()) - 1; // # of entries in watches[NegatedLit] that were not yet processed when we hit this conflict.
				// Copying the remaining watched clauses:
				for (int i = dist - 1; i >= 0; i--) {
					new_watch_list[new_watch_list_idx--] = watches[NegatedLit][i];
				}
				if (verbose_now()) cout << "conflict" << endl;
				break;
			}
			case ClauseState::C_SAT:
				if (verbose_now()) cout << "clause is sat" << endl;
				break; // nothing to do when clause has a satisfied literal.
			case ClauseState::C_UNIT: { // new implication
				if (verbose_now()) cout << "propagating: ";
				assert_lit(other_watch);
				antecedent[l2v(other_watch)] = *it;
				if (verbose_now()) cout << "new implication <- " << l2rl(other_watch) << endl;
				break;
			}
			default: // replacing watch_lit
				Assert(NewWatchLocation < static_cast<int>(c.size()));
				int new_lit = c.lit(NewWatchLocation);
				watches[new_lit].push_back(*it);
				if (verbose_now()) { c.print_real_lits(); cout << " now watched by " << l2rl(new_lit) << endl;}
			}
		}
		// resetting the list of clauses watched by this literal.
		watches[NegatedLit].clear();
		new_watch_list_idx++; // just because of the redundant '--' at the end.
		watches[NegatedLit].insert(watches[NegatedLit].begin(), new_watch_list.begin() + new_watch_list_idx, new_watch_list.end());

		//print_watches();
		if (conflicting_clause_idx >= 0) return SolverState::CONFLICT;
		new_watch_list.clear();
	}
	return SolverState::UNDEF;
}

SolverState PBSolver::BCP() {
    if (verbose_now()) cout << "BCP" << endl;
    if (verbose_now()) cout << "qhead = " << qhead << " trail-size = " << trail.size() << endl;
    while (qhead < trail.size()) {
        Lit NegatedLit = ::negate(trail[qhead++]);
        Assert(lit_state(NegatedLit) == LitState::L_UNSAT);
        if (verbose_now()) cout << "propagating " << l2rl(::negate(NegatedLit)) << endl;

        vector<int> new_watch_list;
        int new_watch_list_idx = watches[NegatedLit].size() - 1;
        new_watch_list.resize(watches[NegatedLit].size());

        // Process all PB constraints that watch NegatedLit.
        for (auto it = watches[NegatedLit].rbegin(); it != watches[NegatedLit].rend() && conflicting_clause_idx < 0; ++it) {
        	PBClause& c = opb[*it]; // Use the PB clause database.

        	PBClauseState res = c.next_not_false(NegatedLit);
            if (res != PBClauseState::PB_UNDEF)
                new_watch_list[new_watch_list_idx--] = *it;

            switch (res) {
            case PBClauseState::PB_UNSAT: {
                if (verbose_now()) print_state();
                if (dl == 0) return SolverState::UNSAT;
                conflicting_clause_idx = *it;
                int dist = distance(it, watches[NegatedLit].rend()) - 1;
                for (int i = dist - 1; i >= 0; i--) {
                    new_watch_list[new_watch_list_idx--] = watches[NegatedLit][i];
                }
                if (verbose_now()) cout << "conflict" << endl;
                break;
            }
            case PBClauseState::PB_SAT:
                if (verbose_now()) cout << "PB constraint is satisfied" << endl;
                break;
            case PBClauseState::PB_UNIT: { // new implication
                if (verbose_now()) cout << "propagating: ";
            	// Recompute the sums over the clause.
            	int S_val = 0;  // Sum of coefficients for literals assigned true.
            	int nonFalsifiedSum = 0;  // Sum for literals not falsified (true or unassigned).
            	for (size_t i = 0; i < c.size(); i++) {
            		LitState ls = PB_S.lit_state(c.get_literals()[i]);
            		if (ls == LitState::L_SAT) {
            			S_val += c.get_coefficients()[i];
            			nonFalsifiedSum += c.get_coefficients()[i];
            		} else if (ls == LitState::L_UNASSIGNED) {
            			nonFalsifiedSum += c.get_coefficients()[i];
            		}
            		// If a literal is false, it contributes 0.
            	}

            	// Compute slack: the amount by which the non-falsified sum exceeds the threshold.
            	int slack = nonFalsifiedSum - c.get_degree();

            	// Propagate every unassigned literal whose coefficient exceeds the slack.
            	for (size_t i = 0; i < c.size(); i++) {
            		if (PB_S.lit_state(c.get_literals()[i]) == LitState::L_UNASSIGNED && c.get_coefficients()[i] > slack) {
            			if (verbose_now()) cout << l2rl(c.get_literals()[i]) << " ";
            			assert_lit(c.get_literals()[i]);  // Propagate this literal.
            			antecedent[l2v(c.get_literals()[i])] = *it;  // Record the implication.
            		}
            	}

                // assert_lit(other_watch);
                // antecedent[l2v(other_watch)] = *it;
                // if (verbose_now()) cout << "new implication <- " << l2rl(other_watch) << endl;
                break;
            }
            case PBClauseState::PB_WATCH_UPDATE: {
	            // Update the watch: move the watch from NegatedLit to a new literal.
            	// Assert(NewWatchLocation < static_cast<int>(c.size()));
            	// int new_lit = c.lit(NewWatchLocation);
            	// watches[new_lit].push_back(*it);
            	// if (verbose_now()) {
            	// 	c.print_real_lits();
            	// 	cout << " now watched by " << l2rl(new_lit) << endl;
            	// }
            	break;
            }
            default:
                break;
            }
        }
        // Reset the watch list for NegatedLit.
        watches[NegatedLit].clear();
        new_watch_list_idx++; // adjust for the final decrement.
        watches[NegatedLit].insert(watches[NegatedLit].begin(),
                                    new_watch_list.begin() + new_watch_list_idx,
                                    new_watch_list.end());
        if (conflicting_clause_idx >= 0)
            return SolverState::CONFLICT;
    }
    return SolverState::UNDEF;
}

/*******************************************************************************************************************
name: analyze
input:	1) conflicting clause
		2) dlevel
		3) marked
		
assumes: 1) no clause should have the same literal twice. To guarantee this we read through a set in read_cnf. 
            Wihtout this assumption it may loop forever because we may remove only one copy of the pivot.

This is Alg. 1 from "HaifaSat: a SAT solver based on an Abstraction/Refinement model" 
********************************************************************************************************************/

int Solver::analyze(const Clause conflicting) {
	if (verbose_now()) cout << "analyze" << endl;
	Clause	current_clause = conflicting, 
			new_clause;
	int resolve_num = 0,
		bktrk = 0, 
		watch_lit = 0, // points to what literal in the learnt clause should be watched, other than the asserting one
		antecedents_idx = 0;

	Lit u;
	Var v;
	trail_t::reverse_iterator t_it = trail.rbegin();
	do {
		for (clause_it it = current_clause.cl().begin(); it != current_clause.cl().end(); ++it) {
			Lit lit = *it;
			v = l2v(lit);
			if (!marked[v]) {
				marked[v] = true;
				if (dlevel[v] == dl) ++resolve_num;
				else { // literals from previos decision levels (roots) are entered to the learned clause.
					new_clause.insert(lit);
					if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(v);
					if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(lit);
					int c_dl = dlevel[v];
					if (c_dl > bktrk) {
						bktrk = c_dl;
						watch_lit = new_clause.size() - 1;
					}
				}
			}
		} 
		
		while (t_it != trail.rend()) {
			u = *t_it;
			v = l2v(u);
			++t_it;
			if (marked[v]) break;
		}
		marked[v] = false;
		--resolve_num;
		if(!resolve_num) continue; 
		int ant = antecedent[v];		
		current_clause = cnf[ant]; 
		current_clause.cl().erase(find(current_clause.cl().begin(), current_clause.cl().end(), u));	
	}	while (resolve_num > 0);
	for (clause_it it = new_clause.cl().begin(); it != new_clause.cl().end(); ++it) 
		marked[l2v(*it)] = false;
	Lit Negated_u = ::negate(u);
	new_clause.cl().push_back(Negated_u);		
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) 
		m_var_inc *= 1 / var_decay; // increasing importance of participating variables.
	
	++num_learned;
	asserted_lit = Negated_u;
	if (new_clause.size() == 1) { // unary clause	
		add_unary_clause(Negated_u);
	}
	else {
		add_clause(new_clause, watch_lit, new_clause.size() - 1);
	}
	

	if (verbose_now()) {	
		cout << "Learned clause #" << cnf_size() + unaries.size() << ". "; 
		new_clause.print_real_lits(); 
		cout << endl;
		cout << " learnt clauses:  " << num_learned;				
		cout << " Backtracking to level " << bktrk << endl;
	}

	if (verbose >= 1 && !(num_learned % 1000)) {
		cout << "Learned: "<< num_learned <<" clauses" << endl;		
	}	
	return bktrk; 
}

int PBSolver::analyze(const PBClause conflicting) {
    if (verbose_now()) cout << "analyze" << endl;

    PBClause current_clause = conflicting,
             new_clause;

    int resolve_num = 0,
        bktrk = 0,
        watch_lit = 0, // points to what literal in the learnt clause should be watched, other than the asserting one
        antecedents_idx = 0;

    Lit u;
    Var v;
    trail_t::reverse_iterator t_it = trail.rbegin();

    do {
        // Store the literals and coefficients for easier access
        clause_t& current_literals = current_clause.get_literals();
        vector<int>& current_coeffs = current_clause.get_coefficients();

        // Process current clause's literals
        for (size_t i = 0; i < current_literals.size(); ++i) {
            Lit lit = current_literals[i];
            int coeff = current_coeffs[i];

            v = l2v(lit);
        	VarState var_state = state[v];
        	if (var_state == VarState::V_UNASSIGNED) continue;
            if (!marked[v]) {
                marked[v] = true;
                if (dlevel[v] == dl) {
                    ++resolve_num;
                }
                else { // literals from previous decision levels are entered to the learned clause
                    new_clause.insert(lit, coeff); // Use actual coefficient, not just 1

                    if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
                    	if (verbose_now()) cout << "--------" << "bumping" << v << endl;
	                    bumpVarScore(v);
                    }
                    if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(lit);

                    int c_dl = dlevel[v];
                    if (c_dl > bktrk) {
                        bktrk = c_dl;
                        watch_lit = new_clause.size() - 1;
                    }
                }
            }
            else {
                // If literal already in new_clause, merge coefficients
                clause_t& new_literals = new_clause.get_literals();
                vector<int>& new_coeffs = new_clause.get_coefficients();
                bool found = false;

                for (size_t j = 0; j < new_literals.size(); ++j) {
                    if (new_literals[j] == lit) {
                        new_coeffs[j] += coeff;
                        found = true;
                        break;
                    }
                }

                // If the literal isn't in new_clause yet, we don't add it
                // This is correct because it's marked, so it must be a reason literal at the current decision level
            }
        }

        // Find the next literal to resolve on
        while (t_it != trail.rend()) {
            u = *t_it;
            v = l2v(u);
            ++t_it;
            if (marked[v]) break;
        }

        marked[v] = false;
        --resolve_num;
        if (!resolve_num) continue;

        int ant = antecedent[v];
        current_clause = opb[ant];

        // For PB constraints, we need to remove the literal and adjust the degree
        clause_t& literals = current_clause.get_literals();
        vector<int>& coeffs = current_clause.get_coefficients();

        // Find the position of u in the literals
        for (size_t i = 0; i < literals.size(); ++i) {
            if (literals[i] == u) {
                // Store the coefficient before removing
                int u_coeff = coeffs[i];

                // Remove the literal and its coefficient
                literals.erase(literals.begin() + i);
                coeffs.erase(coeffs.begin() + i);

                // Adjust the degree based on the removed literal's coefficient
                current_clause.set_degree(current_clause.get_degree() - u_coeff);

                break;
            }
        }
    } while (resolve_num > 0);

    // Clear marks
    clause_t& new_literals = new_clause.get_literals();
    for (clause_it it = new_literals.begin(); it != new_literals.end(); ++it) {
        marked[l2v(*it)] = false;
    }

    // Add the negation of the last resolved literal (the asserting literal)
    Lit asserting_lit = ::negate(u);

    // Calculate appropriate coefficient for the asserting literal
    // For PB constraints, we need to calculate coefficient carefully
    int max_falsified_sum = 0;
    vector<int>& new_coeffs = new_clause.get_coefficients();
    for (size_t i = 0; i < new_literals.size(); ++i) {
        max_falsified_sum += new_coeffs[i];
    }

    // Add the asserting literal with an appropriate coefficient
    // In many PB solvers this is set to 1, but it could be calculated more precisely
    // based on your specific resolution strategy
    int asserting_coeff = 1;
    new_clause.insert(asserting_lit, asserting_coeff);

    // Calculate the degree for the new clause
    // The degree should be just enough to force unit propagation of the asserting literal
    // when all other literals are falsified
    int new_degree = max_falsified_sum + 1 - asserting_coeff;

    // Ensure the degree is at least 1
    if (new_degree <= 0) new_degree = 1;

    // Set the degree for the new clause
    new_clause.set_degree(new_degree);

    // Normalize the constraint to maintain canonical form
    // normalizeConstraint(new_clause);

    if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
        m_var_inc *= 1 / var_decay; // increasing importance of participating variables
    }

    ++num_learned;
    asserted_lit = asserting_lit;

    add_clause(new_clause, watch_lit, new_clause.size() - 1);

    if (verbose_now()) {
        cout << "Learned PB constraint #" << get_size() << ". ";
        new_clause.print_real_lits();
        cout << " >= " << new_clause.get_degree();
        cout << endl;
        cout << " learnt constraints: " << num_learned;
        cout << " Backtracking to level " << bktrk << endl;
    }

    if (verbose >= 1 && !(num_learned % 1000)) {
        cout << "Learned: " << num_learned << " constraints" << endl;
    }

    return bktrk;
}


void Solver::backtrack(int k) {
	if (verbose_now()) cout << "backtrack" << endl;
	// local restart means that we restart if the number of conflicts learned in this 
	// decision level has passed the threshold. 
	if (k > 0 && (num_learned - conflicts_at_dl[k] > restart_threshold)) {	// "local restart"	
		restart(); 		
		return;
	}
	static int counter = 0;
		
	for (trail_t::iterator it = trail.begin() + separators[k+1]; it != trail.end(); ++it) { // erasing from k+1
		Var v = l2v(*it);
		if (dlevel[v]) { // we need the condition because of learnt unary clauses. In that case we enforce an assignment with dlevel = 0.
			state[v] = VarState::V_UNASSIGNED;
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_curr_activity = max(m_curr_activity, m_activity[v]);
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_should_reset_iterators = true;
	if (verbose_now()) print_state();
	trail.erase(trail.begin() + separators[k+1], trail.end());
	qhead = trail.size();
	dl = k;	
	assert_lit(asserted_lit);
	antecedent[l2v(asserted_lit)] = cnf.size() - 1;
	conflicting_clause_idx = -1;
}

void PBSolver::backtrack(int k) {
	if (verbose_now()) cout << "backtrack" << endl;
	// local restart means that we restart if the number of conflicts learned in this
	// decision level has passed the threshold.
	if (k > 0 && (num_learned - conflicts_at_dl[k] > restart_threshold)) {	// "local restart"
		restart();
		return;
	}
	static int counter = 0;

	for (trail_t::iterator it = trail.begin() + separators[k+1]; it != trail.end(); ++it) { // erasing from k+1
		Var v = l2v(*it);
		if (dlevel[v]) { // we need the condition because of learnt unary clauses. In that case we enforce an assignment with dlevel = 0.
			state[v] = VarState::V_UNASSIGNED;
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_curr_activity = max(m_curr_activity, m_activity[v]);
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_should_reset_iterators = true;
	if (verbose_now()) print_state();
	trail.erase(trail.begin() + separators[k+1], trail.end());
	qhead = trail.size();
	dl = k;
	assert_lit(asserted_lit);
	antecedent[l2v(asserted_lit)] = opb.size() - 1;
	conflicting_clause_idx = -1;
}

void Solver::validate_assignment() {
	for (unsigned int i = 1; i <= nvars; ++i) if (state[i] == VarState::V_UNASSIGNED) {
		cout << "Unassigned var: " + to_string(i) << endl; // This is supposed to happen only if the variable does not appear in any clause
	}
	for (vector<Clause>::iterator it = cnf.begin(); it != cnf.end(); ++it) {
		int found = 0;
		for(clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c) 
			if (lit_state(*it_c) == LitState::L_SAT) found = 1;
		if (!found) {
			cout << "fail on clause: "; 
			it->print();
			cout << endl;
			for (clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c)
				cout << *it_c << " (" << (int) lit_state(*it_c) << ") ";
			cout << endl;
			Abort("Assignment validation failed", 3);
		}
	}
	for (vector<Lit>::iterator it = unaries.begin(); it != unaries.end(); ++it) {
		if (lit_state(*it) != LitState::L_SAT) 
			Abort("Assignment validation failed (unaries)", 3);
	}
	cout << "Assignment validated" << endl;
}

void Solver::restart() {	
	if (verbose_now()) cout << "restart" << endl;
	restart_threshold = static_cast<int>(restart_threshold * restart_multiplier);
	if (restart_threshold > restart_upper) {
		restart_threshold = restart_lower;
		restart_upper = static_cast<int>(restart_upper  * restart_multiplier);
		if (verbose >= 1) cout << "new restart upper bound = " << restart_upper << endl;
	}
	if (verbose >=1) cout << "restart: new threshold = " << restart_threshold << endl;
	++num_restarts;
	for (unsigned int i = 1; i <= nvars; ++i) 
		if (dlevel[i] > 0) {
			state[i] = VarState::V_UNASSIGNED;
			dlevel[i] = 0;
		}	
	trail.clear();
	qhead = 0;
	separators.clear(); 
	conflicts_at_dl.clear(); 
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
		m_curr_activity = 0; // The activity does not really become 0. When it is reset in decide() it becomes the largets activity. 
		m_should_reset_iterators = true;
	}
	reset();
}

void PBSolver::restart() {
	if (verbose_now()) cout << "restart" << endl;
	restart_threshold = static_cast<int>(restart_threshold * restart_multiplier);
	if (restart_threshold > restart_upper) {
		restart_threshold = restart_lower;
		restart_upper = static_cast<int>(restart_upper  * restart_multiplier);
		if (verbose >= 1) cout << "new restart upper bound = " << restart_upper << endl;
	}
	if (verbose >=1) cout << "restart: new threshold = " << restart_threshold << endl;
	++num_restarts;
	for (unsigned int i = 1; i <= nvars; ++i)
		if (dlevel[i] > 0) {
			state[i] = VarState::V_UNASSIGNED;
			dlevel[i] = 0;
		}
	trail.clear();
	qhead = 0;
	separators.clear();
	conflicts_at_dl.clear();
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
		m_curr_activity = 0; // The activity does not really become 0. When it is reset in decide() it becomes the largets activity.
		m_should_reset_iterators = true;
	}
	reset();
}

void Solver::solve() { 
	SolverState res = _solve(); 	
	Assert(res == SolverState::SAT || res == SolverState::UNSAT || res == SolverState::TIMEOUT);
	S.print_stats();
	switch (res) {
	case SolverState::SAT: {
		S.validate_assignment();
		string str = "solution in ",
			str1 = Assignment_file;
		cout << str + str1 << endl;
		cout << "SAT" << endl;
		break;
	}
	case SolverState::UNSAT: 
		cout << "UNSAT" << endl;
		break;
	case SolverState::TIMEOUT: 
		cout << "TIMEOUT" << endl;
		return;
	}
	return;
}

void PBSolver::solve() {
	SolverState res = _solve();
	Assert(res == SolverState::SAT || res == SolverState::UNSAT || res == SolverState::TIMEOUT);
	S.print_stats();
	switch (res) {
		case SolverState::SAT: {
			S.validate_assignment();
			string str = "solution in ",
				str1 = Assignment_file;
			cout << str + str1 << endl;
			cout << "SAT" << endl;
			break;
		}
		case SolverState::UNSAT:
			cout << "UNSAT" << endl;
		break;
		case SolverState::TIMEOUT:
			cout << "TIMEOUT" << endl;
		return;
	}
	return;
}

SolverState Solver::_solve() {
	SolverState res;
	while (true) {
		if (timeout > 0 && cpuTime() - begin_time > timeout) return SolverState::TIMEOUT;
		while (true) {
			res = BCP();
			if (res == SolverState::UNSAT) return res;
			if (res == SolverState::CONFLICT)
				backtrack(analyze(cnf[conflicting_clause_idx]));
			else break;
		}
		res = decide();
		if (res == SolverState::SAT) return res;
	}
}

void PBSolver::debugScores() {
	cout << "=== Debug Scores ===" << endl;
	cout << "Variable Activities:" << endl;
	for (Var v = 1; v < nvars+1; ++v) {
		cout << "Var " << v
			 << " state: " << static_cast<int>(state[v])
			 << " activity: " << m_activity[v] << endl;
	}
	cout << "m_Score2Vars:" << endl;
	for (auto it = m_Score2Vars.begin(); it != m_Score2Vars.end(); ++it) {
		cout << "Score: " << it->first << " -> Vars: ";
		for (auto v : it->second) {
			cout << v << " ";
		}
		cout << endl;
	}
	cout << "=== End Debug Scores ===" << endl;
}

SolverState PBSolver::_solve() {
	SolverState res;
	while (true) {
		if (timeout > 0 && cpuTime() - begin_time > timeout) return SolverState::TIMEOUT;
		cout << "Decision Level: " << dl << endl;
		while (true) {
			res = BCP();
			if (res == SolverState::UNSAT) return res;
			if (res == SolverState::CONFLICT) {
				cout << "CONFLICT" << endl;
				if (state[1] == VarState::V_FALSE) {
					cout << "DEBUG PLACE" << endl;
				}
				int k = analyze(opb[conflicting_clause_idx]);
				backtrack(k);
			}
			else break;
		}
		res = decide();
		if (res == SolverState::SAT) return res;
	}
}

#pragma endregion solving


/******************  main ******************************/

void todo() {
	cout << "TODO / FIX\n"
		 "1. Sort coeffiecents and variables when creating clause\n"
		 "2. Used v2l and l2v is that good\n\n" << endl;
}

int main(int argc, char** argv){
	todo();

	decisions.push_back(2);
	decisions.push_back(7);
	decisions.push_back(6);

	begin_time = cpuTime();
	parse_options(argc, argv);

	ifstream in (argv[argc - 1]);
	if (!in.good()) Abort("cannot read input file", 1);
	cout << "This is edusat" << endl;
	PB_S.read_opb(in);
	// S.read_cnf(in);
	in.close();
	PB_S.solve();
	// S.solve();


	return 0;
}
