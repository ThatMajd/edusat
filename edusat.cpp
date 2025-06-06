// #include "edusat.h"
#include "pbextension.h"

Solver S;
PBSolver PB_S;

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
	int vars, clauses, eqls;;

	int l = 0;

	// First line we extract variables and clauses
	if (!match(in, "* #variable=")) Abort("Expecting `*' in the input file", 1);
	in >> vars;
	if (!match(in, " #constraint=")) Abort("No constraints provided", 1);
	in >> clauses;
	if (match(in, " #equal=")) {
		in >> eqls;
			if (eqls > 0) Abort("Don't currently support equals", 1);
	}

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
	int coef, var, rhs;
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
			normalization_sum = 0;
			add_clause(pb, 0, 1);
			// pb.print();
			pb.reset();

			in >> token1;
			assert(token1 == ";");
			while (in.peek() == '\n') in.get();
			l++;

		} else {
			coef = std::stoi(token1);
			var = std::stoi(token2.substr(1));

			if (var > vars) Abort("Literal index larger than declared on the first line", 1);
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(var);



			if (coef < 0) {
				normalization_sum += -coef;
				var = -var;
				coef = -coef;
			}
			int lit = v2l(var);
			pb.insert(v2l(var), coef);

			if Neg(lit) {
				watches_false[l2v(lit)].push_back(opb.size());
			}
			else {
				watches_true[l2v(lit)].push_back(opb.size());
			}

			if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(v2l(var));
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
	if (Neg(l)) {
		prev_state[var] = state[var] = VarState::V_FALSE;
	}
	else {
		prev_state[var] = state[var] = VarState::V_TRUE;
	}
	dlevel[var] = dl;
	++num_assignments;
	if (verbose_now()) cout << l2rl(l) <<  " @ " << dl << endl;
}

inline void PBSolver::remove_assignment(Lit l) {
	Var v = l2v(l);

	// If we reached decision which was made by the solver and not a propagation then decrease the dl
	if (antecedent[v] == -1) dl--;
	// trail.pop_back();
	antecedent[v] = -1;
	prev_state[v] = state[v] = VarState::V_UNASSIGNED;
	dlevel[v] = dl;
	--num_assignments;
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
	c.lw_set(l);
	c.rw_set(r);
	int loc = static_cast<int>(opb.size());  // the first is in location 0 in cnf
	int size = c.size();

	// watches[c.lit(l)].push_back(loc);
	// watches[c.lit(r)].push_back(loc);
	opb.push_back(c);
	// opb.insert(opb.begin(), c);
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

	for (Var i = 1; i < state.size(); ++i) {
		if (state[i] == VarState::V_UNASSIGNED) {
			best_lit = v2l(-i);
			goto Apply_decision;
		}
	}
	return SolverState::SAT;

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

	for (Var i = 1; i < state.size(); ++i) {
		if (state[i] == VarState::V_UNASSIGNED) {
			best_lit = v2l(-i);
			goto Apply_decision;
		}
	}
	return SolverState::SAT;

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

inline PBClauseState PBClause::next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc) {
    if (verbose_now()) cout << "pb_next_not_false" << endl;

    // Compute S_val = sum(coefficients for literals assigned true)
    // and R_val = sum(coefficients for unassigned literals)
    int S_val = 0;
    int R_val = 0;
    for (size_t i = 0; i < literals.size(); ++i) {
        LitState ls = PB_S.lit_state(literals[i]); // Assuming access to solver state S.
        if (ls == LitState::L_SAT)
            S_val += coefficients[i];
        else if (ls == LitState::L_UNASSIGNED)
            R_val += coefficients[i];
    }

    // Check if the constraint is already satisfied.
    if (S_val >= degree)
        return PBClauseState::PB_SAT;

    // Conflict: Even if all unassigned literals become true, threshold cannot be met.
    if (S_val + R_val < degree) {
        if (verbose_now()) {
            print_real_lits();
            cout << " is conflicting" << endl;
        }
        return PBClauseState::PB_UNSAT;
    }

    // If clause is not binary, try to find another literal (other than other_watch) to watch.
    if (!binary) {
        for (size_t i = 0; i < literals.size(); ++i) {
            if (literals[i] == other_watch)
                continue;
            if (S.lit_state(literals[i]) != LitState::L_UNSAT) { // Found a candidate.
                loc = i;
                if (is_left_watch)
                    lw = i;
                else
                    rw = i;
                return PBClauseState::PB_UNDEF; // No propagation; watch updated.
            }
        }
    }

    // No replacement found: Check if the other watched literal forces an implication.
    int coeff_other = -1;
    for (size_t i = 0; i < literals.size(); ++i) {
        if (literals[i] == other_watch) {
            coeff_other = coefficients[i];
            break;
        }
    }
    Assert(coeff_other != -1); // Must find other_watch in the clause.

    // Use the forced condition: if other_watch is unassigned and without its contribution
    // the total possible sum is below the threshold, then it must be set to true.
    switch (S.lit_state(other_watch)) {
        case LitState::L_UNSAT:
            if (verbose_now()) {
                print_real_lits();
                cout << " is conflicting" << endl;
            }
            return PBClauseState::PB_UNSAT;
        case LitState::L_UNASSIGNED:
            if (S_val + (R_val - coeff_other) < degree)
                return PBClauseState::PB_UNIT;
            return PBClauseState::PB_UNDEF;
        case LitState::L_SAT:
            return PBClauseState::PB_SAT;
        default:
            Assert(0);
            return PBClauseState::PB_UNDEF;
    }
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

ClauseState PBSolver::propagate_assignment(int clause_idx) {
	if (verbose_now()) cout << "propagate_assignment" << endl;

	PBClause c = opb[clause_idx];

	clause_t literals = c.get_literals();
	std::vector<int> coefficients = c.get_coefficients();
	int degree = c.get_degree();

	int slack = -degree;
	int true_sum = 0;

	for (int i=0; i < c.size(); ++i) {
		if (PB_S.lit_state(literals[i]) != LitState::L_UNSAT) {
			slack += coefficients[i];
		}
	}
	if (slack < 0) return ClauseState::C_UNSAT;
	for (int i=0; i < c.size(); ++i) {
		if (PB_S.lit_state(literals[i]) == LitState::L_UNASSIGNED && coefficients[i] > slack) {
			assert_lit(literals[i]);
			antecedent[l2v(literals[i])] = clause_idx;

		}
		if (PB_S.lit_state(literals[i]) == LitState::L_SAT) {
			true_sum += coefficients[i];
		}
	}
	if (true_sum - degree >= 0) return ClauseState::C_SAT;
	return ClauseState::C_UNDEF;
}
// AssertionStatus ConstrExp<SMALL, LARGE>::isAssertingBefore(const IntVecIt& level, int lvl) const {
// 	assert(lvl >= 0);
// 	assert(isSaturated());
// 	SMALL largestCoef = 0;
// 	LARGE slack = -degree;
// 	cout << degree << endl;
// 	for (int i = 0; i < (int)vars.size(); ++i) {
// 		Var v = vars[i];
// 		Lit l = coefs[v] < 0 ? -v : v;
// 		if (level[-l] < lvl) continue;  // falsified lit does not contribute to slack
// 		SMALL c = aux::abs(coefs[v]);
// 		if (level[l] >= lvl) largestCoef = std::max(largestCoef, c);  // unknown lit
// 		slack += c;
// 		cout << slack << endl;
// 		// _slack += c;
// 		if (slack >= degree) return AssertionStatus::NONASSERTING;
// 	}
// 	if (slack >= largestCoef)
// 		return AssertionStatus::NONASSERTING;
// 	else if (slack >= 0)
// 		return AssertionStatus::ASSERTING;
// 	else
// 		return AssertionStatus::FALSIFIED;
// }


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


	if (global_conflict) return SolverState::UNSAT;

    while (qhead < trail.size()) {
        // Get the assigned literal and compute its negation.
        Lit assigned_lit = trail[qhead++];
        Var v = l2v(assigned_lit);

        if (verbose_now()) cout << "propagating " << l2rl(assigned_lit) << endl;

        // Process each clause that contains this now-false literal.
    	for (auto* clauses : {&watches_true[v], &watches_false[v]}){
    		for (int clause_idx : *clauses) {
    			PBClause& c = opb[clause_idx];
    			// Propagate the effect of the false literal on the clause.
    			ClauseState res = propagate_assignment(clause_idx);

    			switch (res) {
    				case ClauseState::C_UNSAT:
    					if (verbose_now()) print_state();
    					if (dl == 0) return SolverState::UNSAT;
    					conflicting_clause_idx = clause_idx;
    					if (verbose_now()) cout << "conflict" << endl;
    					return SolverState::CONFLICT;

    				case ClauseState::C_UNIT: {
    					// The clause is unit – propagate the remaining literal.
    					// Lit unit_lit = c.get_unit_literal();
    					// if (verbose_now()) cout << "propagating: " << l2rl(unit_lit) << endl;
    					// assert_lit(unit_lit);
    					// antecedent[l2v(unit_lit)] = clause_idx;
    					// trail.push_back(unit_lit);
    					break;
    				}

    				case ClauseState::C_SAT:
    					if (verbose_now()) cout << "clause is sat" << endl;
    					// No action needed if the clause is satisfied.
    					break;

    				default:
    					// Additional handling if needed.
    						break;
    			}
    		}
    	}
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

PBClause PBSolver::cancel(PBClause conflict, PBClause reason, Lit pivot) {
	map<Var, map<Lit, int>> var_map;

	for (int i=0; i < conflict.size(); ++i) {
		var_map[l2v(conflict.literal_at(i))][conflict.literal_at(i)] += conflict.coeff_at(i);
	}
	for (int i=0; i < reason.size(); ++i) {
		var_map[l2v(reason.literal_at(i))][reason.literal_at(i)] += reason.coeff_at(i);
	}

	int correcting_sum = 0;
	PBClause new_clause;

	// README 1
	for (const auto &var_pair : var_map) {
		// std::cout << "Var " << var_pair.first << ":\n";
		int a = 0 , b = 0;
		for (const auto &lit_pair : var_pair.second) {
			// std::cout << "   Lit " << lit_pair.first << " : " << lit_pair.second << "\n";
			Lit l = lit_pair.first;
			int coeff = lit_pair.second;

			if (Neg(l)) {
				a += coeff;
			} else {
				b += coeff;
			}
		}
		if ( b - a > 0) {
			correcting_sum += a;
			new_clause.insert(v2l(var_pair.first), b-a);
		}
		else if ( b - a < 0) {
			correcting_sum += b;
			new_clause.insert(v2l(-var_pair.first), a-b);
		}
		else if (b - a == 0) {
			correcting_sum += a;
			// The terms cancel out no need to add variable
		}
	}
	new_clause.set_degree(conflict.get_degree() + reason.get_degree() - correcting_sum);
	return new_clause;
}

PBClause PBSolver::reduce(PBClause c, Lit pivot) {
	PBClause new_clause;
	std::vector<Lit> literals = c.get_literals();
	std::vector<int> coefficients = c.get_coefficients();
	int pivot_coef = c.get_coefficient(pivot);

	if (pivot_coef <= 0) {
		cout << "debugggg" << endl;
	}
	if (pivot_coef <= 0) {
		cout << "KILL ME NOW" << endl;
	}
	Assert(pivot_coef > 0);

	int weakend_sum = 0;

	// Reduce: remove all literals that are not falsified and whose coefficient is not divisible by the pivot coefficient.
	// We keep the pivot literal regardless.
	for (int i = 0; i < literals.size(); ++i) {
		// If the literal is not falsified and its coefficient is not divisible by pivot_coef...
		if (lit_state(literals[i]) != LitState::L_UNSAT && (coefficients[i] % pivot_coef)) {
			weakend_sum += coefficients[i];
			// Erase the literal and its coefficient.
			literals.erase(literals.begin() + i);
			coefficients.erase(coefficients.begin() + i);
			i--;  // adjust index because of removal
		}
	}
	// Adjust the degree by subtracting the sum of coefficients removed.
	int degree = c.get_degree() - weakend_sum;

	// Division: Divide each remaining coefficient by pivot_coef, rounding up.
	// Rounding up is performed using: (a + b - 1) / b.
	for (int i = 0; i < coefficients.size(); ++i) {
		coefficients[i] = (coefficients[i] + pivot_coef - 1) / pivot_coef;
	}
	// Also adjust the degree in the same way.
	degree = (degree + pivot_coef - 1) / pivot_coef;

	// Build the new clause from the reduced literals, adjusted coefficients, and updated degree.
	new_clause.set_literals(literals);
	new_clause.set_coefficients(coefficients);
	new_clause.set_degree(degree);

	return new_clause;
}

PBClause PBSolver::resolve(const PBClause c, const PBClause r, Lit pivot) {
	// Reduce: remove all non falsified literals, keep pivot.
	PBClause conflict = reduce(c, pivot);
	PBClause reason = reduce(r, pivot);


	return cancel(conflict, reason, pivot);
}


// int PBSolver::analyze(const PBClause conflicting) {
// 	if (verbose_now()) cout << "analyze" << endl;
// 	PBClause	current_clause = conflicting,
// 			new_clause;
// 	int resolve_num = 0,
// 		bktrk = 0,
// 		watch_lit = 0, // points to what literal in the learnt clause should be watched, other than the asserting one
// 		antecedents_idx = 0;
// 	bool applied_resolution = false;
//
//
// 	Lit u;
// 	Var v;
// 	trail_t::reverse_iterator t_it = trail.rbegin();
// 	do {
// 		for (int i = 0; i < current_clause.size(); ++i) {
// 			Lit lit = current_clause.literal_at(i);
// 			int coeff = current_clause.coeff_at(i);
//
// 			v = l2v(lit);
// 			if (!marked[v]) {
// 				marked[v] = true;
// 				if (dlevel[v] == dl) ++resolve_num;
// 				else { // literals from previos decision levels (roots) are entered to the learned clause.
// 					if (lit_state(lit) == LitState::L_UNASSIGNED) continue;
//
// 					new_clause.insert(lit, coeff);
// 					if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(v);
// 					if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(lit);
// 					int c_dl = dlevel[v];
// 					if (c_dl > bktrk) {
// 						bktrk = c_dl;
// 					}
// 				}
// 			}
// 		}
//
// 		if (t_it == trail.rend()){
// 			break;
// 		}
// 		while (t_it != trail.rend()) {
// 			u = *t_it;
// 			v = l2v(u);
// 			++t_it;
// 			if (marked[v]) break;
// 		}
//
// 		marked[v] = false;
// 		--resolve_num;
// 		if(!resolve_num) continue;
// 		int ant = antecedent[v];
// 		if (ant == -1) continue;
// 		PBClause reason = opb[ant];
//
// 		Lit pivot_conflict = current_clause.get_lit_with_pivot(u);
// 		Lit pivot_reason = reason.get_lit_with_pivot(u);
//
// 		// Ensuring the pivot exists and they are opposite in the 2 constraints
// 		if (pivot_conflict == -1 || pivot_reason == -1) continue;
// 		if (pivot_conflict == pivot_reason) continue;
//
// 		current_clause = resolve(current_clause, reason, u);
// 		applied_resolution = true;
// 		if (current_clause.size() == 0 && current_clause.get_degree() > 0) {
// 			global_conflict = true;
// 			bktrk = 0;
// 			break;
// 		}
// 	}	while (resolve_num > 0);
//
// 	std::vector<Lit> literals = current_clause.get_literals();
// 	for (clause_it it = literals.begin(); it != literals.end(); ++it)
// 		marked[l2v(*it)] = false;
//
//
//
// 	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT)
// 		m_var_inc *= 1 / var_decay; // increasing importance of participating variables.
//
// 	if (applied_resolution) {
// 		// update_asserted_lits(current_clause);
// 		asserted_lits.clear();
// 		asserted_lits.push_back(::negate(u));
// 		++num_learned;
// 		opb.push_back(current_clause);
//
// 		Lit l;
// 		for (int i = 0; i < current_clause.size(); i++) {
// 			l = current_clause.literal_at(i);
// 			if (Neg(l)) {
// 				watches_false[l2v(l)].push_back(opb.size());
// 			} else {
// 				watches_true[l2v(l)].push_back(opb.size());
// 			}
// 		}
// 		// add_clause(current_clause, 0 , 1);
// 	}
//
//
// 	if (verbose_now()) {
// 		new_clause.print_real_lits();
// 		cout << endl;
// 		cout << " learnt clauses:  " << num_learned;
// 		cout << " Backtracking to level " << bktrk << endl;
// 	}
//
// 	if (verbose >= 1 && !(num_learned % 1000)) {
// 		cout << "Learned: "<< num_learned <<" clauses" << endl;
// 	}
// 	return bktrk;
// }

// CeSuper Solver::analyze(CeSuper conflict) {
// 	assert(conflict->hasNegativeSlack(Level));
//
// 	if (logger) logger->logComment("Analyze", stats);
// 	stats.NADDEDLITERALS += conflict->vars.size();
//
// 	CeSuper confl = prepareConflictConstraint(conflict);
// 	assignActiveSet(confl);
//
// 	while (decisionLevel() > 0) {
// 		if (asynch_interrupt) throw asynchInterrupt;
// 		Lit l = trail.back();
// 		if (confl->hasLit(-l)) {
// 			assert(confl->hasNegativeSlack(Level));
//
// 			AssertionStatus status = confl->isAssertingBefore(Level, decisionLevel());
// 			// Conflict constraint could now be asserting after removing some assignments.
// 			if (status == AssertionStatus::ASSERTING) break;
// 			// Constraint is already falsified by before last decision on trail.
// 			else if (status == AssertionStatus::FALSIFIED) {
// 				backjumpTo(decisionLevel() - 1);
// 				continue;
// 			}
//
// 			Constr& reasonC = getReasonConstraint(l);
// 			reasonC.resolveWith(confl, l, &actSet, *this);
// 		}
// 		removeLastAssignment();
// 	}
// 	bumpLiteralActivity();
//
// 	assert(confl->hasNegativeSlack(Level));
// 	return confl;
// }

AssertionStatus PBSolver::is_asserting(PBClause c, int lvl) {
	// Clause is asserting if it forces an assignment on at least 1 variable in a lower decision level.
	if (verbose_now()) cout << "is_asserting" << endl;

	clause_t literals = c.get_literals();
	std::vector<int> coefficients = c.get_coefficients();
	int degree = c.get_degree();

	int slack = -degree;
	int largestCoef = 0;

	for (int i=0; i < c.size(); ++i) {
		// We ignore variables that have been falsified at previous decision levels
		// if they were falsified now we count them
		// if they are true or unassigned we also count them
		Lit l = literals[i];
		int coef = coefficients[i];
		if (PB_S.lit_state(l) == LitState::L_UNSAT && dlevel[l2v(l)] < lvl) {
			continue;
		}
		if (dlevel[l2v(l)] >= lvl) largestCoef = std::max(largestCoef, coef);
		slack += coef;
		if (slack >= degree) return AssertionStatus::NONASSERTING;
	}

	if (slack >= largestCoef) return AssertionStatus::NONASSERTING;
	if (slack >= 0) return AssertionStatus::ASSERTING;
	return AssertionStatus::FALSIFIED;
}

void PBSolver::print_clause(PBClause c) {
	std::string constraint = "";
	std::string assignment = "";
	std::string dlevel = "";

	for (int i=0; i < c.size(); ++i) {
		constraint += c.coeff_at(i);
		if (Neg(c.literal_at(i))) std::cout << '~';
		cout << "x" << l2v(c.literal_at(i)) << "\t";

		assignment += std::to_string(int(lit_state(c.literal_at(i)))) + "\t\t";
		dlevel += std::to_string(dlevel[l2v(c.literal_at(i))]) + "\t\t";
	}
	constraint += ">= " + c.get_degree();
	cout << constraint << endl;
	cout << assignment << endl;
	cout << dlevel << endl;
}

int PBSolver::analyze(const PBClause conflicting) {
	if (verbose_now()) cout << "analyze" << endl;
	PBClause	confl = conflicting;

	// cout << "- CONFLICT -" << endl;
	// confl.print();

	trail_t::reverse_iterator t_it = trail.rbegin();
	bool applied_resolution = false;
	int decision_level = dl;
	while (decision_level > 0) {
		if (t_it == trail.rend()){
			break;
		}

		Lit l = *t_it;
		Var v = l2v(l);
		int ant = antecedent[v];

		if (ant == -1) {
			// We reached a decision by the solver
			AssertionStatus asserting = is_asserting(confl, decision_level);

			if (asserting == AssertionStatus::ASSERTING) {
				if (*(trail.begin() + separators[decision_level]) == l) cout << "we good" << endl;
				update_asserted_lits(confl, decision_level);
				decision_level--;
				break;
			}
			else if (asserting == AssertionStatus::FALSIFIED) {
				int target = *(trail.begin() + separators[decision_level - 1] - 1);

				while (*t_it != target) {t_it++;}

				decision_level--;
				continue;

			}
		}
		if (confl.hasLit(::negate(l)) && ant != -1) {
			assert(ant != -1);
			confl = reduce(confl, ::negate(l));
			PBClause reason_clause = opb[ant];

			if (!reason_clause.hasLit(l)) {
				cout << "Reason has no literal " << l << endl;
			}
			confl = resolve(confl, reason_clause, l);
			applied_resolution = true;
		}
		// remove_assignment(l);
		// if (antecedent[v] == -1) decision_level--;
		++t_it;
	}
	if ((confl.size() == 0 && confl.get_degree() > 0) || !confl.can_be_satisfied()) {
		global_conflict = true;
		return 0;
	}

	if (applied_resolution) {
		++num_learned;

		opb.push_back(confl);
		Lit l;
		for (int i = 0; i < confl.size(); i++) {
			l = confl.literal_at(i);
			if (Neg(l)) {
				watches_false[l2v(l)].push_back(opb.size() - 1);
			} else {
				watches_true[l2v(l)].push_back(opb.size() - 1);
			}
		}
	}
	else {
		opb.erase(opb.begin() + conflicting_clause_idx);
		opb.push_back(confl);
	}
	// cout << "- Backtracking to " << decision_level << endl;
	// cout << "- Learned the following constraint " << decision_level << endl;
	// confl.print();
	int bktrk = 0;
	for (int i = 0; i < confl.size(); i++) {
		Var v = l2v(confl.literal_at(i));
		int c_dl = dlevel[v];
		if (c_dl == dl) {continue;}
		if (c_dl > bktrk) {
			bktrk = c_dl;
		}
	}
	if (!(num_learned % 1000)) {
		cout << "Learned: "<< num_learned <<" clauses" << endl;
	}
	return bktrk;
}

// int PBSolver::analyze(const PBClause conflicting) {
// 	if (verbose_now()) cout << "analyze" << endl;
// 	PBClause	confl = conflicting,
// 			reason_clause;
// 	int resolve_num = 0,
// 		bktrk = 0;
// 	bool applied_resolution = false;
//
// 	cout << "conflicting" << endl;
// 	confl.print();
//
// 	Lit u;
// 	Var v;
// 	trail_t::reverse_iterator t_it = trail.rbegin();
// 	do {
// 		for (int i = 0; i < confl.size(); ++i) {
// 			Lit lit = confl.literal_at(i);
// 			int coeff = confl.coeff_at(i);
//
// 			v = l2v(lit);
// 			if (!marked[v]) {
// 				marked[v] = true;
// 				if (dlevel[v] == dl) ++resolve_num;
// 				else { // literals from previos decision levels (roots) are entered to the learned clause.
// 					if (lit_state(lit) == LitState::L_UNASSIGNED) continue;
//
// 					// new_clause.insert(lit, coeff);
// 					if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(v);
// 					if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(lit);
// 					int c_dl = dlevel[v];
// 					if (c_dl > bktrk) {
// 						bktrk = c_dl;
// 					}
// 				}
// 			}
// 		}
//
// 		if (t_it == trail.rend()){
// 			break;
// 		}
// 		while (t_it != trail.rend()) {
// 			u = *t_it;
// 			v = l2v(u);
// 			++t_it;
// 			if (marked[v]) break;
// 		}
//
// 		marked[v] = false;
// 		--resolve_num;
// 		if(!resolve_num) continue;
// 		int ant = antecedent[v];
//
// 		if (confl.hasLit(::negate(u)) && ant != -1) {
// 			assert(ant != -1);
// 			confl = reduce(confl, ::negate(u));
// 			reason_clause = opb[ant];
//
// 			if (!reason_clause.hasLit(u)) {
// 				cout << "Reason has no literal " << u << endl;
// 			}
// 			confl = resolve(confl, reason_clause, u);
// 			applied_resolution = true;
// 		}
//
//
// 		if ((confl.size() == 0 && confl.get_degree() > 0) || !confl.can_be_satisfied()) {
// 			global_conflict = true;
// 			bktrk = 0;
// 			break;
// 		}
// 	}	while (resolve_num > 0);
//
// 	std::vector<Lit> literals = confl.get_literals();
// 	for (clause_it it = literals.begin(); it != literals.end(); ++it)
// 		marked[l2v(*it)] = false;
//
//
//
// 	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT)
// 		m_var_inc *= 1 / var_decay; // increasing importance of participating variables.
//
// 	asserted_lits.clear();
// 	asserted_lits.push_back(::negate(u));
// 	if (applied_resolution) {
// 		// update_asserted_lits(current_clause);
// 		++num_learned;
// 		opb.push_back(confl);
//
// 		Lit l;
// 		for (int i = 0; i < confl.size(); i++) {
// 			l = confl.literal_at(i);
// 			if (Neg(l)) {
// 				watches_false[l2v(l)].push_back(opb.size() - 1);
// 			} else {
// 				watches_true[l2v(l)].push_back(opb.size() - 1);
// 			}
// 		}
// 		// add_clause(current_clause, 0 , 1);
// 	}
//
//
// 	if (verbose_now()) {
// 		cout << endl;
// 		cout << " learnt clauses:  " << num_learned;
// 		cout << " Backtracking to level " << bktrk << endl;
// 	}
//
// 	if (verbose >= 1 && !(num_learned % 1000)) {
// 		cout << "Learned: "<< num_learned <<" clauses" << endl;
// 	}
// 	return bktrk;
// }

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

	if (separators[k+1] >= trail.size()) {
		cout << "lord have mercy" << endl;
	};

	for (trail_t::iterator it = trail.begin() + separators[k+1]; it != trail.end(); ++it) { // erasing from k+1
		// cout << *it << endl;
		Var v = l2v(*it);
		if (dlevel[v]) { // we need the condition because of learnt unary clauses. In that case we enforce an assignment with dlevel = 0.
			state[v] = VarState::V_UNASSIGNED;
			antecedent[v] = -1;
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_curr_activity = max(m_curr_activity, m_activity[v]);
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_should_reset_iterators = true;
	if (verbose_now()) print_state();
	trail.erase(trail.begin() + separators[k+1], trail.end());
	qhead = trail.size();
	dl = k;
	for (auto asserted_lit : asserted_lits) {
		assert_lit(asserted_lit);
		antecedent[l2v(asserted_lit)] = opb.size() - 1;
	}
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

void PBSolver::validate_assignment() {
	// Check that all variables that appear have an assignment.
	for (unsigned int i = 1; i <= nvars; ++i) {
		if (state[i] == VarState::V_UNASSIGNED) {
			cout << "Unassigned var: " + to_string(i) << endl;
			// This should only happen if the variable does not appear in any constraint.
		}
	}

	// Check each pseudo boolean constraint.
	// Assume opb is the vector of PBClause constraints.
	for (vector<PBClause>::iterator it = opb.begin(); it != opb.end(); ++it) {
		int sum = 0;
		vector<Lit> lits = it->get_literals();
		vector<int> coefs = it->get_coefficients();

		// Sum the coefficients of all satisfied literals.
		for (size_t j = 0; j < lits.size(); ++j) {
			if (lit_state(lits[j]) == LitState::L_SAT) {
				sum += coefs[j];
			}
		}

		// If the sum is less than the required degree, the constraint is unsatisfied.
		if (sum < it->get_degree()) {
			cout << "Fail on constraint: ";
			it->print();  // Assume PBClause has a print method.
			cout << endl;
			// Also print the state of each literal in the constraint.
			for (size_t j = 0; j < lits.size(); ++j) {
				cout << lits[j] << " (" << (int)lit_state(lits[j]) << ") ";
			}
			cout << endl;
			Abort("Assignment validation failed", 3);
		}
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
	// state[1] = VarState::V_TRUE;
	// state[2] = state[3] = state[4] = state[5] = VarState::V_FALSE;
	//
	// resolve(opb[1], opb[0], 4);
	// return;
	SolverState res = _solve();
	Assert(res == SolverState::SAT || res == SolverState::UNSAT || res == SolverState::TIMEOUT);
	PB_S.print_stats();
	switch (res) {
		case SolverState::SAT: {
			PB_S.validate_assignment();
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

SolverState PBSolver::_solve() {
	SolverState res;
	while (true) {
		if (timeout > 0 && cpuTime() - begin_time > timeout) return SolverState::TIMEOUT;
		while (true) {
			if (antecedent[5985] == 15372) {
				cout << "WTF GOING ON HERE?" << endl;
			}
			res = BCP();

			// ant_graph();

			if (res == SolverState::UNSAT) return res;
			if (res == SolverState::CONFLICT) {
				// cout << "CONFLICT" << endl;
				int k = analyze(opb[conflicting_clause_idx]);
				backtrack(k);
				// cout << "- AT LEVEL = " << dl << endl;

				// ant_graph();
			}
			else break;
		}
		res = decide();
		if (res == SolverState::SAT) return res;
	}
}

#pragma endregion solving


/******************  main ******************************/


int main(int argc, char** argv){
	begin_time = cpuTime();
	parse_options(argc, argv);

	ifstream in (argv[argc - 1]);
	if (!in.good()) Abort("cannot read input file", 1);
	cout << "This is edusat" << endl;
	PB_S.read_opb(in);
	// S.read_cnf(in);
	in.close();
	// S.solve();
	PB_S.solve();


	return 0;
}