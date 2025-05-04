# edusat - Pseudo Boolean Extension

The following repo is a project for the course *Algorithms in Boolean Logic* in the Technion.

The goal of this project was to extend and add support for Pseudo Boolean constraints to the base SAT solver provided by the lecturer.

## Overview

`edusat` extends a standard SAT solver to handle pseudo-Boolean (PB) constraints directly, without reducing them to pure CNF. It provides:

* A parser for OPB-format PB instances.
* Constraint normalization (all constraints of the form $\sum a_i x_i + \sum b_j \bar{x}_j \geq k$).
* Slack-variable handling for mixed coefficients.
* Conflict-driven clause learning (CDCL) with PB-specific analysis by utilizing **Division based reduction**
* Backtracking search integrated with PB propagation.

## Features

* **OPB Input**: Reads `.opb` files, including comments and header directives (e.g. `#variable`, `#constraint`).
* **Normalization**: Converts all constraints to `>=` form, folds negative coefficients into the right-hand side.
* **Propagation**: Uses two watches per PB constraint to detect unit conditions and propagate assignments.
* **Conflict Analysis**: Learns new clauses and PB cuts to prevent repeated conflicts.
* **Benchmarks**: See `results.txt` for a sample comparison on FPGA and channel-routing instances.

## Code Structure

* `edusat.cpp` / `edusat.h`: Core CDCL solver interface extended for PB constraints.
* `options.cpp` / `options.h`: Command-line parsing and configuration of solver parameters.
* `pbextension.h`: Definitions of PBClause, watch lists, and propagation routines.
* `example.opb`: A minimal example demonstrating constraint format.
* `results.txt`: Sample solver output on benchmark PB instances.

## Input Format

`example.opb` illustrates the expected input layout:

```opb
* #variable= 3 #constraint= 3
* A simple test of PB propagation
1 x1 1 x2 2 x3 >= 2 ;
-1 x3 >= 0 ;
```

* Lines beginning with `*` are comments.
* The header `#variable` and `#constraint` give counts (optional).
* Each constraint ends with a semicolon (`;`).

## Results

To validate our code, we ran executed our code and `roundingsat` (solver available on the internet) side by side and we compared the final results of the execution on each test, the results can be found in `results/final_tests.txt`

## References

This project is an implementation of the work done in the following papers and tutorials:

* **Gioni Mexi**, **Timo Berthold**, **Ambros Gleixner**, and **Jakob Nordström**. *Improving Conflict Analysis in MIP Solvers by Pseudo-Boolean Reasoning*. In Proceedings of the 29th International Conference on Principles and Practice of Constraint Programming (CP 2023). LIPIcs, Vol. 207, Article 27:1–27:19, 2023. DOI: 10.4230/LIPIcs.CP.2023.27 ([jakobnordstrom.se][1])

* **Fadi A. Aloul**, **Arathi Ramani**, **Karem A. Sakallah**, and **Igor L. Markov**. *Solution and Optimization of Systems of Pseudo-Boolean Constraints*. IEEE Transactions on Computers, **56**(10):1349–1360, Oct. 2007. DOI: 10.1109/TC.2007.1075 ([aloul.net][2])

* **Jakob Nordström**. *Pseudo-Boolean Solving and Optimization*. Tutorial presented at the “Satisfiability: Theory, Practice, and Beyond Boot Camp”, The Simons Institute for the Theory of Computing, UC Berkeley, Feb. 4 2021. ([Simons Institute][3])

* **Daniel Le Berre** and **Romain Wallon**. *On Dedicated CDCL Strategies for PB Solvers*. arXiv preprint arXiv:2109.01013, Sept. 2021. ([arXiv][4])

* **RoundingSat**: The pseudo-Boolean solver powered by proof complexity. GitLab repository, created Jan. 18, 2020. [https://gitlab.com/MIAOresearch/software/roundingsat](https://gitlab.com/MIAOresearch/software/roundingsat) ([gitlab.com][5])

[1]: https://jakobnordstrom.se/docs/publications/ImprovingConflictAnalysisMIP_CP.pdf?utm_source=chatgpt.com "[PDF] Improving Conflict Analysis in MIP Solvers by Pseudo-Boolean ..."
[2]: https://www.aloul.net/Papers/faloul_tc07.pdf "untitled"
[3]: https://simons.berkeley.edu/talks/pseudo-boolean-solving-optimization "Pseudo-Boolean Solving and Optimization"
[4]: https://arxiv.org/abs/2109.01013?utm_source=chatgpt.com "On Dedicated CDCL Strategies for PB Solvers"
[5]: https://gitlab.com/MIAOresearch/software/roundingsat?utm_source=chatgpt.com "MIAO / Software / RoundingSat - GitLab"
