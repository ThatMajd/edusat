## Things to implement:

- <s>Write file (opb) parser</s>
- <s>Normalize constraints</s>
- Sort coefficients and variables when creating clause
- Parse # variables & Clauses from input
- **PBClause**
  - Add *Slack* or current sum
- **Solver**
  - BCP
  - Analyze
  - Backtrack (?)

## Current progress
### Parser:
- The file parser uses the same variable encoding as edusat positive -> even and negative -> odd
- Parser assumes constraint are >=, to normalize the coef we take the positive sum of negative coef and add them to the RHS
- in edusat there are 2 watched literals I think we can get away with just 1 but idk
