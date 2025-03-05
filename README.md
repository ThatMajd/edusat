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
- <s> in edusat there are 2 watched literals I think we can get away with just 1 but idk </s> 2 watched literals are used because if we know that there are 2 unresolved literals then we can't propogate


## Watch literal
- https://www.cecs.uci.edu/~papers/compendium94-03/papers/2003/dac03/pdffiles/48_3.pdf