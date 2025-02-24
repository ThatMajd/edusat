## Things to implement:

- <s>Write file (opb) parser</s>
- <s>Normalize constraints</s>
- Sort coefficients and variables when creating clause
- Modify PBClause
- Modify Solver

## Current progress
### Parser:
- The file parser uses the same variable encoding as edusat positive -> even and negative -> odd
- Parser assumes constraint are >=, to normalize the coef we take the positive sum of negative coef and add them to the RHS
