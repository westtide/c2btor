#ifndef CPROVER_GOTO_BTOR2_LOWER_FLOAT_OPERATIONS_H
#define CPROVER_GOTO_BTOR2_LOWER_FLOAT_OPERATIONS_H

class goto_modelt;

// Replace only CBMC library bodies, before inlining, with exact math nodes.
// Ordinary symex and user-defined functions retain their original bodies.
void lower_float_operations(goto_modelt &model);

#endif
