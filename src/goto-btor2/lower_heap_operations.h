#ifndef CPROVER_GOTO_BTOR2_LOWER_HEAP_OPERATIONS_H
#define CPROVER_GOTO_BTOR2_LOWER_HEAP_OPERATIONS_H
class goto_modelt;
/// Preserve primitive events from CBMC library bodies before call inlining.
void lower_heap_operations(goto_modelt &);
#endif
