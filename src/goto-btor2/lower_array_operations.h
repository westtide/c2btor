#ifndef CPROVER_GOTO_BTOR2_LOWER_ARRAY_OPERATIONS_H
#define CPROVER_GOTO_BTOR2_LOWER_ARRAY_OPERATIONS_H

class goto_programt;
class symbol_tablet;
class messaget;

// Packed object memory implements a snapshot copy in one state update;
// other encodings retain the byte-loop lowering.
void lower_array_operations(
  goto_programt &, symbol_tablet &, messaget &, bool packed_copy = false);

#endif
