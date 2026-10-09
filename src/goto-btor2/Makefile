SRC = btor2_builder.cpp \
      heap_model.cpp \
      object_memory.cpp \
      object_copy.cpp \
      memory_capacity.cpp \
      memory_access.cpp \
      goto_btor2_unroll.cpp \
      btor2_type_utils.cpp \
      expr_to_btor2.cpp \
      expr_to_btor2_arrays.cpp \
      expr_to_btor2_bitvec.cpp \
      expr_to_btor2_float.cpp \
      ieee754_arith.cpp \
      ieee754_math.cpp \
      expr_to_btor2_pointers.cpp \
      goto_btor2.cpp \
      goto_btor2_format.cpp \
      goto_btor2_assign.cpp \
      goto_btor2_collect.cpp \
      goto_btor2_instructions.cpp \
      simplify_callback_targets.cpp \
      lower_recursive_calls.cpp \
      lower_float_operations.cpp \
      lower_heap_operations.cpp \
      lower_array_operations.cpp \
      # empty

INCLUDES = -I ..

include ../config.inc
include ../common

CLEANFILES = goto-btor2$(LIBEXT)

all: goto-btor2$(LIBEXT)

###############################################################################

goto-btor2$(LIBEXT): $(OBJ)
	$(LINKLIB)
