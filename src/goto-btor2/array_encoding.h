#ifndef CPROVER_GOTO_BTOR2_ARRAY_ENCODING_H
#define CPROVER_GOTO_BTOR2_ARRAY_ENCODING_H

#include <cstddef>
#include <optional>

/// Storage representation only; both modes use the same C memory semantics.
struct array_encoding_optionst
{
  bool bitvectors = true;
  bool object_memory = true;
  // Unset: infer each runtime object capacity from the final GotoIR.
  // Set: an explicit per-object bound; exceeding it remains model_limit.
  std::optional<std::size_t> max_object_bytes;
};

#endif
