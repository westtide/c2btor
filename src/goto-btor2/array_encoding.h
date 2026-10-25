// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_ARRAY_ENCODING_H
#define CPROVER_GOTO_BTOR2_ARRAY_ENCODING_H

#include <cstddef>
#include <optional>

/// Storage representation only; all modes use the same C memory semantics.
struct array_encoding_optionst
{
  // bitvectors denotes the pure-BV mode. Mixed permits native Array Sorts.
  bool bitvectors = true;
  bool mixed = false;
  std::size_t mixed_threshold_bits = 2048;
  bool object_memory = true;
  // Unset: infer each runtime object capacity from the final GotoIR.
  // Set: a translation-time storage limit; an insufficient limit rejects conversion.
  std::optional<std::size_t> max_object_bytes;
  // Record typed allocation expressions and their existing allocation-time
  // size snapshots. Later stages opt into a symbolic-capacity representation.
  bool symbolic_heap = false;
  // Object-local native Arrays with a fixed index domain and size snapshots.
  bool symbolic_heap_arrays = false;
  // Hidden object tag plus a full machine-width byte offset. C types/layout
  // retain their source width; unsupported pointer serialization is rejected.
  bool symbolic_heap_wide_offsets = false;
  // Explicitly permit native object Arrays where pure BV cannot represent an
  // allocation. Other objects/logical arrays retain their selected backend.
  bool symbolic_heap_bv_array_fallback = false;
  // Remove duplicate dynamic seeds and use 64-bit cells only with a CFG
  // alignment/uniform-access certificate; otherwise preserve byte Arrays.
  bool symbolic_heap_compact = false;
};

#endif
