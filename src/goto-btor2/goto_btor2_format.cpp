#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/string_constant.h>

#include "goto_btor2_converter.h"

#include <algorithm>

bool goto_to_btor2_convertert::process_sprintf_hex(
  unsigned loc,
  btor2_nid_t at_loc,
  const goto_programt::instructiont &instruction)
{
  const auto &args = instruction.call_arguments();
  if(
    args.size() != 3 || (!instruction.call_lhs().is_nil() &&
                         instruction.call_lhs().id() != ID_symbol))
    return false;
  // Only a declaration may use this library primitive. A user-supplied body
  // must be inlined and keep its own semantics.
  const auto &callee = to_symbol_expr(instruction.call_function());
  if(ns.lookup(callee.get_identifier()).value.is_not_nil())
    return false;
  exprt format = args[1];
  while(format.id() == ID_typecast)
    format = to_typecast_expr(format).op();
  if(format.id() == ID_address_of)
    format = to_address_of_expr(format).object();
  if(format.id() == ID_index && to_index_expr(format).index().is_zero())
    format = to_index_expr(format).array();
  if(format.id() != ID_string_constant)
    return false;
  const auto text = id2string(format.get(ID_value));
  if(text.size() < 2 || text[0] != '%')
    return false;
  std::size_t position = 1;
  unsigned precision = 1;
  if(text[position] == '.')
  {
    precision = 0;
    ++position;
    while(position < text.size() && text[position] >= '0' &&
          text[position] <= '9')
    {
      precision = precision * 10 + (text[position++] - '0');
      if(precision > 4096)
        return false;
    }
  }
  if(
    position + 1 != text.size() ||
    (text[position] != 'x' && text[position] != 'X'))
    return false;
  const bool upper = text[position] == 'X';
  const auto type = unsigned_int_type();
  const auto width = config.ansi_c.int_width;
  const auto byte_width = memory.heap.byte_bits;
  if(
    byte_width > width || width < 16 ||
    (args[2].type().id() != ID_signedbv &&
     args[2].type().id() != ID_unsignedbv) ||
    expr_converter.get_width(args[2].type()) != width)
    return false;
  auto destination = expr_converter.convert(args[0]);
  auto value =
    expr_converter.convert(typecast_exprt::conditional_cast(args[2], type));
  if(!destination || !value)
  {
    conversion_error("Cannot encode hexadecimal sprintf arguments");
    return true;
  }
  const auto sort = expr_converter.convert_type(type);
  const auto bool_sort = builder.get_bool_sort();
  const auto byte_sort = builder.get_or_create_bitvec_sort(byte_width);
  const unsigned digits = (width + 3) / 4;
  auto constant = [&](unsigned n) { return builder.constd(sort, n); };
  auto length = constant(precision);
  for(unsigned n = 1; n <= digits; ++n)
  {
    // For precision zero, zero has no digits. Otherwise the precision
    // already supplies its required zero padding.
    auto nonzero_digit = builder.ugte(
      bool_sort, value, builder.constd(sort, mp_integer(1) << (4 * (n - 1))));
    length = builder.ite(
      sort, nonzero_digit, constant(std::max(n, precision)), length);
  }
  auto pointer_size = [&](btor2_nid_t n)
  {
    if(width < memory.heap.pointer_bits)
      return builder.uext(
        memory.heap.pointer_sort, n, memory.heap.pointer_bits - width);
    if(width > memory.heap.pointer_bits)
      return builder.slice(
        memory.heap.pointer_sort, n, memory.heap.pointer_bits - 1, 0);
    return n;
  };
  const auto saved_guard = memory.heap.path_guard;
  for(unsigned i = 0; i < std::max(digits, precision); ++i)
  {
    memory.heap.path_guard = builder.land(
      bool_sort, saved_guard, builder.ult(bool_sort, constant(i), length));
    const auto shift = builder.mul(
      sort, builder.sub(sort, length, constant(i + 1)), constant(4));
    const auto digit =
      builder.land(sort, builder.srl(sort, value, shift), constant(15));
    const auto character = builder.ite(
      sort,
      builder.ult(bool_sort, digit, constant(10)),
      builder.add(sort, digit, constant('0')),
      builder.add(sort, digit, constant((upper ? 'A' : 'a') - 10)));
    memory.heap.store(
      memory.heap.add_offset(
        destination, builder.constd(memory.heap.pointer_sort, i)),
      width == byte_width
        ? character
        : builder.slice(byte_sort, character, byte_width - 1, 0),
      byte_width);
  }
  memory.heap.path_guard = saved_guard;
  memory.heap.store(
    memory.heap.add_offset(destination, pointer_size(length)),
    builder.zero(byte_sort),
    byte_width);
  const auto &lhs = instruction.call_lhs();
  if(lhs.is_not_nil())
  {
    const auto lhs_width = expr_converter.get_width(lhs.type());
    if(!lhs_width || *lhs_width != width)
      conversion_error("Unexpected sprintf return width");
    else if(memory.owns_lvalue(lhs))
      memory.heap.store(memory.address(lhs), length, width);
    else
      state_updates[to_symbol_expr(lhs).get_identifier()].push_back(
        {at_loc, length});
  }
  add_pc_fallthrough(loc, at_loc);
  return true;
}
