#include "lower_array_operations.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <optional>

namespace
{
// Only a direct decay of an entire byte array establishes the intrinsic's
// extent here. Unknown roots and non-byte element types remain unsupported.
std::optional<exprt> byte_array_object(exprt pointer, const namespacet &ns)
{
  while(pointer.id() == ID_typecast)
    pointer = to_typecast_expr(pointer).op();
  if(pointer.id() != ID_address_of)
    return {};
  exprt object = to_address_of_expr(pointer).object();
  if(object.id() == ID_index)
  {
    const auto &index = to_index_expr(object);
    if(!simplify_expr(index.index(), ns).is_zero())
      return {};
    object = index.array();
  }
  if(object.type().id() != ID_array)
    return {};
  const auto &type = to_array_type(object.type());
  const auto &element = type.element_type();
  if(
    (element.id() != ID_signedbv && element.id() != ID_unsignedbv) ||
    to_bitvector_type(element).get_width() != 8 || type.size().is_nil())
    return {};
  return object;
}
} // namespace

void lower_array_operations(
  goto_programt &program,
  symbol_tablet &symbols,
  messaget &log,
  bool packed_copy)
{
  const namespacet ns(symbols);
  unsigned lowered = 0;
  for(auto it = program.instructions.begin(); it != program.instructions.end();)
  {
    auto next = std::next(it);
    if(!it->is_other())
    {
      it = next;
      continue;
    }
    const auto &code = it->get_other();
    const auto operation = code.get_statement();
    if(
      (operation != ID_array_set && operation != ID_array_copy &&
       operation != ID_array_replace) ||
      code.operands().size() != 2)
    {
      it = next;
      continue;
    }
    const exprt destination = code.op0();
    const exprt source = code.op1();
    const auto destination_object = byte_array_object(destination, ns);
    const auto source_object = operation == ID_array_set
                                 ? std::optional<exprt>{}
                                 : byte_array_object(source, ns);
    const auto &object =
      operation == ID_array_replace ? source_object : destination_object;
    if(!object && operation != ID_array_copy)
    {
      it = next;
      continue;
    }
    const auto location = it->source_location();
    // Dynamic array_copy (notably realloc) copies the common object prefix.
    // Both argument values and the length are locked into auxiliary states.
    auto extent = [](const exprt &pointer) -> exprt {
      return minus_exprt(object_size_exprt(pointer, size_type()),
        typecast_exprt(pointer_offset_exprt(pointer, pointer_diff_type()), size_type()));
    };
    exprt count;
    if(object)
      count = to_array_type(object->type()).size();
    if(operation == ID_array_copy)
    {
      auto dst_size = extent(destination);
      auto src_size = extent(source);
      count = if_exprt(binary_relation_exprt(dst_size, ID_lt, src_size),
        dst_size, src_size);
    }
    const auto array_type = array_typet(unsigned_char_type(), count);
    if(packed_copy && operation != ID_array_set)
    {
      // The original intrinsic is atomic. Evaluating both pointers and the
      // count before updating storage gives memmove its snapshot semantics.
      codet copy("c2btor_copy_range");
      copy.operands() = {destination, source, count};
      *it = goto_programt::make_other(copy, location);
    }
    else if(operation == ID_array_set && array_type.size().is_constant())
    {
      const auto value =
        typecast_exprt::conditional_cast(source, array_type.element_type());
      *it = goto_programt::make_assignment(
        *object, array_of_exprt(value, array_type), location);
    }
    else
    {
      goto_programt block;
      auto emit = [&](goto_programt::instructiont instruction)
      {
        auto target = block.add_instruction();
        *target = std::move(instruction);
        return target;
      };
      auto auxiliary = [&](const typet &type, const std::string &name)
      {
        auto symbol = get_fresh_aux_symbol(
                        type, "main", "btor_" + name, location, ID_C, symbols)
                        .symbol_expr();
        emit(goto_programt::make_decl(symbol, location));
        return symbol;
      };
      const auto size = auxiliary(size_type(), "copy_size");
      emit(
        goto_programt::make_assignment(
          size,
          typecast_exprt::conditional_cast(array_type.size(), size.type()),
          location));
      const auto byte_pointer_type = pointer_type(unsigned_char_type());
      const auto dst = auxiliary(byte_pointer_type, "copy_dst");
      emit(
        goto_programt::make_assignment(
          dst,
          typecast_exprt::conditional_cast(destination, byte_pointer_type),
          location));
      const auto index = auxiliary(size_type(), "copy_index");
      const auto zero = from_integer(0, size.type());
      const auto one = from_integer(1, size.type());
      auto byte = [&](const exprt &pointer)
      {
        return dereference_exprt(
          plus_exprt(pointer, index), unsigned_char_type());
      };
      // A named array has a stable base throughout the copy. Use its storage
      // directly instead of dispatching each byte over every tagged object.
      // More general lvalues still use the captured pointer (their base may
      // itself be stored in memory overwritten by this operation).
      auto element =
        [&](const std::optional<exprt> &array, const exprt &pointer) -> exprt
      {
        if(array && array->id() == ID_symbol)
        {
          const auto &type = to_array_type(array->type());
          return index_exprt(
            *array, typecast_exprt::conditional_cast(index, type.index_type()));
        }
        return byte(pointer);
      };
      auto loop = [&](const exprt &lhs, const exprt &rhs, bool copy = false)
      {
        emit(goto_programt::make_assignment(index, zero, location));
        const auto head = block.add_instruction(SKIP);
        head->source_location_nonconst() = location;
        const auto done = emit(
          goto_programt::make_goto(
            head, binary_relation_exprt(index, ID_ge, size), location));
        if(copy)
        {
          codet step("c2btor_copy_byte");
          step.add_to_operands(address_of_exprt(lhs), address_of_exprt(rhs));
          emit(goto_programt::make_other(step, location));
        }
        else
          emit(goto_programt::make_assignment(
            lhs, typecast_exprt::conditional_cast(rhs, lhs.type()), location));
        emit(
          goto_programt::make_assignment(
            index, plus_exprt(index, one), location));
        emit(goto_programt::make_goto(head, location));
        const auto end = block.add_instruction(SKIP);
        end->source_location_nonconst() = location;
        done->targets = {end};
      };
      if(operation == ID_array_set)
      {
        const auto value = auxiliary(unsigned_char_type(), "fill_value");
        emit(
          goto_programt::make_assignment(
            value,
            typecast_exprt::conditional_cast(source, value.type()),
            location));
        loop(element(destination_object, dst), value);
        emit(goto_programt::make_dead(value, location));
      }
      else
      {
        const auto src = auxiliary(byte_pointer_type, "copy_src");
        emit(
          goto_programt::make_assignment(
            src,
            typecast_exprt::conditional_cast(source, byte_pointer_type),
            location));
        const auto snapshot =
          auxiliary(array_typet(unsigned_char_type(), size), "copy_snapshot");
        loop(index_exprt(snapshot, index), element(source_object, src), true);
        loop(element(destination_object, dst), index_exprt(snapshot, index), true);
        emit(goto_programt::make_dead(snapshot, location));
        emit(goto_programt::make_dead(src, location));
      }
      for(const auto &symbol : {index, dst, size})
        emit(goto_programt::make_dead(symbol, location));
      it->turn_into_skip();
      program.insert_before_swap(it, block);
    }
    ++lowered;
    it = next;
  }
  program.update();
  log.status() << "Lowered " << lowered << " byte-array operations for BTOR2"
               << messaget::eom;
}
