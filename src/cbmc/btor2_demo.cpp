/*******************************************************************\

Module: Demo BTOR2 Export (simple while-loop subset)

Author: 

\*******************************************************************/

#include "btor2_demo.h"

#include <goto-programs/goto_instruction_code.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/irep_ids.h>
#include <util/std_expr.h>


namespace
{

struct loop_spect
{
  irep_idt var_id;
  std::string var_name;
  std::size_t width = 0;
  bool is_signed = true;
  mp_integer init_value;
  mp_integer guard_const;
  bool guard_is_negated = false;
  mp_integer inc_value;
  mp_integer assert_value;
};

class btor2_buildert
{
public:
  unsigned sort_bitvec(std::size_t width)
  {
    return add_line("sort bitvec " + std::to_string(width));
  }

  unsigned state(unsigned sort_id, const std::string &name)
  {
    return add_line("state " + std::to_string(sort_id) + " " + name);
  }

  unsigned constd(unsigned sort_id, const mp_integer &value)
  {
    return add_line(
      "constd " + std::to_string(sort_id) + " " + integer2string(value));
  }

  unsigned init(unsigned sort_id, unsigned state_id, unsigned value_id)
  {
    return add_line(
      "init " + std::to_string(sort_id) + " " + std::to_string(state_id) +
      " " + std::to_string(value_id));
  }

  unsigned eq(unsigned sort_id, unsigned a, unsigned b)
  {
    return add_line(
      "eq " + std::to_string(sort_id) + " " + std::to_string(a) + " " +
      std::to_string(b));
  }

  unsigned add(unsigned sort_id, unsigned a, unsigned b)
  {
    return add_line(
      "add " + std::to_string(sort_id) + " " + std::to_string(a) + " " +
      std::to_string(b));
  }

  unsigned lt(const std::string &op, unsigned sort_id, unsigned a, unsigned b)
  {
    return add_line(
      op + " " + std::to_string(sort_id) + " " + std::to_string(a) + " " +
      std::to_string(b));
  }

  unsigned land(unsigned sort_id, unsigned a, unsigned b)
  {
    return add_line(
      "and " + std::to_string(sort_id) + " " + std::to_string(a) + " " +
      std::to_string(b));
  }

  unsigned lnot(unsigned sort_id, unsigned a)
  {
    return add_line(
      "not " + std::to_string(sort_id) + " " + std::to_string(a));
  }

  unsigned ite(unsigned sort_id, unsigned cond, unsigned t, unsigned f)
  {
    return add_line(
      "ite " + std::to_string(sort_id) + " " + std::to_string(cond) + " " +
      std::to_string(t) + " " + std::to_string(f));
  }

  unsigned next(unsigned sort_id, unsigned state_id, unsigned value_id)
  {
    return add_line(
      "next " + std::to_string(sort_id) + " " + std::to_string(state_id) +
      " " + std::to_string(value_id));
  }

  unsigned bad(unsigned cond_id)
  {
    return add_line("bad " + std::to_string(cond_id));
  }

  void write(std::ostream &out) const
  {
    for(const auto &line : lines)
      out << line << '\n';
  }

private:
  unsigned next_id = 1;
  std::vector<std::string> lines;

  unsigned add_line(const std::string &line)
  {
    const unsigned id = next_id++;
    lines.push_back(std::to_string(id) + " " + line);
    return id;
  }
};

std::string normalize_symbol_name(const irep_idt &id)
{
  std::string name = id2string(id);
  const std::string::size_type pos = name.rfind("::");
  if(pos != std::string::npos)
    name = name.substr(pos + 2);
  for(char &ch : name)
  {
    if(ch == '\'')
      ch = '_';
  }
  return name;
}

bool get_constant(const exprt &expr, mp_integer &value)
{
  const exprt &bare = skip_typecast(expr);
  if(bare.id() != ID_constant)
    return false;
  if(to_integer(to_constant_expr(bare), value))
    return false;
  return true;
}

bool get_symbol(const exprt &expr, irep_idt &id)
{
  const exprt &bare = skip_typecast(expr);
  if(bare.id() != ID_symbol)
    return false;
  id = to_symbol_expr(bare).get_identifier();
  return true;
}

bool parse_guard(
  const exprt &expr,
  const irep_idt &var_id,
  mp_integer &limit,
  bool &negated)
{
  const exprt &bare = skip_typecast(expr);
  if(bare.id() == ID_not)
  {
    negated = !negated;
    return parse_guard(to_not_expr(bare).op(), var_id, limit, negated);
  }

  if(bare.id() == ID_lt || bare.id() == ID_ge)
  {
    const auto &rel = to_binary_relation_expr(bare);
    irep_idt lhs_id;
    mp_integer rhs_value;
    if(!get_symbol(rel.lhs(), lhs_id) || lhs_id != var_id)
      return false;
    if(!get_constant(rel.rhs(), rhs_value))
      return false;
    if(bare.id() == ID_ge)
      negated = !negated;
    limit = rhs_value;
    return true;
  }

  return false;
}

bool is_overflow_assert(const exprt &expr)
{
  const exprt &bare = skip_typecast(expr);
  if(bare.id() == ID_not)
  {
    const exprt &op = skip_typecast(to_not_expr(bare).op());
    return op.id() == ID_overflow_plus;
  }
  return false;
}

bool parse_assignment(
  const code_assignt &assign,
  const irep_idt &var_id,
  mp_integer &init_value,
  bool &has_init,
  mp_integer &inc_value,
  bool &has_inc)
{
  const exprt &lhs = skip_typecast(assign.lhs());
  if(lhs.id() != ID_symbol)
    return false;
  if(to_symbol_expr(lhs).get_identifier() != var_id)
    return false;

  const exprt &rhs = skip_typecast(assign.rhs());
  mp_integer value;
  if(!has_init && get_constant(rhs, value))
  {
    init_value = value;
    has_init = true;
    return true;
  }

  if(rhs.id() == ID_plus && rhs.operands().size() == 2)
  {
    const auto &binary_rhs = to_binary_expr(rhs);
    const exprt &op0 = skip_typecast(binary_rhs.op0());
    const exprt &op1 = skip_typecast(binary_rhs.op1());
    irep_idt id0;
    mp_integer rhs_const;
    if(get_symbol(op0, id0) && id0 == var_id && get_constant(op1, rhs_const))
    {
      inc_value = rhs_const;
      has_inc = true;
      return true;
    }
    if(get_symbol(op1, id0) && id0 == var_id && get_constant(op0, rhs_const))
    {
      inc_value = rhs_const;
      has_inc = true;
      return true;
    }
  }

  return false;
}

bool parse_assert(
  const exprt &expr,
  const irep_idt &var_id,
  mp_integer &assert_value)
{
  const exprt &bare = skip_typecast(expr);
  if(bare.id() != ID_equal)
    return false;
  const auto &eq = to_equal_expr(bare);
  irep_idt lhs_id;
  mp_integer rhs_value;
  if(get_symbol(eq.lhs(), lhs_id) && lhs_id == var_id &&
     get_constant(eq.rhs(), rhs_value))
  {
    assert_value = rhs_value;
    return true;
  }
  if(get_symbol(eq.rhs(), lhs_id) && lhs_id == var_id &&
     get_constant(eq.lhs(), rhs_value))
  {
    assert_value = rhs_value;
    return true;
  }
  return false;
}

bool parse_main_loop(
  const goto_programt &program,
  loop_spect &spec,
  messaget &log)
{
  bool has_var = false;
  bool has_init = false;
  bool has_guard = false;
  bool has_inc = false;
  bool has_assert = false;

  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_decl())
    {
      const auto &decl = to_code_decl(instruction.code());
      const auto &sym = decl.symbol();
      if(!has_var)
      {
        spec.var_id = sym.get_identifier();
        spec.var_name = normalize_symbol_name(spec.var_id);
        const auto &type = sym.type();
        if(can_cast_type<signedbv_typet>(type))
        {
          spec.is_signed = true;
          spec.width = to_signedbv_type(type).get_width();
        }
        else if(can_cast_type<unsignedbv_typet>(type))
        {
          spec.is_signed = false;
          spec.width = to_unsignedbv_type(type).get_width();
        }
        else
        {
          log.error() << "btor2-demo only supports signed/unsigned bitvector "
                         "variables in main()"
                      << messaget::eom;
          return false;
        }
        has_var = true;
      }
      continue;
    }

    if(instruction.is_assign() && has_var)
    {
      if(parse_assignment(
           to_code_assign(instruction.code()),
           spec.var_id,
           spec.init_value,
           has_init,
           spec.inc_value,
           has_inc))
      {
        continue;
      }
    }

    if(instruction.is_goto() && has_var)
    {
      if(instruction.condition().is_true())
        continue;
      if(instruction.is_backwards_goto())
        continue;
      if(parse_guard(
           instruction.condition(),
           spec.var_id,
           spec.guard_const,
           spec.guard_is_negated))
      {
        has_guard = true;
      }
      continue;
    }

    if(instruction.is_assert() && has_var)
    {
      if(is_overflow_assert(instruction.condition()))
        continue;
      if(parse_assert(
           instruction.condition(),
           spec.var_id,
           spec.assert_value))
      {
        has_assert = true;
      }
      continue;
    }
  }

  if(!has_var || !has_init || !has_guard || !has_inc || !has_assert)
  {
    log.error() << "btor2-demo requires: int x=const; while(x<k) x=x+c; "
                   "assert(x==c);"
                << messaget::eom;
    return false;
  }

  return true;
}

void emit_btor2(const loop_spect &spec, std::ostream &out)
{
  btor2_buildert b;

  const unsigned sort_bool = b.sort_bitvec(1);
  const unsigned sort_int = b.sort_bitvec(spec.width);

  const unsigned x_state = b.state(sort_int, spec.var_name);
  const unsigned pc_state = b.state(sort_bool, "pc");

  const unsigned const_x_init = b.constd(sort_int, spec.init_value);
  const unsigned const_pc0 = b.constd(sort_bool, 0);
  b.init(sort_int, x_state, const_x_init);
  b.init(sort_bool, pc_state, const_pc0);

  const unsigned const_guard = b.constd(sort_int, spec.guard_const);
  const std::string lt_op = spec.is_signed ? "slt" : "ult";
  const unsigned x_lt = b.lt(lt_op, sort_bool, x_state, const_guard);
  const unsigned x_ge = b.lnot(sort_bool, x_lt);
  const unsigned pc_is_0 = b.eq(sort_bool, pc_state, const_pc0);

  const unsigned take_cond = spec.guard_is_negated ? x_lt : x_ge;
  const unsigned exit_cond = spec.guard_is_negated ? x_ge : x_lt;

  const unsigned take_loop = b.land(sort_bool, pc_is_0, take_cond);
  const unsigned exit_loop = b.land(sort_bool, pc_is_0, exit_cond);

  const unsigned const_inc = b.constd(sort_int, spec.inc_value);
  const unsigned x_plus = b.add(sort_int, x_state, const_inc);
  const unsigned x_next = b.ite(sort_int, take_loop, x_plus, x_state);

  const unsigned const_pc1 = b.constd(sort_bool, 1);
  const unsigned pc_next = b.ite(sort_bool, exit_loop, const_pc1, pc_state);

  b.next(sort_int, x_state, x_next);
  b.next(sort_bool, pc_state, pc_next);

  const unsigned pc_is_1 = b.eq(sort_bool, pc_state, const_pc1);
  const unsigned const_assert = b.constd(sort_int, spec.assert_value);
  const unsigned x_eq_assert = b.eq(sort_bool, x_state, const_assert);
  const unsigned x_ne_assert = b.lnot(sort_bool, x_eq_assert);
  const unsigned bad_cond = b.land(sort_bool, pc_is_1, x_ne_assert);
  b.bad(bad_cond);

  out << "; BTOR2 demo (simple while-loop)\n";
  b.write(out);
}

} // namespace

bool write_btor2_demo(
  const goto_modelt &goto_model,
  std::ostream &out,
  messaget &log)
{
  const auto &functions = goto_model.get_goto_functions().function_map;
  const auto it = functions.find(ID_main);
  if(it == functions.end())
  {
    log.error() << "btor2-demo expects a main() function" << messaget::eom;
    return true;
  }

  loop_spect spec;
  if(!parse_main_loop(it->second.body, spec, log))
    return true;

  emit_btor2(spec, out);
  return false;
}
