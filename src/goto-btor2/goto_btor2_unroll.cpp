/*******************************************************************\

Module: Goto 程序常量界循环展开 - 实现

Author: Based on CBMC project

\*******************************************************************/

#include "goto_btor2_unroll.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/irep_ids.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/symbol.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <algorithm>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

namespace
{

constexpr std::size_t MAX_UNROLL_K = 64;

bool is_alloc_call(const goto_programt::instructiont &instr)
{
  if(instr.is_function_call())
  {
    const exprt &function = instr.call_function();
    irep_idt fid;
    if(function.id() == ID_symbol)
      fid = to_symbol_expr(function).get_identifier();
    else if(function.id() == ID_address_of)
    {
      const exprt &obj = function.operands().empty()
                           ? nil_exprt()
                           : function.operands()[0];
      if(obj.id() == ID_symbol)
        fid = to_symbol_expr(obj).get_identifier();
    }
    const std::string s = id2string(fid);
    const std::string malloc_suffix = "::malloc";
    const std::string calloc_suffix = "::calloc";
    return s == "malloc" || s == "calloc" ||
           (s.size() >= malloc_suffix.size() &&
            s.compare(
              s.size() - malloc_suffix.size(),
              malloc_suffix.size(),
              malloc_suffix) == 0) ||
           (s.size() >= calloc_suffix.size() &&
            s.compare(
              s.size() - calloc_suffix.size(),
              calloc_suffix.size(),
              calloc_suffix) == 0);
  }
  if(instr.is_assign())
  {
    const exprt &rhs = instr.assign_rhs();
    const exprt *cur = &rhs;
    while(cur->id() == ID_typecast)
      cur = &to_typecast_expr(*cur).op();
    return cur->id() == ID_side_effect &&
           to_side_effect_expr(*cur).get_statement() == ID_allocate;
  }
  return false;
}

std::optional<mp_integer> as_integer(const exprt &e)
{
  if(e.is_constant())
  {
    mp_integer v;
    if(!to_integer(to_constant_expr(e), v))
      return v;
  }
  return std::nullopt;
}

std::map<irep_idt, mp_integer> collect_constants(
  const std::vector<const goto_programt::instructiont *> &order,
  std::size_t stop_before)
{
  std::map<irep_idt, mp_integer> known;
  for(std::size_t i = 0; i < stop_before && i < order.size(); ++i)
  {
    const auto &ins = *order[i];
    // Only straight-line reaching constants are hints for the trip count.
    if(ins.is_target() || ins.is_goto() || ins.is_function_call())
      known.clear();
    if(ins.is_decl())
      known.erase(ins.decl_symbol().get_identifier());
    if(ins.is_dead())
      known.erase(ins.dead_symbol().get_identifier());
    if(ins.is_other())
      known.clear();
    if(!ins.is_assign())
      continue;
    const auto &lhs = ins.assign_lhs();
    if(lhs.id() != ID_symbol)
    {
      known.clear();
      continue;
    }
    const auto id = to_symbol_expr(lhs).get_identifier();
    const auto &rhs = ins.assign_rhs();
    if(auto value = as_integer(rhs))
      known[id] = *value;
    else if(rhs.id() == ID_symbol &&
            known.count(to_symbol_expr(rhs).get_identifier()))
      known[id] = known.at(to_symbol_expr(rhs).get_identifier());
    else
      known.erase(id);
  }
  return known;
}

struct parsed_guardt
{
  irep_idt var;
  irep_idt op;
  mp_integer threshold;
};

std::optional<parsed_guardt> parse_guard(const exprt &guard)
{
  if(guard.id() != ID_gt && guard.id() != ID_ge &&
     guard.id() != ID_lt && guard.id() != ID_le)
    return std::nullopt;
  const auto &g = to_binary_expr(guard);
  parsed_guardt r;
  r.op = g.id();
  if(g.op0().id() == ID_symbol && g.op1().is_constant())
  {
    r.var = to_symbol_expr(g.op0()).get_identifier();
    mp_integer v;
    if(to_integer(to_constant_expr(g.op1()), v))
      return std::nullopt;
    r.threshold = v;
    return r;
  }
  if(g.op1().id() == ID_symbol && g.op0().is_constant())
  {
    static const std::map<irep_idt, irep_idt> flip = {
      {ID_gt, ID_lt},
      {ID_lt, ID_gt},
      {ID_ge, ID_le},
      {ID_le, ID_ge},
    };
    r.var = to_symbol_expr(g.op1()).get_identifier();
    r.op = flip.at(g.id());
    mp_integer v;
    if(to_integer(to_constant_expr(g.op0()), v))
      return std::nullopt;
    r.threshold = v;
    return r;
  }
  return std::nullopt;
}

std::optional<mp_integer> find_induction_step(
  const std::vector<const goto_programt::instructiont *> &body,
  const irep_idt &var)
{
  int writes = 0;
  mp_integer step = 0;
  for(const auto *ins : body)
  {
    if(!ins->is_assign())
      continue;
    const exprt &lhs = ins->assign_lhs();
    if(lhs.id() != ID_symbol)
      continue;
    if(to_symbol_expr(lhs).get_identifier() != var)
      continue;
    writes++;
    const exprt &rhs = ins->assign_rhs();
    if(rhs.id() != ID_plus && rhs.id() != ID_minus)
      return std::nullopt;
    const auto &ops_r = rhs.operands();
    if(ops_r.size() != 2)
      return std::nullopt;
    const exprt *cst = nullptr;
    int sym_count = 0;
    for(const auto &op : ops_r)
    {
      if(op.id() == ID_symbol &&
         to_symbol_expr(op).get_identifier() == var)
        sym_count++;
      else if(as_integer(op).has_value())
        cst = &op;
    }
    if(sym_count != 1 || !cst ||
       (rhs.id() == ID_minus && ops_r[0].id() != ID_symbol))
      return std::nullopt;
    auto delta = *as_integer(*cst);
    mp_integer this_step = rhs.id() == ID_plus ? delta : -delta;
    if(this_step == 0)
      return std::nullopt;
    step = this_step;
  }
  if(writes != 1)
    return std::nullopt;
  return step;
}

mp_integer compute_K(const parsed_guardt &g, mp_integer init, mp_integer step)
{
  if(step == 0)
    return 0;
  mp_integer v = init;
  mp_integer k = 0;
  const mp_integer cap = static_cast<mp_integer>(MAX_UNROLL_K) + 1;
  while(k <= cap)
  {
    bool cont;
    if(g.op == ID_gt)
      cont = v > g.threshold;
    else if(g.op == ID_ge)
      cont = v >= g.threshold;
    else if(g.op == ID_lt)
      cont = v < g.threshold;
    else
      cont = v <= g.threshold;
    if(!cont)
      break;
    v += step;
    ++k;
  }
  return k;
}

} // namespace

//===========================================================================

std::size_t unroll_malloc_counted_loops(goto_modelt &goto_model, messaget &log)
{
  auto &fn_map = goto_model.goto_functions.function_map;
  auto fit = fn_map.find(ID_main);
  if(fit == fn_map.end())
    return 0;
  goto_programt &program = fit->second.body;
  namespacet ns(goto_model.symbol_table);

  std::size_t total = 0;
  for(int pass = 0; pass < 8; ++pass)
  {
    // 顺序 + 地址->位置
    std::vector<const goto_programt::instructiont *> order;
    order.reserve(program.instructions.size());
    std::map<const goto_programt::instructiont *, std::size_t> pos_of;
    std::size_t idx = 0;
    for(const auto &ins : program.instructions)
    {
      order.push_back(&ins);
      pos_of[&ins] = idx++;
    }
    const std::size_t n = order.size();
    if(n == 0)
      break;

    // 找可展开循环
    bool found = false;
    std::size_t head_pos = 0, back_pos = 0, exit_pos = 0;
    mp_integer K = 0;
    parsed_guardt pg{};

    for(std::size_t j = 0; j < n && !found; ++j)
    {
      const auto *b = order[j];
      if(!b->is_goto() || !b->condition().is_true() || b->targets.empty())
        continue;
      auto pit = pos_of.find(&*b->targets.front());
      if(pit == pos_of.end())
        continue;
      std::size_t head = pit->second;
      if(head >= j)
        continue;
      const auto *h = order[head];
      if(!h->is_goto() || h->condition().is_true() || h->targets.empty())
        continue;
      auto eit = pos_of.find(&*h->targets.front());
      if(eit == pos_of.end())
        continue;
      std::size_t exit_p = eit->second;
      if(exit_p != j + 1)
        continue;
      std::vector<const goto_programt::instructiont *> body(
        order.begin() + head + 1, order.begin() + j);
      if(!std::any_of(body.begin(), body.end(),
                      [](const auto *p) { return is_alloc_call(*p); }))
        continue;

      exprt cont = not_exprt(h->condition());
      simplify(cont, ns);
      auto pgg = parse_guard(cont);
      if(!pgg)
        continue;
      auto step_opt = find_induction_step(body, pgg->var);
      if(!step_opt)
        continue;
      auto known = collect_constants(order, head);
      auto vit = known.find(pgg->var);
      if(vit == known.end())
        continue;
      mp_integer k = compute_K(*pgg, vit->second, *step_opt);
      if(k < 1 || k > static_cast<mp_integer>(MAX_UNROLL_K))
        continue;

      // The induction variable must not wrap, be address-taken, or have its
      // increment bypassed on a path that reaches the back edge. Skip complex
      // loops rather than guessing a finite bound and truncating executions.
      const auto &var_type = ns.lookup(pgg->var).type;
      if(var_type.id() != ID_signedbv && var_type.id() != ID_unsignedbv)
        continue;
      const auto &bv_type = to_integer_bitvector_type(var_type);
      const auto final_value = vit->second + k * *step_opt;
      if(vit->second < bv_type.smallest() || vit->second > bv_type.largest() ||
         final_value < bv_type.smallest() || final_value > bv_type.largest())
        continue;
      bool simple = true;
      std::size_t increment = head;
      for(std::size_t i = head + 1; i < j; ++i)
        if(order[i]->is_assign() && order[i]->assign_lhs().id() == ID_symbol &&
           to_symbol_expr(order[i]->assign_lhs()).get_identifier() == pgg->var)
          increment = i;
      std::function<void(const exprt &, bool)> check_address =
        [&](const exprt &e, bool addressed) {
          addressed = addressed || e.id() == ID_address_of;
          if(addressed && e.id() == ID_symbol &&
             to_symbol_expr(e).get_identifier() == pgg->var)
            simple = false;
          for(const auto &op : e.operands())
            check_address(op, addressed);
        };
      for(std::size_t i = 0; i < n; ++i)
      {
        check_address(order[i]->code(), false);
        if(order[i]->has_condition())
          check_address(order[i]->condition(), false);
        if(i > head && i < j)
        {
          if(order[i]->is_function_call() || order[i]->is_other())
            simple = false;
          if(order[i]->is_decl() &&
             order[i]->decl_symbol().get_identifier() == pgg->var)
            simple = false;
          if(order[i]->is_dead() &&
             order[i]->dead_symbol().get_identifier() == pgg->var)
            simple = false;
        }
        for(const auto &target : order[i]->targets)
        {
          const auto tp = pos_of.at(&*target);
          if(i <= head || i > j)
          {
            if(tp > head && tp <= j)
              simple = false; // external entry into the body
          }
          else if(i < j && tp >= head && tp <= j)
          {
            if(tp <= i || (i < increment && tp > increment))
              simple = false; // nested cycle or bypass of increment
          }
        }
      }
      if(!simple)
        continue;

      head_pos = head;
      back_pos = j;
      exit_pos = exit_p;
      K = k;
      pg = *pgg;
      found = true;
    }
    if(!found)
      break;

    const std::size_t Ksize = static_cast<std::size_t>(K.to_long());

    // 捕获每条原始指令的目标位置（清空前）
    std::vector<std::vector<std::size_t>> orig_targets(n);
    for(std::size_t i = 0; i < n; ++i)
    {
      for(const auto &t : order[i]->targets)
      {
        auto it = pos_of.find(&*t);
        if(it != pos_of.end())
          orig_targets[i].push_back(it->second);
      }
    }

    // 构建 prog2
    goto_programt prog2;
    enum Kt
    {
      KEPT,
      HEAD_COPY,
      BODY_COPY
    };
    struct Meta
    {
      Kt kind;
      std::size_t orig_pos;
      std::size_t copy_i;
    };
    std::vector<goto_programt::targett> new_iters;
    std::vector<Meta> metas;
    std::map<std::size_t, goto_programt::targett> kept_map;
    std::map<std::size_t, goto_programt::targett> head_map;
    std::map<std::pair<std::size_t, std::size_t>, goto_programt::targett>
      body_map;

    auto append = [&](std::size_t i, std::size_t ci, Kt kind) {
      goto_programt::instructiont copy = *order[i];
      copy.targets.clear();
      copy.incoming_edges.clear();
      auto t = prog2.add(std::move(copy));
      new_iters.push_back(t);
      metas.push_back({kind, i, ci});
      if(kind == KEPT)
        kept_map[i] = t;
      else if(kind == HEAD_COPY)
        head_map[ci] = t;
      else
        body_map[{i, ci}] = t;
    };
    for(std::size_t i = 0; i < head_pos; ++i)
      append(i, 0, KEPT);
    // Copy whole iterations in execution order, not each instruction K times.
    for(std::size_t ci = 0; ci < Ksize; ++ci)
    {
      append(head_pos, ci, HEAD_COPY);
      for(std::size_t i = head_pos + 1; i < back_pos; ++i)
        append(i, ci, BODY_COPY);
    }
    for(std::size_t i = back_pos + 1; i < n; ++i)
      append(i, 0, KEPT);

    // 重接 targets
    for(std::size_t k = 0; k < new_iters.size(); ++k)
    {
      if(!new_iters[k]->is_goto() && !new_iters[k]->is_incomplete_goto())
        continue;
      const auto &m = metas[k];
      for(std::size_t tp : orig_targets[m.orig_pos])
      {
        goto_programt::targett resolved;
        bool ok = false;
        if(tp > head_pos && tp < back_pos)
        {
          // body 内：同 copy
          auto it = body_map.find({tp, m.copy_i});
          if(it != body_map.end())
          {
            resolved = it->second;
            ok = true;
          }
        }
        else if(tp == head_pos)
        {
          // An incoming edge from outside the loop starts at iteration zero.
          resolved = head_map[0];
          ok = true;
        }
        else if(tp == back_pos)
        {
          if(m.copy_i + 1 < Ksize)
            resolved = head_map[m.copy_i + 1];
          else
            resolved = kept_map[exit_pos];
          ok = true;
        }
        else
        {
          auto it = kept_map.find(tp);
          if(it != kept_map.end())
          {
            resolved = it->second;
            ok = true;
          }
        }
        if(ok)
          new_iters[k]->targets.push_back(resolved);
      }
    }

    prog2.update();
    program.instructions.swap(prog2.instructions);
    ++total;
    log.status() << "[goto-btor2-unroll] unrolled a counted loop (K=" << Ksize
                 << ") around '" << pg.var << "'" << messaget::eom;
  }
  return total;
}
