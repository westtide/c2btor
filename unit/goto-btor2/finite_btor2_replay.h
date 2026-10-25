#ifndef CPROVER_UNIT_GOTO_BTOR2_FINITE_BTOR2_REPLAY_H
#define CPROVER_UNIT_GOTO_BTOR2_FINITE_BTOR2_REPLAY_H

#include <util/mp_arith.h>

#include <map>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <vector>

namespace btor2_test
{
// Evaluate a supplied finite input trace with simultaneous next-state updates.
// No path search, constraint solving or model checking is performed. Missing
// scalar/array evaluator support fails explicitly instead of guessing a value.
class trace_replayt
{
  struct array_valuet
  {
    mp_integer initial = 0;
    std::map<mp_integer, mp_integer> cells;
  };
  struct valuet
  {
    mp_integer bits = 0;
    std::shared_ptr<array_valuet> array;
  };
  struct nodet
  {
    std::string operation;
    unsigned sort = 0;
    std::vector<std::string> arguments;
  };
  std::map<unsigned, nodet> nodes;
  std::map<unsigned, unsigned> widths, array_elements, initializers,
    next_functions;
  std::map<unsigned, valuet> states, inputs, cache;

  mp_integer normalize(const mp_integer &value, unsigned sort) const
  {
    const mp_integer modulus = mp_integer(1) << widths.at(sort);
    return ((value % modulus) + modulus) % modulus;
  }
  mp_integer signed_value(const mp_integer &value, unsigned sort) const
  {
    const auto width = widths.at(sort);
    return value >= (mp_integer(1) << (width - 1))
             ? value - (mp_integer(1) << width)
             : value;
  }
  valuet at_sort(valuet value, unsigned sort) const
  {
    if(array_elements.count(sort))
    {
      if(!value.array)
      {
        value.array = std::make_shared<array_valuet>();
        value.array->initial = normalize(value.bits, array_elements.at(sort));
      }
    }
    else
      value.bits = normalize(value.bits, sort);
    return value;
  }
  valuet evaluate(unsigned id)
  {
    if(cache.count(id))
      return cache.at(id);
    const auto &node = nodes.at(id);
    auto argument = [&](unsigned i)
    { return evaluate(std::stoul(node.arguments.at(i))); };
    auto signed_argument = [&](unsigned i)
    {
      const auto nid = std::stoul(node.arguments.at(i));
      return signed_value(evaluate(nid).bits, nodes.at(nid).sort);
    };
    valuet value;
    const auto &op = node.operation;
    if(op == "state")
      value = states.at(id);
    else if(op == "input")
    {
      if(inputs.count(id))
        value = inputs.at(id);
    }
    else if(op == "zero")
      value.bits = 0;
    else if(op == "one")
      value.bits = 1;
    else if(op == "ones")
      value.bits = (mp_integer(1) << widths.at(node.sort)) - 1;
    else if(op == "constd")
      value.bits = string2integer(node.arguments.at(0));
    else if(op == "const" || op == "consth")
      value.bits = string2integer(node.arguments.at(0), op == "const" ? 2 : 16);
    else if(op == "ite")
      value = argument(0).bits != 0 ? argument(1) : argument(2);
    else if(op == "not")
      value.bits =
        (mp_integer(1) << widths.at(node.sort)) - 1 - argument(0).bits;
    else if(op == "and")
      value.bits = bitwise_and(argument(0).bits, argument(1).bits);
    else if(op == "or")
      value.bits = bitwise_or(argument(0).bits, argument(1).bits);
    else if(op == "xor")
      value.bits = bitwise_xor(argument(0).bits, argument(1).bits);
    else if(op == "eq" || op == "neq")
    {
      const auto lhs = argument(0), rhs = argument(1);
      if(lhs.array || rhs.array)
        throw std::logic_error(
          "native array equality is unsupported by finite replay");
      const bool equal = lhs.bits == rhs.bits;
      value.bits = op == "eq" ? equal : !equal;
    }
    else if(op == "add")
      value.bits = argument(0).bits + argument(1).bits;
    else if(op == "sub")
      value.bits = argument(0).bits - argument(1).bits;
    else if(op == "mul")
      value.bits = argument(0).bits * argument(1).bits;
    else if(op == "urem")
      value.bits = argument(1).bits == 0 ? argument(0).bits
                                         : argument(0).bits % argument(1).bits;
    else if(op == "udiv")
      value.bits = argument(1).bits == 0
                     ? (mp_integer(1) << widths.at(node.sort)) - 1
                     : argument(0).bits / argument(1).bits;
    else if(op == "sdiv")
    {
      const auto dividend = signed_argument(0);
      const auto divisor = signed_argument(1);
      if(divisor == 0)
        value.bits = dividend < 0 ? mp_integer(1)
                                 : (mp_integer(1) << widths.at(node.sort)) - 1;
      else
      {
        const auto magnitude =
          (dividend < 0 ? -dividend : dividend) /
          (divisor < 0 ? -divisor : divisor);
        value.bits = (dividend < 0) != (divisor < 0) ? -magnitude : magnitude;
      }
    }
    else if(op == "concat")
    {
      const auto lower = std::stoul(node.arguments.at(1));
      value.bits = (argument(0).bits << widths.at(nodes.at(lower).sort)) +
                   argument(1).bits;
    }
    else if(op == "ult")
      value.bits = argument(0).bits < argument(1).bits;
    else if(op == "ulte")
      value.bits = argument(0).bits <= argument(1).bits;
    else if(op == "ugt")
      value.bits = argument(0).bits > argument(1).bits;
    else if(op == "ugte")
      value.bits = argument(0).bits >= argument(1).bits;
    else if(op == "slt")
      value.bits = signed_argument(0) < signed_argument(1);
    else if(op == "slte")
      value.bits = signed_argument(0) <= signed_argument(1);
    else if(op == "sgt")
      value.bits = signed_argument(0) > signed_argument(1);
    else if(op == "sgte")
      value.bits = signed_argument(0) >= signed_argument(1);
    else if(op == "uext")
      value = argument(0);
    else if(op == "sext")
      value.bits = signed_argument(0);
    else if(op == "slice")
      value.bits = argument(0).bits >> std::stoul(node.arguments.at(2));
    else if(op == "sll" || op == "srl")
    {
      const auto amount = argument(1).bits;
      if(amount >= widths.at(node.sort))
        value.bits = 0;
      else if(op == "sll")
        value.bits = argument(0).bits << amount.to_ulong();
      else
        value.bits = argument(0).bits >> amount.to_ulong();
    }
    else if(op == "read")
    {
      const auto storage = argument(0).array;
      const auto index = argument(1).bits;
      value.bits = storage->cells.count(index) ? storage->cells.at(index)
                                               : storage->initial;
    }
    else if(op == "write")
    {
      value.array = std::make_shared<array_valuet>(*argument(0).array);
      value.array->cells[argument(1).bits] = argument(2).bits;
    }
    else
      throw std::logic_error("unsupported replay operation: " + op);
    return cache[id] = at_sort(std::move(value), node.sort);
  }

public:
  explicit trace_replayt(const std::string &model)
  {
    std::istringstream stream(model);
    std::string line;
    while(std::getline(stream, line))
    {
      std::istringstream words(line.substr(0, line.find(';')));
      unsigned id;
      nodet node;
      if(!(words >> id >> node.operation))
        continue;
      if(node.operation == "sort")
      {
        std::string kind;
        unsigned first, second;
        words >> kind >> first;
        if(kind == "bitvec")
          widths[id] = first;
        else if(kind == "array")
        {
          words >> second;
          array_elements[id] = second;
        }
        else
          throw std::logic_error("unsupported replay sort");
        continue;
      }
      if(
        node.operation == "output" || node.operation == "bad" ||
        node.operation == "constraint")
        continue;
      words >> node.sort;
      std::string word;
      while(words >> word)
        node.arguments.push_back(word);
      if(node.operation == "init" || node.operation == "next")
      {
        auto &functions =
          node.operation == "init" ? initializers : next_functions;
        functions[std::stoul(node.arguments.at(0))] =
          std::stoul(node.arguments.at(1));
      }
      else
      {
        if(node.operation == "state")
          states[id] = at_sort({}, node.sort);
        nodes.emplace(id, std::move(node));
      }
    }
    for(auto &entry : states)
      if(initializers.count(entry.first))
      {
        cache.clear();
        entry.second = at_sort(
          evaluate(initializers.at(entry.first)), nodes.at(entry.first).sort);
      }
    cache.clear();
  }
  void input(unsigned id, const mp_integer &value)
  {
    inputs[id] = at_sort({value, {}}, nodes.at(id).sort);
    cache.clear();
  }
  mp_integer value(unsigned id)
  {
    const auto result = evaluate(id);
    if(result.array)
      throw std::logic_error("array node requested as scalar observation");
    return result.bits;
  }
  void step()
  {
    auto updated = states;
    for(const auto &entry : next_functions)
      updated[entry.first] =
        at_sort(evaluate(entry.second), nodes.at(entry.first).sort);
    states = std::move(updated);
    cache.clear();
  }
};
} // namespace btor2_test

#endif
