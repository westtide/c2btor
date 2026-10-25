// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

/*******************************************************************\

Module: BTOR2 构建器实现

Authors: C2BTOR contributors; CBMC attribution is retained in LICENSES/

\*******************************************************************/

/// \file
/// BTOR2 构建器实现
///
/// 本文件实现了 btor2_buildert 类的所有方法。
/// 每个方法负责生成一条 BTOR2 指令，并返回该指令的节点 ID。
///
/// BTOR2 指令格式：
///   <nid> <op> <参数...> [<名称/注释>]
///
/// 其中 nid 是递增的正整数，op 是操作符名称。

#include "btor2_builder.h"

#include <util/arith_tools.h>

#include <limits>
#include <sstream>
#include <stdexcept>

//=============================================================================
// 辅助方法
//=============================================================================

/// 添加一行 BTOR2 指令
/// @param line 指令内容（不包含 nid 前缀）
/// @return 分配给该指令的节点 ID
btor2_nid_t btor2_buildert::add_line(const std::string &line)
{
  const btor2_nid_t nid = next_nid++;
  lines.push_back(std::to_string(nid) + " " + line);
  return nid;
}

/// 添加原始行（不带 nid，用于注释）
/// @param line 完整的行内容
void btor2_buildert::add_raw_line(const std::string &line)
{
  lines.push_back(line);
}

//=============================================================================
// 类型定义操作
//=============================================================================

/// 创建位向量类型
/// 生成：<nid> sort bitvec <width>
btor2_nid_t btor2_buildert::sort_bitvec(std::size_t width)
{
  return add_line("sort bitvec " + std::to_string(width));
}

/// 创建数组类型
/// 生成：<nid> sort array <index_sort> <element_sort>
btor2_nid_t
btor2_buildert::sort_array(btor2_nid_t index_sort, btor2_nid_t element_sort)
{
  emitted_array_sort = true;
  return add_line(
    "sort array " + std::to_string(index_sort) + " " +
    std::to_string(element_sort));
}

/// 获取或创建位向量类型（带缓存）
/// 避免为相同宽度重复创建类型
btor2_nid_t btor2_buildert::get_or_create_bitvec_sort(std::size_t width)
{
  auto it = bitvec_sort_cache.find(width);
  if(it != bitvec_sort_cache.end())
    return it->second;

  btor2_nid_t nid = sort_bitvec(width);
  bitvec_sort_cache[width] = nid;
  return nid;
}

/// 获取布尔类型（1 位位向量）
btor2_nid_t btor2_buildert::get_bool_sort()
{
  return get_or_create_bitvec_sort(1);
}

//=============================================================================
// 常量操作
//=============================================================================

/// 创建十进制常量
/// 生成：<nid> constd <sort_nid> <value>
btor2_nid_t btor2_buildert::constd(btor2_nid_t sort_nid, const mp_integer &value)
{
  return add_line("constd " + std::to_string(sort_nid) + " " + integer2string(value));
}

/// 创建二进制常量
/// 生成：<nid> const <sort_nid> <bits>
btor2_nid_t
btor2_buildert::const_binary(btor2_nid_t sort_nid, const std::string &bits)
{
  return add_line("const " + std::to_string(sort_nid) + " " + bits);
}

/// 创建十六进制常量
/// 生成：<nid> consth <sort_nid> <hex>
btor2_nid_t
btor2_buildert::consth(btor2_nid_t sort_nid, const std::string &hex)
{
  return add_line("consth " + std::to_string(sort_nid) + " " + hex);
}

/// 创建零常量
/// 生成：<nid> zero <sort_nid>
btor2_nid_t btor2_buildert::zero(btor2_nid_t sort_nid)
{
  return add_line("zero " + std::to_string(sort_nid));
}

/// 创建常量 1
/// 生成：<nid> one <sort_nid>
btor2_nid_t btor2_buildert::one(btor2_nid_t sort_nid)
{
  return add_line("one " + std::to_string(sort_nid));
}

/// 创建全 1 常量
/// 生成：<nid> ones <sort_nid>
btor2_nid_t btor2_buildert::ones(btor2_nid_t sort_nid)
{
  return add_line("ones " + std::to_string(sort_nid));
}

//=============================================================================
// 状态和输入变量操作
//=============================================================================

/// 创建状态变量
/// 生成：<nid> state <sort_nid> [<name>]
std::string btor2_buildert::unique_symbol(const std::string &name)
{
  if(name.empty() || used_symbols.insert(name).second)
    return name;
  auto &suffix = next_symbol_suffix[name];
  if(suffix < 2)
    suffix = 2;
  std::string candidate;
  do
  {
    candidate = name + "__" + std::to_string(suffix++);
  } while(!used_symbols.insert(candidate).second);
  return candidate;
}

btor2_nid_t btor2_buildert::state(
  btor2_nid_t sort_nid,
  const std::string &name,
  const std::string &source_symbol)
{
  std::string line = "state " + std::to_string(sort_nid);
  if(!name.empty())
    line += " " + unique_symbol(name);
  const auto nid = add_line(line);
  if(!source_symbol.empty())
  {
    // Hex encoding keeps arbitrary source identifiers on one comment line.
    const char *hex = "0123456789abcdef";
    std::string encoded;
    for(unsigned char c : source_symbol)
    {
      encoded += hex[c >> 4];
      encoded += hex[c & 15];
    }
    comment("c2btor-source " + std::to_string(nid) + " " + encoded);
  }
  return nid;
}

/// 创建输入变量
/// 生成：<nid> input <sort_nid> [<name>]
btor2_nid_t btor2_buildert::input(btor2_nid_t sort_nid, const std::string &name)
{
  std::string line = "input " + std::to_string(sort_nid);
  if(!name.empty())
    line += " " + unique_symbol(name);
  return add_line(line);
}

/// 初始化状态变量
/// 生成：<nid> init <sort_nid> <state_nid> <value_nid>
/// 注意：BTOR2 要求 state_nid > value_nid
btor2_nid_t btor2_buildert::init(
  btor2_nid_t sort_nid,
  btor2_nid_t state_nid,
  btor2_nid_t value_nid)
{
  return add_line(
    "init " + std::to_string(sort_nid) + " " + std::to_string(state_nid) + " " +
    std::to_string(value_nid));
}

/// 设置状态变量的下一个值
/// 生成：<nid> next <sort_nid> <state_nid> <value_nid>
btor2_nid_t btor2_buildert::next(
  btor2_nid_t sort_nid,
  btor2_nid_t state_nid,
  btor2_nid_t value_nid)
{
  return add_line(
    "next " + std::to_string(sort_nid) + " " + std::to_string(state_nid) + " " +
    std::to_string(value_nid));
}

//=============================================================================
// 通用运算符生成
//=============================================================================

/// 通用一元运算符
/// 生成：<nid> <op> <sort_nid> <a>
btor2_nid_t btor2_buildert::unary_op(
  const std::string &op,
  btor2_nid_t sort_nid,
  btor2_nid_t a)
{
  return add_line(op + " " + std::to_string(sort_nid) + " " + std::to_string(a));
}

/// 通用二元运算符
/// 生成：<nid> <op> <sort_nid> <a> <b>
btor2_nid_t btor2_buildert::binary_op(
  const std::string &op,
  btor2_nid_t sort_nid,
  btor2_nid_t a,
  btor2_nid_t b)
{
  return add_line(
    op + " " + std::to_string(sort_nid) + " " + std::to_string(a) + " " +
    std::to_string(b));
}

//=============================================================================
// 一元运算符
//=============================================================================

/// 逻辑非（按位取反）
btor2_nid_t btor2_buildert::lnot(btor2_nid_t sort_nid, btor2_nid_t a)
{
  return unary_op("not", sort_nid, a);
}

/// 算术取反
btor2_nid_t btor2_buildert::neg(btor2_nid_t sort_nid, btor2_nid_t a)
{
  return unary_op("neg", sort_nid, a);
}

/// 归约与
btor2_nid_t btor2_buildert::redand(btor2_nid_t sort_nid, btor2_nid_t a)
{
  return unary_op("redand", sort_nid, a);
}

/// 归约或
btor2_nid_t btor2_buildert::redor(btor2_nid_t sort_nid, btor2_nid_t a)
{
  return unary_op("redor", sort_nid, a);
}

/// 归约异或
btor2_nid_t btor2_buildert::redxor(btor2_nid_t sort_nid, btor2_nid_t a)
{
  return unary_op("redxor", sort_nid, a);
}

//=============================================================================
// 二元算术运算符
//=============================================================================

/// 加法
btor2_nid_t
btor2_buildert::add(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("add", sort_nid, a, b);
}

/// 减法
btor2_nid_t
btor2_buildert::sub(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("sub", sort_nid, a, b);
}

/// 乘法
btor2_nid_t
btor2_buildert::mul(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("mul", sort_nid, a, b);
}

/// 有符号除法
btor2_nid_t
btor2_buildert::sdiv(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("sdiv", sort_nid, a, b);
}

/// 无符号除法
btor2_nid_t
btor2_buildert::udiv(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("udiv", sort_nid, a, b);
}

/// 有符号取余
btor2_nid_t
btor2_buildert::srem(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("srem", sort_nid, a, b);
}

/// 无符号取余
btor2_nid_t
btor2_buildert::urem(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("urem", sort_nid, a, b);
}

/// 有符号取模
btor2_nid_t
btor2_buildert::smod(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("smod", sort_nid, a, b);
}

//=============================================================================
// 二元逻辑运算符
//=============================================================================

/// 按位与
btor2_nid_t
btor2_buildert::land(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("and", sort_nid, a, b);
}

/// 按位或
btor2_nid_t
btor2_buildert::lor(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("or", sort_nid, a, b);
}

/// 按位异或
btor2_nid_t
btor2_buildert::lxor(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("xor", sort_nid, a, b);
}

/// 按位与非
btor2_nid_t
btor2_buildert::nand_op(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("nand", sort_nid, a, b);
}

/// 按位或非
btor2_nid_t
btor2_buildert::nor_op(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("nor", sort_nid, a, b);
}

/// 按位同或
btor2_nid_t
btor2_buildert::xnor_op(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("xnor", sort_nid, a, b);
}

//=============================================================================
// 比较运算符
//=============================================================================

/// 相等比较
btor2_nid_t
btor2_buildert::eq(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("eq", sort_nid, a, b);
}

/// 不等比较
btor2_nid_t
btor2_buildert::neq(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("neq", sort_nid, a, b);
}

/// 有符号小于
btor2_nid_t
btor2_buildert::slt(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("slt", sort_nid, a, b);
}

/// 无符号小于
btor2_nid_t
btor2_buildert::ult(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("ult", sort_nid, a, b);
}

/// 有符号小于等于
btor2_nid_t
btor2_buildert::slte(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("slte", sort_nid, a, b);
}

/// 无符号小于等于
btor2_nid_t
btor2_buildert::ulte(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("ulte", sort_nid, a, b);
}

/// 有符号大于
btor2_nid_t
btor2_buildert::sgt(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("sgt", sort_nid, a, b);
}

/// 无符号大于
btor2_nid_t
btor2_buildert::ugt(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("ugt", sort_nid, a, b);
}

/// 有符号大于等于
btor2_nid_t
btor2_buildert::sgte(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("sgte", sort_nid, a, b);
}

/// 无符号大于等于
btor2_nid_t
btor2_buildert::ugte(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("ugte", sort_nid, a, b);
}

//=============================================================================
// 移位运算符
//=============================================================================

/// 逻辑左移
btor2_nid_t
btor2_buildert::sll(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("sll", sort_nid, a, b);
}

/// 逻辑右移
btor2_nid_t
btor2_buildert::srl(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("srl", sort_nid, a, b);
}

/// 算术右移（保持符号位）
btor2_nid_t
btor2_buildert::sra(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("sra", sort_nid, a, b);
}

/// 循环左移
btor2_nid_t
btor2_buildert::rol(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("rol", sort_nid, a, b);
}

/// 循环右移
btor2_nid_t
btor2_buildert::ror(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("ror", sort_nid, a, b);
}

//=============================================================================
// 位操作
//=============================================================================

/// 位拼接
/// 生成：<nid> concat <sort_nid> <a> <b>
/// 结果是 a 在高位，b 在低位
btor2_nid_t
btor2_buildert::concat(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("concat", sort_nid, a, b);
}

/// 位提取/切片
/// 生成：<nid> slice <sort_nid> <a> <upper> <lower>
/// 提取 a 的 [upper:lower] 位
btor2_nid_t btor2_buildert::slice(
  btor2_nid_t sort_nid,
  btor2_nid_t a,
  unsigned upper,
  unsigned lower)
{
  INVARIANT(
    is_bitvec_sort(sort_nid),
    "slice requires a bitvec sort, not array");
  return add_line(
    "slice " + std::to_string(sort_nid) + " " + std::to_string(a) + " " +
    std::to_string(upper) + " " + std::to_string(lower));
}

/// 符号扩展
/// 生成：<nid> sext <sort_nid> <a> <w>
/// 将 a 符号扩展 w 位
btor2_nid_t
btor2_buildert::sext(btor2_nid_t sort_nid, btor2_nid_t a, unsigned w)
{
  INVARIANT(
    is_bitvec_sort(sort_nid),
    "sext requires a bitvec sort, not array");
  return add_line(
    "sext " + std::to_string(sort_nid) + " " + std::to_string(a) + " " +
    std::to_string(w));
}

/// 无符号扩展（零扩展）
/// 生成：<nid> uext <sort_nid> <a> <w>
/// 将 a 零扩展 w 位
btor2_nid_t
btor2_buildert::uext(btor2_nid_t sort_nid, btor2_nid_t a, unsigned w)
{
  INVARIANT(
    is_bitvec_sort(sort_nid),
    "uext requires a bitvec sort, not array");
  return add_line(
    "uext " + std::to_string(sort_nid) + " " + std::to_string(a) + " " +
    std::to_string(w));
}

//=============================================================================
// 条件表达式
//=============================================================================

/// 条件选择（三目运算符）
/// 生成：<nid> ite <sort_nid> <cond> <then_val> <else_val>
/// 语义：cond ? then_val : else_val
btor2_nid_t btor2_buildert::ite(
  btor2_nid_t sort_nid,
  btor2_nid_t cond,
  btor2_nid_t then_val,
  btor2_nid_t else_val)
{
  return add_line(
    "ite " + std::to_string(sort_nid) + " " + std::to_string(cond) + " " +
    std::to_string(then_val) + " " + std::to_string(else_val));
}

/// 逻辑蕴含
/// 语义：a → b (等价于 ¬a ∨ b)
btor2_nid_t
btor2_buildert::implies(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("implies", sort_nid, a, b);
}

/// 逻辑等价
/// 语义：a ↔ b
btor2_nid_t
btor2_buildert::iff(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b)
{
  return binary_op("iff", sort_nid, a, b);
}

//=============================================================================
// 数组操作
//=============================================================================

/// 数组读取
/// 生成：<nid> read <element_sort> <array> <index>
/// 语义：array[index]
btor2_nid_t
btor2_buildert::read(btor2_nid_t sort_nid, btor2_nid_t array, btor2_nid_t index)
{
  return binary_op("read", sort_nid, array, index);
}

/// 数组写入
/// 生成：<nid> write <array_sort> <array> <index> <value>
/// 语义：创建新数组，其中 array[index] = value
btor2_nid_t btor2_buildert::write(
  btor2_nid_t sort_nid,
  btor2_nid_t array,
  btor2_nid_t index,
  btor2_nid_t value)
{
  return add_line(
    "write " + std::to_string(sort_nid) + " " + std::to_string(array) + " " +
    std::to_string(index) + " " + std::to_string(value));
}

//=============================================================================
// 属性定义
//=============================================================================

/// 定义坏状态（安全属性违反）
/// 生成：<nid> bad <cond> [<comment>]
/// 语义：如果 cond 在某个可达状态下为真，则表示安全属性被违反
/// 模型检测器会尝试找到一条到达 bad 状态的路径
btor2_nid_t btor2_buildert::bad(btor2_nid_t cond, const std::string &comment)
{
  std::string line = "bad " + std::to_string(cond);
  if(!comment.empty())
    line += " " + unique_symbol(comment);
  return add_line(line);
}

/// 添加约束
/// 生成：<nid> constraint <cond> [<comment>]
/// 语义：假设 cond 在所有时刻都为真
/// 模型检测器会排除违反约束的执行路径
btor2_nid_t
btor2_buildert::constraint(btor2_nid_t cond, const std::string &comment)
{
  std::string line = "constraint " + std::to_string(cond);
  if(!comment.empty())
    line += " " + unique_symbol(comment);
  return add_line(line);
}

/// 定义公平条件（用于活性属性验证）
/// 生成：<nid> fair <cond> [<comment>]
btor2_nid_t btor2_buildert::fair(btor2_nid_t cond, const std::string &comment)
{
  std::string line = "fair " + std::to_string(cond);
  if(!comment.empty())
    line += " " + unique_symbol(comment);
  return add_line(line);
}

/// 定义输出
/// 生成：<nid> output <value> [<comment>]
btor2_nid_t btor2_buildert::observed_output(
  btor2_nid_t sort, btor2_nid_t value, const std::string &name)
{
  const auto mask = ones(sort);
  const auto signal = add_line(
    "and " + std::to_string(sort) + " " + std::to_string(value) + " " +
    std::to_string(mask) + " " + unique_symbol(name));
  return output(signal);
}

btor2_nid_t btor2_buildert::output(btor2_nid_t value, const std::string &comment)
{
  std::string line = "output " + std::to_string(value);
  if(!comment.empty())
    line += " " + unique_symbol(comment);
  return add_line(line);
}

//=============================================================================
// 辅助方法
//=============================================================================

/// 添加注释行
/// 生成：; <text>
void btor2_buildert::comment(const std::string &text)
{
  add_raw_line("; " + text);
}

// Only heap_modelt registers these internal initializers. Source variables
// continue using init(), so their observable initial relationships are kept.
btor2_nid_t btor2_buildert::memory_init(
  btor2_nid_t sort, btor2_nid_t state, btor2_nid_t value)
{
  const auto id = init(sort, state, value);
  memory_initializers.insert(id);
  return id;
}

std::size_t btor2_buildert::simplify_memory_initializers()
{
  if(memory_initializers.empty() || !emitted_array_sort)
    return 0;

  struct nodet
  {
    std::string op;
    btor2_nid_t sort = 0;
    std::vector<btor2_nid_t> operands;
    std::size_t line = 0;
  };
  std::map<btor2_nid_t, nodet> nodes;
  std::map<btor2_nid_t, std::vector<btor2_nid_t>> uses, inits, nexts;
  std::map<btor2_nid_t, btor2_nid_t> array_elements;
  const std::set<std::string> literals = {
    "zero", "one", "ones", "const", "constd", "consth"};
  const std::set<std::string> unary = {
    "not", "neg", "redand", "redor", "redxor", "slice", "uext", "sext"};
  const std::set<std::string> binary = {
    "add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "smod",
    "and", "or", "xor", "nand", "nor", "xnor", "eq", "neq", "slt",
    "ult", "slte", "ulte", "sgt", "ugt", "sgte", "ugte", "sll",
    "srl", "sra", "rol", "ror", "concat", "implies", "iff", "read",
    "init", "next"};

  // Analyze the complete graph before changing any line. Operand positions
  // deliberately exclude constants, widths, slice bounds and optional names.
  // A future unsupported opcode disables this pass instead of hiding a use.
  for(std::size_t i = 0; i < lines.size(); ++i)
  {
    std::istringstream input(lines[i]);
    input >> std::ws;
    if(input.peek() == ';' || input.peek() == std::char_traits<char>::eof())
      continue;
    btor2_nid_t id;
    nodet node;
    node.line = i;
    if(!(input >> id >> node.op))
      return 0;
    if(node.op == "sort")
    {
      std::string kind;
      if(!(input >> kind))
        return 0;
      if(kind == "array")
      {
        btor2_nid_t index, element;
        if(!(input >> index >> element))
          return 0;
        array_elements[id] = element;
      }
      else if(kind != "bitvec")
        return 0;
      continue;
    }
    unsigned arity;
    if(node.op == "bad" || node.op == "constraint" ||
       node.op == "output" || node.op == "fair")
      arity = 1;
    else
    {
      if(!(input >> node.sort))
        return 0;
      if(literals.count(node.op) || node.op == "state" || node.op == "input")
        arity = 0;
      else if(unary.count(node.op))
        arity = 1;
      else if(binary.count(node.op))
        arity = 2;
      else if(node.op == "ite" || node.op == "write")
        arity = 3;
      else
        return 0;
    }
    for(unsigned operand = 0; operand < arity; ++operand)
    {
      btor2_nid_t value;
      if(!(input >> value) || value == 0)
        return 0;
      node.operands.push_back(value);
      uses[value].push_back(id);
    }
    if(node.op == "init")
      inits[node.operands[0]].push_back(id);
    if(node.op == "next")
      nexts[node.operands[0]].push_back(id);
    if(!nodes.emplace(id, std::move(node)).second)
      return 0;
  }

  std::map<std::size_t, std::string> replacements;
  for(const auto id : memory_initializers)
  {
    const auto found = nodes.find(id);
    if(found == nodes.end() || found->second.op != "init")
      continue;
    const auto &init_node = found->second;
    const auto element = array_elements.find(init_node.sort);
    if(element == array_elements.end())
      continue;
    const auto target = init_node.operands[0];
    const auto seed = init_node.operands[1];
    const auto seed_node = nodes.find(seed);
    if(target == seed || inits[target].size() != 1 ||
       seed_node == nodes.end() || seed_node->second.op != "state" ||
       seed_node->second.sort != init_node.sort)
      continue;

    if(inits[seed].empty() && nexts[seed].size() == 1)
    {
      const auto self_next = nexts[seed][0];
      const auto &transition = nodes.at(self_next);
      const auto &references = uses[seed];
      if(transition.operands[1] == seed && references.size() == 3)
      {
        // The only references must be the two operands of next S S and
        // the value of init A S. Thus existentially choosing S0 adds no
        // restriction to A0. A's next function is completely unchanged.
        bool exclusive = true;
        for(const auto reference : references)
          exclusive = exclusive && (reference == self_next || reference == id);
        if(exclusive)
        {
          replacements[init_node.line] =
            "; redundant private array seed initializer " + std::to_string(id);
          removed_nodes.insert(id);
        }
      }
    }
    else if(inits[seed].size() == 1)
    {
      const auto value = nodes.at(inits[seed][0]).operands[1];
      const auto literal = nodes.find(value);
      if(literal != nodes.end() && literals.count(literal->second.op) &&
         literal->second.sort == element->second)
        replacements[init_node.line] =
          std::to_string(id) + " init " + std::to_string(init_node.sort) +
          " " + std::to_string(target) + " " + std::to_string(value);
    }
  }
  for(const auto &replacement : replacements)
    lines[replacement.first] = replacement.second;
  return replacements.size();
}

namespace
{
/// Read exactly a numeric token, never interpreting a literal/name as a ref.
btor2_nid_t pruning_number(
  std::istream &input,
  bool signed_reference = false,
  bool allow_zero = false)
{
  std::string token;
  if(!(input >> token))
    throw std::logic_error("Missing BTOR2 dependency pruning operand");
  const std::size_t begin = signed_reference && token[0] == '-' ? 1 : 0;
  btor2_nid_t result = 0;
  if(begin == token.size())
    throw std::logic_error("Invalid BTOR2 dependency pruning operand");
  for(std::size_t i = begin; i < token.size(); ++i)
  {
    const auto character = token[i];
    if(character < '0' || character > '9')
      throw std::logic_error("Invalid BTOR2 dependency pruning operand");
    const unsigned digit = character - '0';
    if(result > (std::numeric_limits<btor2_nid_t>::max() - digit) / 10)
      throw std::logic_error("BTOR2 dependency pruning operand is too large");
    result = result * 10 + digit;
  }
  if(!allow_zero && result == 0)
    throw std::logic_error("Zero BTOR2 dependency pruning reference");
  return result;
}
} // namespace

btor2_buildert::dependency_pruning_reportt
btor2_buildert::prune_dependencies(const std::vector<btor2_nid_t> &extra_roots)
{
  struct nodet
  {
    enum class kindt
    {
      absent,
      bitvec_sort,
      array_sort,
      state,
      input,
      init,
      next,
      root,
      expression
    };
    std::size_t dependencies_begin = 0;
    std::size_t dependencies_count = 0;
    btor2_nid_t sort = 0;
    btor2_nid_t state_target = 0;
    kindt kind = kindt::absent;
  };
  using kindt = nodet::kindt;

  // Dense ID indexing and one flat edge vector avoid a map/allocation per
  // expression in large models. The indices remain the original numeric IDs.
  std::vector<nodet> nodes(next_nid);
  std::vector<btor2_nid_t> dependencies, roots, line_ids(lines.size(), 0);
  std::map<btor2_nid_t, std::vector<btor2_nid_t>> state_definitions;
  dependency_pruning_reportt report;
  const std::set<std::string> literals = {"const", "constd", "consth"};
  const std::set<std::string> unary = {
    "not",
    "neg",
    "inc",
    "dec",
    "redand",
    "redor",
    "redxor",
    "slice",
    "uext",
    "sext"};
  const std::set<std::string> binary = {
    "add",  "sub",   "mul",   "sdiv",  "udiv",  "srem",   "urem",    "smod",
    "and",  "or",    "xor",   "nand",  "nor",   "xnor",   "eq",      "neq",
    "slt",  "ult",   "slte",  "ulte",  "sgt",   "ugt",    "sgte",    "ugte",
    "sll",  "srl",   "sra",   "rol",   "ror",   "concat", "implies", "iff",
    "read", "uaddo", "usubo", "umulo", "saddo", "ssubo",  "smulo",   "sdivo"};

  // Parse and validate the complete graph before changing any line. The
  // schema excludes widths, constant values, slice bounds, justice counts,
  // and optional symbols from the dependency graph.
  for(std::size_t i = 0; i < lines.size(); ++i)
  {
    std::istringstream input(lines[i]);
    input >> std::ws;
    if(input.peek() == ';' || input.peek() == std::char_traits<char>::eof())
      continue;
    const auto id = pruning_number(input);
    std::string op;
    if(id >= nodes.size() || nodes[id].kind != kindt::absent || !(input >> op))
      throw std::logic_error("Invalid BTOR2 dependency pruning declaration");
    auto &node = nodes[id];
    node.dependencies_begin = dependencies.size();
    line_ids[i] = id;
    if(op == "sort")
    {
      std::string kind;
      if(!(input >> kind))
        throw std::logic_error("Missing BTOR2 sort kind");
      if(kind == "bitvec")
      {
        node.kind = kindt::bitvec_sort;
        pruning_number(input); // Width is not a node reference.
      }
      else if(kind == "array")
      {
        node.kind = kindt::array_sort;
        dependencies.push_back(pruning_number(input));
        dependencies.push_back(pruning_number(input));
      }
      else
        throw std::logic_error("Unknown BTOR2 dependency pruning sort kind");
    }
    else
    {
      std::size_t arity = 0;
      if(op == "bad" || op == "constraint" || op == "fair" || op == "output")
      {
        node.kind = kindt::root;
        arity = 1;
      }
      else if(op == "justice")
      {
        node.kind = kindt::root;
        arity = pruning_number(input);
      }
      else
      {
        node.kind = kindt::expression;
        node.sort = pruning_number(input);
        dependencies.push_back(node.sort);
        if(op == "state")
          node.kind = kindt::state;
        else if(op == "input")
          node.kind = kindt::input;
        else if(literals.count(op))
        {
          std::string value;
          if(!(input >> value) || value[0] == ';')
            throw std::logic_error("Missing BTOR2 constant literal");
        }
        else if(op == "zero" || op == "one" || op == "ones")
        {
        }
        else if(unary.count(op))
          arity = 1;
        else if(binary.count(op))
          arity = 2;
        else if(op == "ite" || op == "write")
          arity = 3;
        else if(op == "init" || op == "next")
        {
          node.kind = op == "init" ? kindt::init : kindt::next;
          node.state_target = pruning_number(input);
          dependencies.push_back(node.state_target);
          state_definitions[node.state_target].push_back(id);
          arity = 1;
        }
        else
          throw std::logic_error(
            "Unknown BTOR2 dependency pruning operator: " + op);
      }
      for(std::size_t operand = 0; operand < arity; ++operand)
        dependencies.push_back(pruning_number(input, true));
      if(op == "slice")
      {
        pruning_number(input, false, true);
        pruning_number(input, false, true);
      }
      else if(op == "uext" || op == "sext")
        pruning_number(input, false, true);
      if(node.kind == kindt::root)
        roots.push_back(id);
    }
    node.dependencies_count = dependencies.size() - node.dependencies_begin;
    ++report.nodes_before;
    report.states_before += node.kind == kindt::state;
    report.inputs_before += node.kind == kindt::input;
  }

  const auto is_sort = [&](btor2_nid_t id)
  {
    return nodes[id].kind == kindt::bitvec_sort ||
           nodes[id].kind == kindt::array_sort;
  };
  for(const auto &node : nodes)
  {
    for(std::size_t j = 0; j < node.dependencies_count; ++j)
    {
      const auto dependency = dependencies[node.dependencies_begin + j];
      if(dependency >= nodes.size() || nodes[dependency].kind == kindt::absent)
        throw std::logic_error("Dangling BTOR2 dependency pruning reference");
      const bool sort_reference =
        node.kind == kindt::array_sort || (node.sort != 0 && j == 0);
      if(is_sort(dependency) != sort_reference)
        throw std::logic_error(
          "Invalid BTOR2 dependency pruning reference kind");
    }
    if(node.state_target != 0 && nodes[node.state_target].kind != kindt::state)
      throw std::logic_error("BTOR2 init/next target is not a state");
  }
  for(const auto root : extra_roots)
  {
    if(root == 0 || root >= nodes.size() || nodes[root].kind == kindt::absent)
      throw std::logic_error("Missing BTOR2 dependency pruning extra root");
    roots.push_back(root);
  }

  std::vector<unsigned char> retained(nodes.size(), 0);
  while(!roots.empty())
  {
    const auto id = roots.back();
    roots.pop_back();
    if(retained[id])
      continue;
    retained[id] = 1;
    const auto &node = nodes[id];
    report.retained_nodes.insert(id);
    report.states_after += node.kind == kindt::state;
    report.inputs_after += node.kind == kindt::input;
    roots.insert(
      roots.end(),
      dependencies.begin() + node.dependencies_begin,
      dependencies.begin() + node.dependencies_begin + node.dependencies_count);
    if(node.kind == kindt::state)
    {
      const auto definitions = state_definitions.find(id);
      if(definitions != state_definitions.end())
        roots.insert(
          roots.end(), definitions->second.begin(), definitions->second.end());
    }
  }
  report.nodes_after = report.retained_nodes.size();

  std::vector<std::string> retained_lines;
  retained_lines.reserve(lines.size());
  auto newly_removed = removed_nodes;
  bool retained_array_sort = false;
  for(std::size_t i = 0; i < lines.size(); ++i)
  {
    const auto id = line_ids[i];
    if(id != 0)
    {
      if(!retained[id])
      {
        newly_removed.insert(id);
        continue;
      }
      retained_array_sort =
        retained_array_sort || nodes[id].kind == kindt::array_sort;
    }
    else
    {
      std::istringstream input(lines[i]);
      std::string semicolon, marker;
      if(
        input >> semicolon >> marker && semicolon == ";" &&
        marker == "c2btor-source")
      {
        const auto source = pruning_number(input);
        if(source >= retained.size() || !retained[source])
          continue;
      }
    }
    retained_lines.push_back(lines[i]);
  }
  lines.swap(retained_lines);
  removed_nodes.swap(newly_removed);
  emitted_array_sort = retained_array_sort;
  for(auto it = bitvec_sort_cache.begin(); it != bitvec_sort_cache.end();)
    if(!contains_node(it->second))
      it = bitvec_sort_cache.erase(it);
    else
      ++it;
  for(auto it = array_sort_cache.begin(); it != array_sort_cache.end();)
    if(!contains_node(it->second))
      it = array_sort_cache.erase(it);
    else
      ++it;
  for(auto it = memory_initializers.begin(); it != memory_initializers.end();)
    if(!contains_node(*it))
      it = memory_initializers.erase(it);
    else
      ++it;
  return report;
}

/// 将生成的 BTOR2 内容写入输出流
void btor2_buildert::write(std::ostream &out) const
{
  for(const auto &line : lines)
    out << line << '\n';
}
