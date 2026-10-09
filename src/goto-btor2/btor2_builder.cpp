/*******************************************************************\

Module: BTOR2 构建器实现

Author: Based on CBMC project

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

#include <sstream>

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

/// 将生成的 BTOR2 内容写入输出流
void btor2_buildert::write(std::ostream &out) const
{
  for(const auto &line : lines)
    out << line << '\n';
}
