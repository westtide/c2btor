/*******************************************************************\

Module: BTOR2 构建器 - 生成 BTOR2 格式的核心基础设施

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// BTOR2 构建器 - 生成 BTOR2 格式的核心基础设施
///
/// 本文件定义了 btor2_buildert 类，用于生成符合 BTOR2 规范的硬件模型检测格式。
/// BTOR2 是一种用于描述有限状态转换系统的标准格式，被 btormc、Boolector、Pono 等
/// 硬件模型检测器广泛使用。
///
/// BTOR2 格式的基本结构：
/// - 每条指令都有一个唯一的节点 ID (nid)
/// - 支持位向量 (bitvec) 和数组 (array) 类型
/// - 状态变量通过 init（初始化）和 next（状态转换）定义
/// - 属性通过 bad（坏状态）和 constraint（约束）定义

#ifndef CPROVER_GOTO_BTOR2_BTOR2_BUILDER_H
#define CPROVER_GOTO_BTOR2_BTOR2_BUILDER_H

#include <util/mp_arith.h>

#include <iosfwd>
#include <map>
#include <set>
#include <string>
#include <vector>

/// BTOR2 节点 ID 类型
/// 每条 BTOR2 指令都有一个唯一的正整数 ID，从 1 开始递增
using btor2_nid_t = unsigned;

/// BTOR2 格式输出构建器类
///
/// 这个类提供了生成 BTOR2 格式文件的所有必要方法。
/// BTOR2 格式用于硬件模型检测，描述有限状态转换系统。
///
/// 使用示例：
/// ```cpp
/// btor2_buildert builder;
/// auto sort32 = builder.sort_bitvec(32);           // 定义 32 位向量类型
/// auto zero = builder.zero(sort32);                 // 创建零常量
/// auto x = builder.state(sort32, "x");              // 创建状态变量 x
/// builder.init(sort32, x, zero);                    // 初始化 x = 0
/// auto one = builder.one(sort32);                   // 创建常量 1
/// auto x_plus_1 = builder.add(sort32, x, one);      // x + 1
/// builder.next(sort32, x, x_plus_1);                // x' = x + 1
/// builder.write(std::cout);                         // 输出 BTOR2
/// ```
class btor2_buildert
{
public:
  /// 构造函数，初始化节点 ID 计数器为 1
  btor2_buildert() : next_nid(1)
  {
  }

  //=========================================================================
  // 类型（Sort）定义操作
  //=========================================================================

  /// 创建位向量类型
  /// @param width 位向量的宽度（位数）
  /// @return 该类型的节点 ID
  /// 生成格式：<nid> sort bitvec <width>
  btor2_nid_t sort_bitvec(std::size_t width);

  /// 创建数组类型
  /// @param index_sort 数组索引的类型节点 ID
  /// @param element_sort 数组元素的类型节点 ID
  /// @return 该类型的节点 ID
  /// 生成格式：<nid> sort array <index_sort> <element_sort>
  btor2_nid_t sort_array(btor2_nid_t index_sort, btor2_nid_t element_sort);

  bool has_array_sorts() const
  {
    return emitted_array_sort;
  }

  /// 获取或创建位向量类型（带缓存）
  /// 如果相同宽度的类型已经创建过，直接返回缓存的节点 ID
  /// @param width 位宽
  /// @return 类型的节点 ID
  btor2_nid_t get_or_create_bitvec_sort(std::size_t width);

  /// 获取布尔类型（1 位位向量）
  /// @return 布尔类型的节点 ID
  btor2_nid_t get_bool_sort();

  //=========================================================================
  // 常量定义操作
  //=========================================================================

  /// 创建十进制常量
  /// @param sort_nid 常量的类型节点 ID
  /// @param value 十进制值
  /// @return 常量的节点 ID
  /// 生成格式：<nid> constd <sort_nid> <value>
  btor2_nid_t constd(btor2_nid_t sort_nid, const mp_integer &value);

  /// 创建二进制常量
  /// @param sort_nid 常量的类型节点 ID
  /// @param bits 二进制字符串（如 "1010"）
  /// @return 常量的节点 ID
  /// 生成格式：<nid> const <sort_nid> <bits>
  btor2_nid_t const_binary(btor2_nid_t sort_nid, const std::string &bits);

  /// 创建十六进制常量
  /// @param sort_nid 常量的类型节点 ID
  /// @param hex 十六进制字符串（如 "1A2B"）
  /// @return 常量的节点 ID
  /// 生成格式：<nid> consth <sort_nid> <hex>
  btor2_nid_t consth(btor2_nid_t sort_nid, const std::string &hex);

  /// 创建零常量（所有位为 0）
  /// @param sort_nid 类型节点 ID
  /// @return 零常量的节点 ID
  /// 生成格式：<nid> zero <sort_nid>
  btor2_nid_t zero(btor2_nid_t sort_nid);

  /// 创建一常量（值为 1）
  /// @param sort_nid 类型节点 ID
  /// @return 常量 1 的节点 ID
  /// 生成格式：<nid> one <sort_nid>
  btor2_nid_t one(btor2_nid_t sort_nid);

  /// 创建全 1 常量（所有位为 1）
  /// @param sort_nid 类型节点 ID
  /// @return 全 1 常量的节点 ID
  /// 生成格式：<nid> ones <sort_nid>
  btor2_nid_t ones(btor2_nid_t sort_nid);

  //=========================================================================
  // 状态和输入变量操作
  //=========================================================================

  /// 创建状态变量
  /// 状态变量在硬件中对应寄存器，其值可以在时钟周期间保持
  /// @param sort_nid 状态变量的类型节点 ID
  /// @param name 可选的变量名称
  /// @return 状态变量的节点 ID
  /// 生成格式：<nid> state <sort_nid> [<name>]
  btor2_nid_t state(
    btor2_nid_t sort_nid,
    const std::string &name = "",
    const std::string &source_symbol = "");

  /// 创建输入变量
  /// 输入变量表示系统的外部输入，每个时钟周期可以取任意值
  /// @param sort_nid 输入变量的类型节点 ID
  /// @param name 可选的变量名称
  /// @return 输入变量的节点 ID
  /// 生成格式：<nid> input <sort_nid> [<name>]
  btor2_nid_t input(btor2_nid_t sort_nid, const std::string &name = "");

  /// 初始化状态变量
  /// 设置状态变量的初始值（时间 t=0 时的值）
  ///
  /// BTOR2 要求所有操作数节点在使用前已定义（nid 更小）。
  /// 本方法产生的 init 节点引用 state_nid 和 value_nid，
  /// 因此调用前两者必须已创建；初值节点还必须先于 state 节点创建。
  ///
  /// @param sort_nid 类型节点 ID
  /// @param state_nid 状态变量的节点 ID
  /// @param value_nid 初始值的节点 ID
  /// @return init 指令的节点 ID
  /// 生成格式：<nid> init <sort_nid> <state_nid> <value_nid>
  btor2_nid_t init(
    btor2_nid_t sort_nid,
    btor2_nid_t state_nid,
    btor2_nid_t value_nid);

  /// 设置状态变量的下一个值
  /// 定义状态转换函数：state' = value
  /// @param sort_nid 类型节点 ID
  /// @param state_nid 状态变量的节点 ID
  /// @param value_nid 下一个状态值的节点 ID
  /// @return next 指令的节点 ID
  /// 生成格式：<nid> next <sort_nid> <state_nid> <value_nid>
  btor2_nid_t next(
    btor2_nid_t sort_nid,
    btor2_nid_t state_nid,
    btor2_nid_t value_nid);

  //=========================================================================
  // 一元运算符
  //=========================================================================

  /// 逻辑非 / 按位取反
  /// @return ~a
  btor2_nid_t lnot(btor2_nid_t sort_nid, btor2_nid_t a);

  /// 算术取反（补码）
  /// @return -a
  btor2_nid_t neg(btor2_nid_t sort_nid, btor2_nid_t a);

  /// 归约与：所有位做 AND
  btor2_nid_t redand(btor2_nid_t sort_nid, btor2_nid_t a);

  /// 归约或：所有位做 OR
  btor2_nid_t redor(btor2_nid_t sort_nid, btor2_nid_t a);

  /// 归约异或：所有位做 XOR
  btor2_nid_t redxor(btor2_nid_t sort_nid, btor2_nid_t a);

  //=========================================================================
  // 二元算术运算符
  //=========================================================================

  /// 加法 @return a + b
  btor2_nid_t add(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 减法 @return a - b
  btor2_nid_t sub(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 乘法 @return a * b
  btor2_nid_t mul(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 有符号除法 @return a / b (signed)
  btor2_nid_t sdiv(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 无符号除法 @return a / b (unsigned)
  btor2_nid_t udiv(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 有符号取余 @return a % b (signed)
  btor2_nid_t srem(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 无符号取余 @return a % b (unsigned)
  btor2_nid_t urem(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 有符号取模 @return a mod b
  btor2_nid_t smod(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);

  //=========================================================================
  // 二元逻辑运算符
  //=========================================================================

  /// 按位与 @return a & b
  btor2_nid_t land(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 按位或 @return a | b
  btor2_nid_t lor(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 按位异或 @return a ^ b
  btor2_nid_t lxor(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 按位与非 @return ~(a & b)
  btor2_nid_t nand_op(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 按位或非 @return ~(a | b)
  btor2_nid_t nor_op(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 按位同或 @return ~(a ^ b)
  btor2_nid_t xnor_op(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);

  //=========================================================================
  // 比较运算符（返回 1 位布尔结果）
  //=========================================================================

  /// 相等 @return a == b
  btor2_nid_t eq(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 不等 @return a != b
  btor2_nid_t neq(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 有符号小于 @return a < b (signed)
  btor2_nid_t slt(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 无符号小于 @return a < b (unsigned)
  btor2_nid_t ult(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 有符号小于等于 @return a <= b (signed)
  btor2_nid_t slte(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 无符号小于等于 @return a <= b (unsigned)
  btor2_nid_t ulte(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 有符号大于 @return a > b (signed)
  btor2_nid_t sgt(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 无符号大于 @return a > b (unsigned)
  btor2_nid_t ugt(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 有符号大于等于 @return a >= b (signed)
  btor2_nid_t sgte(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 无符号大于等于 @return a >= b (unsigned)
  btor2_nid_t ugte(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);

  //=========================================================================
  // 移位运算符
  //=========================================================================

  /// 逻辑左移 @return a << b
  btor2_nid_t sll(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 逻辑右移 @return a >> b (unsigned)
  btor2_nid_t srl(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 算术右移 @return a >> b (signed)
  btor2_nid_t sra(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 循环左移
  btor2_nid_t rol(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  /// 循环右移
  btor2_nid_t ror(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);

  //=========================================================================
  // 位操作
  //=========================================================================

  /// 位拼接：a || b（a 在高位）
  btor2_nid_t concat(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);
  
  /// 位提取 @return a[upper:lower]
  btor2_nid_t
  slice(btor2_nid_t sort_nid, btor2_nid_t a, unsigned upper, unsigned lower);
  
  /// 符号扩展（扩展 w 位）
  btor2_nid_t sext(btor2_nid_t sort_nid, btor2_nid_t a, unsigned w);
  
  /// 零扩展（扩展 w 位）
  btor2_nid_t uext(btor2_nid_t sort_nid, btor2_nid_t a, unsigned w);

  //=========================================================================
  // 条件表达式
  //=========================================================================

  /// 条件选择 @return cond ? then_val : else_val
  btor2_nid_t ite(
    btor2_nid_t sort_nid,
    btor2_nid_t cond,
    btor2_nid_t then_val,
    btor2_nid_t else_val);

  /// 逻辑蕴含 @return a → b
  btor2_nid_t implies(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);

  /// 逻辑等价 @return a ↔ b
  btor2_nid_t iff(btor2_nid_t sort_nid, btor2_nid_t a, btor2_nid_t b);

  //=========================================================================
  // 数组操作
  //=========================================================================

  /// 数组读取 @return array[index]
  btor2_nid_t
  read(btor2_nid_t sort_nid, btor2_nid_t array, btor2_nid_t index);
  
  /// 数组写入 @return array{index ↦ value}
  btor2_nid_t write(
    btor2_nid_t sort_nid,
    btor2_nid_t array,
    btor2_nid_t index,
    btor2_nid_t value);

  //=========================================================================
  // 属性定义
  //=========================================================================

  /// 定义坏状态（安全属性违反）
  /// 当 cond 为真时，表示系统进入了不安全状态
  btor2_nid_t bad(btor2_nid_t cond, const std::string &comment = "");

  /// 添加约束（假设条件必须始终成立）
  btor2_nid_t constraint(btor2_nid_t cond, const std::string &comment = "");

  /// 定义公平条件（用于活性属性）
  btor2_nid_t fair(btor2_nid_t cond, const std::string &comment = "");

  /// 定义输出
  btor2_nid_t output(btor2_nid_t value, const std::string &comment = "");

  //=========================================================================
  // 辅助方法
  //=========================================================================

  /// 添加注释行
  void comment(const std::string &text);

  /// 将生成的 BTOR2 内容写入输出流
  void write(std::ostream &out) const;

  /// 获取当前已生成的节点数量
  btor2_nid_t get_node_count() const
  {
    return next_nid - 1;
  }

  /// Check whether the given sort ID refers to a bitvec sort.
  bool is_bitvec_sort(btor2_nid_t sort_nid) const
  {
    for(const auto &entry : bitvec_sort_cache)
    {
      if(entry.second == sort_nid)
        return true;
    }
    return false;
  }

private:
  bool emitted_array_sort = false;
  // One namespace for all emitted optional symbols. Empty symbols stay absent.
  std::set<std::string> used_symbols;
  std::map<std::string, std::size_t> next_symbol_suffix;
  std::string unique_symbol(const std::string &name);

  btor2_nid_t next_nid;              ///< 下一个可用的节点 ID
  std::vector<std::string> lines;    ///< 存储所有生成的 BTOR2 指令行

  /// 添加一行指令并返回其节点 ID
  btor2_nid_t add_line(const std::string &line);

  /// 添加原始行（用于注释）
  void add_raw_line(const std::string &line);

  /// 通用一元运算符生成
  btor2_nid_t unary_op(
    const std::string &op,
    btor2_nid_t sort_nid,
    btor2_nid_t a);

  /// 通用二元运算符生成
  btor2_nid_t binary_op(
    const std::string &op,
    btor2_nid_t sort_nid,
    btor2_nid_t a,
    btor2_nid_t b);

  /// 位向量类型缓存：宽度 -> 节点 ID
  std::map<std::size_t, btor2_nid_t> bitvec_sort_cache;

  /// 数组类型缓存
  std::map<std::pair<btor2_nid_t, btor2_nid_t>, btor2_nid_t> array_sort_cache;
};

#endif // CPROVER_GOTO_BTOR2_BTOR2_BUILDER_H
