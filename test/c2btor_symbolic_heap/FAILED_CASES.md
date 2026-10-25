# 最终转换失败清单

770 个记录去重 case 排除 4 个递归程序后为 766 个。这里只报告转换与官方 parser，不报告 SAFE/FALSE。

| 编码 | 转换并解析成功 | 失败 |
| --- | ---: | ---: |
| Array / oa | 741 | 25 |
| Mixed | 741 | 25 |
| 纯 BV / ob | 553 | 213 |
| BV + 显式动态 Array 回退 | 691 | 75 |

Array 与 Mixed 的 25 个失败 case 完全一致：18 个自动对象重入、5 个自动/VLA 容量、1 个分配次数、1 个缺源性质。BV 回退额外还有 50 个逻辑数组打包问题，回退开关只改变动态对象。

| Case | 原因 |
| --- | --- |
| [array-crafted/bAnd5.i](/Users/west/Developer/cbmc/test/lab1-data/array-crafted/bAnd5.i) | 自动/VLA对象容量仍超出旧偏移范围 |
| [array-crafted/bor5.i](/Users/west/Developer/cbmc/test/lab1-data/array-crafted/bor5.i) | 自动/VLA对象容量仍超出旧偏移范围 |
| [array-crafted/mapavg5.i](/Users/west/Developer/cbmc/test/lab1-data/array-crafted/mapavg5.i) | 自动/VLA对象容量仍超出旧偏移范围 |
| [array-crafted/mapsum5.i](/Users/west/Developer/cbmc/test/lab1-data/array-crafted/mapsum5.i) | 自动/VLA对象容量仍超出旧偏移范围 |
| [array-crafted/xor5.i](/Users/west/Developer/cbmc/test/lab1-data/array-crafted/xor5.i) | 自动/VLA对象容量仍超出旧偏移范围 |
| [array-examples/sanfoundry_43_ground.i](/Users/west/Developer/cbmc/test/lab1-data/array-examples/sanfoundry_43_ground.i) | 未选中源性质 |
| [array-industry-pattern/array_of_struct_ptr_cond_init.i](/Users/west/Developer/cbmc/test/lab1-data/array-industry-pattern/array_of_struct_ptr_cond_init.i) | 自动对象重入缺少复用证书 |
| [array-industry-pattern/array_of_struct_ptr_flag_init.i](/Users/west/Developer/cbmc/test/lab1-data/array-industry-pattern/array_of_struct_ptr_flag_init.i) | 自动对象重入缺少复用证书 |
| [array-industry-pattern/array_of_struct_ptr_monotonic.i](/Users/west/Developer/cbmc/test/lab1-data/array-industry-pattern/array_of_struct_ptr_monotonic.i) | 自动对象重入缺少复用证书 |
| [array-industry-pattern/array_ptr_partial_init.i](/Users/west/Developer/cbmc/test/lab1-data/array-industry-pattern/array_ptr_partial_init.i) | 自动对象重入缺少复用证书 |
| [array-industry-pattern/array_ptr_single_elem_init-1.i](/Users/west/Developer/cbmc/test/lab1-data/array-industry-pattern/array_ptr_single_elem_init-1.i) | 自动对象重入缺少复用证书 |
| [array-lopstr16/base_case.i](/Users/west/Developer/cbmc/test/lab1-data/array-lopstr16/base_case.i) | 自动对象重入缺少复用证书 |
| [array-lopstr16/break-1.i](/Users/west/Developer/cbmc/test/lab1-data/array-lopstr16/break-1.i) | 自动对象重入缺少复用证书 |
| [array-lopstr16/flag_loopdep.i](/Users/west/Developer/cbmc/test/lab1-data/array-lopstr16/flag_loopdep.i) | 自动对象重入缺少复用证书 |
| [array-lopstr16/partial_lesser_bound.i](/Users/west/Developer/cbmc/test/lab1-data/array-lopstr16/partial_lesser_bound.i) | 自动对象重入缺少复用证书 |
| [array-lopstr16/single_elem_safe.i](/Users/west/Developer/cbmc/test/lab1-data/array-lopstr16/single_elem_safe.i) | 自动对象重入缺少复用证书 |
| [loop-industry-pattern/aiob_1.c](/Users/west/Developer/cbmc/test/lab1-data/loop-industry-pattern/aiob_1.c) | 自动对象重入缺少复用证书 |
| [loop-industry-pattern/aiob_2.c](/Users/west/Developer/cbmc/test/lab1-data/loop-industry-pattern/aiob_2.c) | 自动对象重入缺少复用证书 |
| [loop-industry-pattern/aiob_3.c](/Users/west/Developer/cbmc/test/lab1-data/loop-industry-pattern/aiob_3.c) | 自动对象重入缺少复用证书 |
| [loop-industry-pattern/aiob_4.c.v+cfa-reducer.c](/Users/west/Developer/cbmc/test/lab1-data/loop-industry-pattern/aiob_4.c.v+cfa-reducer.c) | 自动对象重入缺少复用证书 |
| [loop-industry-pattern/aiob_4.c.v+lh-reducer.c](/Users/west/Developer/cbmc/test/lab1-data/loop-industry-pattern/aiob_4.c.v+lh-reducer.c) | 自动对象重入缺少复用证书 |
| [loop-industry-pattern/aiob_4.c.v+lhb-reducer.c](/Users/west/Developer/cbmc/test/lab1-data/loop-industry-pattern/aiob_4.c.v+lhb-reducer.c) | 自动对象重入缺少复用证书 |
| [loops-crafted-1/discover_list.c](/Users/west/Developer/cbmc/test/lab1-data/loops-crafted-1/discover_list.c) | 自动对象重入缺少复用证书 |
| [loops/bubble_sort-2.i](/Users/west/Developer/cbmc/test/lab1-data/loops/bubble_sort-2.i) | 无法证明分配事件数有限 |
| [loops/n.c24.i](/Users/west/Developer/cbmc/test/lab1-data/loops/n.c24.i) | 自动对象重入缺少复用证书 |

完整各配置清单、原诊断和命令见 failed-cases.csv；原始模型/日志保存在 results/lab1-final。失败转换均未保留非空模型。

排除递归：bitvector-regression/recHanoi03-1.c、loop-industry-pattern/ofuf_1.c、ofuf_2.c、ofuf_3.c。

未达到全部 766 转换目标。符号 malloc 的容量拒绝已消除；上述独立问题和强制保留的有限身份边界没有被绕过。
