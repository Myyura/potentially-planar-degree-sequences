# 数学陈述与机器核验

两条主定理都已由 Lean 4.34.1 检查。它们适用于任意有限阶，度至少三的顶点数、二度点数和叶子数均无上限。

| 论文结论 | 无条件的 Lean 定理 |
| --- | --- |
| 定理 3.2。在 $S\le 4n-2-2\ell$ 的可图序列中，唯一没有平面实现的是 $(4^5,2)$ | `SparseBoundary.first_boundary` |
| 定理 3.3。在 $S=4n-2\ell$ 的可图序列中，没有平面实现当且仅当属于论文所列的例外 | `SparseBoundary.second_boundary` |
| 推论 3.4。上层 $p\ge8$ 时有平面实现，每个固定叶子数都有 $p=7$ 的例外 | `upper_eight_core`、`seven_core_obstruction` |
| 推论 3.4 的配对例子。相同的顶点数、度和、最大度、叶子数、二度点数和核心顶点数允许两种不同判定 | `seven_core_companion`、`seven_core_same_statistics`、`seven_core_obstruction` |
| 定理 3.3 的特殊情形。上层 $t\ge3$ 时例外只由核心顶点数和三度顶点数决定，$t=2$ 时有额外例外 | `upper_with_three_twos`、`two_twos_sharp` |
| 同一上层分类，直接以未排序序列为输入 | `SparseBoundary.second_boundary_invariant` |
| 含零度项的两个版本，以正度项数计算 $n$ | `SparseBoundary.first_with_isolates`、`SparseBoundary.second_with_isolates` |

两个顶层证明见 [FullBoundary.lean](../sparse/FullBoundary.lean)。推论及其尖锐例子见 [BoundaryCorollaries.lean](../sparse/BoundaryCorollaries.lean)。[AuditEG.lean](AuditEG.lean) 另外写出展开的定理类型，包括前提、两个方向和例外清单，再把实际证明赋给相应类型。[主定理、推论及例子的公理依赖](axioms-main.log)

## 定义如何对应论文

- `Graphic` 要求存在一张度数逐项相符的有限简单图。顶点有标号，每一对不同顶点的无序对占一位，邻接对称且无自环。`graphic_perm` 和 `planaric_perm` 保证允许任意重排。
- `Planaric` 要求存在一个平面实现。`Graph.Planar` 采用 Wagner 的禁子式刻画，排除具有非空、连通、两两不交分支集的 $K_5$、$K_{3,3}$ 模型。与平面可嵌入性的识别依据经典 Wagner 定理。仓库中的 [Wagner 形式化接口](../planarity/EmbeddingBridge.lean) 将禁子式条件与平面嵌入联系起来。[形式定义](../graphs/SparseBoundary/Graph.lean) · [Wagner 1937](https://doi.org/10.1007/BF01594196)
- 形式陈述写作 $S+2+2\ell\le4n$ 和 $S+2\ell=4n$，避免自然数减法的截断。`profile h t l` 表示一个按降序排列的高次核心、$t$ 个二度项与 $l$ 个一度项。[边界陈述](../graphs/SparseBoundary/Boundary.lean)
- `ZeroPadding.filter_positive` 证明，删去任意位置的全部零度项保持可图性和潜在平面性。若把零计入 $n$，$(4^5,0)$ 满足 $20\le 22$，却只有 $K_5$ 加一个孤立点这一种实现。此反例也已核验。含零版本还涵盖全部顶点均孤立的情况。[孤立点证明](../graphs/SparseBoundary/ZeroPadding.lean)

## 覆盖与证明路线

| 环节 | 可核对的入口 |
| --- | --- |
| 所有禁止情形，含上层无限族 | `lower_exception_verified`、`upper_obstructions_nonplanar` |
| 叶子删除与恢复，及所有例外前驱 | `lower_iff_without_leaves`、`upper_iff_without_leaves` |
| 两个等式层且核心顶点数至多七 | `exact_at_most_seven` |
| 至少八个核心顶点，两个等式层，任意二度点数 | `large_exact_verified` |
| 整个严格不等式区域，包括任意叶子数 | `lower_from_exact_normal`、`lower_from_large` |
| 可图性判定与归约后的简单图存在性 | `ErdosGallai.graphic_boundary_criterion`、`ErdosGallai.sparse_graphic` |
| 引理 C.1 的扩展范围，包括五个核心顶点且 $j\ge1$ 的情形 | `ErdosGallai.graphic_sparse_criterion`、`ErdosGallai.graphic_sparse_iff_degree_cap` |
| 附录 C 中的七个旋转系统及相应度序列的平面实现 | `Rotations.repairs_spherical`、`finite_repairs_planaric` |

未写前缀的 Lean 名称均属于 `SparseBoundary`。机器证明完整覆盖两条主定理的陈述。书面证明用面内插点引理和稀疏区间的已有定理。机器证明在这些环节改用显式图构造、较小核心的归纳，以及边收缩和分支集证书。有限表仅负责归纳的基本情形。对两张最大的收缩表，每一张候选图都有单独的 Lean 证明，按组汇总为小阶平面性定理。第 3 节用度数直方图给出线性时间的判定算法。Lean 的核验范围为表列数学结论。

## 复核

使用 [verify.sh](verify.sh) 复核。所需的源代码、证书数据、版本清单均随附。项目未声明额外数学公理。两条主定理的传递公理依赖均为 `propext`、`Classical.choice`、`Quot.sound`。各辅助结果的输出保存在 [axioms-graph.log](axioms-graph.log) 中。

本次构建使用项目清单锁定的 Lean 和 mathlib。mathlib 固定提交为 `d13f23b723b8a846827a245b89c10fc7d3f11612`。标准命令 `lake build BoundaryCorollaries` 构建两条主定理、推论及尖锐例子。首次构建时 Lake 按清单获取依赖。Erdős–Gallai 的证明源码及许可证已随附。[Lake 清单](../sparse/lake-manifest.json) · [许可证](../sparse/LICENSE.atlas)

[主工程逐模块回放流程](REPLAY.md) · [主工程回放日志](kernel-primary.log) · [补充工程回放日志](kernel-bridge.log)

`leanchecker` 使用同一版本的 Lean 内核，在独立进程中重新检查已编译声明。主工程的 147 个本地模块和补充工程的 5 个模块都已通过回放，其中包括 ATLAS 的 Erdős–Gallai 证明。该次核查逐项比对了主工程 147 个模块的源码、编译产物和本地导入关系，沿用与当前版本完全一致的回放记录。补充工程 5 个模块均已重新回放。两个工程也分别通过标准 Lake 构建和定理类型审计。[构建记录](build.log)

此外，以最多七个顶点的无标号简单图全集作独立抽查。保留没有孤立点的图，并按正度序列分组，在第一条不等式内查到 249 种可图序列，其中一种没有平面实现。在第二个等式层查到 36 种，其中 18 种没有平面实现。逐个比较图的平面性与论文判据，285 种判定全部一致。[独立抽查脚本](check_atlas.py) · [实际输出](atlas.log)

除去注释与字符串，对全部本地 Lean 源文件进行扫描，未发现 `sorry`、`admit`、`sorryAx`、自定义 `axiom` 或 `native_decide`。各模块的覆盖范围可在相应的回放日志中逐项核对。
