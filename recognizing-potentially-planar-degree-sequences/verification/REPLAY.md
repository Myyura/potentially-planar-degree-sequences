# 主工程的内核回放

从仓库根目录运行以下命令。第一行编译 Lean 主工程，第二行重新检查编译产物中的声明。脚本使用 Python 3.9 或更高版本和工程锁定的 Lean 工具链。

```sh
lake build
python3 recognizing-potentially-planar-degree-sequences/verification/replay.py
```

脚本从 `graphs/SparseBoundary.lean` 读取导入关系，依次回放每个可达的本地模块。普通模块由工具链的 `leanchecker -v` 检查。聚合模块的名称同时也是整个工程的命名空间，因此单独调用同一检查器的 `replayFromImports`，只回放该模块自身的声明。每次回放都把该模块的声明重新送入 Lean 内核检查。各次回放使用已编译的依赖环境。

默认日志 `.lake/kernel-primary.log` 包含工具链版本、核查模块、源码和 `.olean` 的 SHA-256、检查器输出、退出码及耗时。使用 `--log 路径` 可保留既有日志并写入另一份结果。下例单独重查大核上层的入口及其本地依赖。

```sh
python3 recognizing-potentially-planar-degree-sequences/verification/replay.py --log sparse-upper.log SparseBoundary.FanLargePositive
```

持续开发时，`--reuse-log 旧日志` 可以复用已经通过检查的条目。脚本验证工具链版本、源码和编译对象的哈希，还递归核对整个本地导入闭包。一个模块的依赖发生变化时，脚本会重新回放该模块。正式的从零复跑可以使用上方默认命令。
