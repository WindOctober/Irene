# IterTestQ / CaQR 本地导入与 Irene 首轮结果

## 2026-09-15 前端复检

补齐 OpenQASM 2 自定义 gate、Qiskit 扩展门和科学计数法支持，并移除固定
gate 展开上限后，当前本地源码的解析检查通过 **291/291 对、582/582 文件**：
IterTestQ 180 对，CaQR 111 对。这里只复检前端，没有重跑等价性求解。
逐例本地记录：`var/experiments/frontend-291-after-fix/results.json`（工作区根目录）。
下文保留原始首轮实验记录；其中的前端失败描述属于修复前结果。

## 原始首轮实验

日期：2026-09-14。结论：**不能全部 solve**。本轮运行了实际导入的
291 对，不是对 Figshare 全量 program pairs 的完整求解覆盖。

## 本地数据与纳入范围

- 完整 IterTestQ Figshare v1 压缩包、两个官方 Git 仓库、CaQR 独立
  Qiskit 0.45.0 环境均在工作区 `var/benchmark-sources/`。
- Figshare 全量扫描 134,607 条 comparison 记录，其中 126,116 条具有
  明确 QCEC 标签：29,739 equivalent、69,590 equivalent_up_to_global_phase、
  26,787 not_equivalent。其余没有可靠 EQ/NEQ 判定，不强行赋 truth。
- 接口过滤及按原始路径去重后有 33,590 个静态 unitary 候选。
  本轮按实验版本、原始判定、左右平台分层，每层取前两对，纳入
  180 对（120 EQ / 60 NEQ）。**其余静态候选没有运行；动态/测量接口
  尚未完成语义适配。** 原始日志、equivalence class 和 provenance 未丢失。
- CaQR 全部 168 个原始输入均尝试官方生成：158 完成且官方验证通过、
  10 个在单例 20 秒限额下生成超时。48 个生成结果有复用但没有原始
  classical 输出，不能把被丢弃的 quantum outputs 简单同 index 配对，
  暂不纳入有真值的 paired manifest。
- CaQR 纳入 110 个生成对及 1 个仓库附带 BV 对，共 111 对。
  其中 108 个无复用，真正复用的是 committed BV、generated BV、generated CC。

详细来源与筛选规则：[IterTestQ README](itertestq/README.md)、
[CaQR README](caqr/README.md)。完整逐项记录分别为
[IterTestQ import-report](../../var/benchmark-sources/import-audits/itertestq/import-report.json) 与
[CaQR import-report](../../var/benchmark-sources/import-audits/caqr/import-report.json)。
逐例 provenance 也归档在各自的审计目录中，正式 manifest 保留来源、标签和语义映射。

## 批量结果

使用重新构建的 `tools/irene-experiment-worker/target/release/irene-experiment-worker`，
Irene revision `b67d4d5-dirty`，当前本地源码。首次构建遇到已有工作树的
私有方法访问错误；后续重试成功。本任务没有修改求解器源码。
本地工作树含既有未提交改动，revision 不是纯净发布版本。

每对 timeout=10 秒，8 个并发任务；沿用现有 runner 的 Irene 2 GiB
内存上限与 20 GiB 保留内存。超时清理使记录 wall time 可略超过 10 秒。

| 集合 | 对数 | EQ 且匹配标签 | NEQ | Unknown | 前端错误 | 超时 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| IterTestQ 首轮 | 180 | 11 | 0 | 115 | 54 | 0 |
| CaQR | 111 | 83 | 0 | 1 | 1 | 26 |
| 合计 | 291 | 94 | 0 | 116 | 55 | 26 |

明确给出 EQ/NEQ 的 94 对均匹配标签；这不代表其余 197 对通过。
IterTestQ 的 60 个来源 NEQ 本轮均未得到明确判定。
CaQR 的 3 个真实复用任务全部 EQ，证据为 `ExactHps`。
10 秒超时不等于长期无法求解，尚未做长时限复跑。

结果及每对 stdout/stderr：

- [IterTestQ summary](../../experiments/irene/itertestq/summary.json)
- [IterTestQ results.jsonl](../../experiments/irene/itertestq/results.jsonl)
- [CaQR summary](../../experiments/irene/caqr/summary.json)
- [CaQR results.jsonl](../../experiments/irene/caqr/results.jsonl)

## 具体问题

1. IterTestQ 的 54 个前端错误：48 个自定义 `gate` 声明不支持，
   3 个 `rzz`、2 个 `c4x`、1 个 `csx` 未识别。原始程序未做展开或改写。
2. IterTestQ 的 115 个 unknown 均为 `KernelAggregationRequired`，
   `solver_queries=[]`。不是 wall-clock timeout。
   例如 `itertestq-0001` 的 debug 输出显示 186 个路径变量、
   ket/bra phase 各 1,232，随后 `density exact SMT encoding refused: left complete sum`。
   这定位到完整路径和编码/聚合无法接纳，不能把 unknown 算作 NEQ。
   此单例诊断不能证明所有 unknown 都是同一个内部限制。
3. CaQR `caqr-generated-qft-16` 解析 `rz(-5.e-05)` / `rz(5.e-05)` 失败，
   消息为 `expected a finite decimal gate parameter: 5.e`。
   `caqr-generated-ising-model-10` 返回 `KernelAggregationRequired`。
4. CaQR 的 26 个超时主要是较大的可逆逻辑电路，即使没有发生复用，
   官方 QASM 导出也会改变表示；不能以文件或电路名字相同跳过真实验证。
5. CaQR 内存电路给插入的 measure/reset 附加条件，而 Qiskit 0.45.0
   的 QASM 导出丢掉这些条件。已用最小复现实验确认；本 benchmark 比较
   官方实际导出的 QASM。官方 `validate.py` 不比较条件，不能独立作为
   任意转换的完整语义证书。
6. IterTestQ 来源使用数值 QCEC；保留的 EQ/NEQ 是**来源参考标签**，
   不是 Irene 精确角度语义下的数学证书。没有把小数角度吸附到 pi，
   也没有根据同一 equivalence class 推导未记录的等价关系。

## 复现与校验

从工作区根目录执行：

```sh
python3 scripts/benchmarks/import_itertestq.py
var/benchmark-sources/caqr-env/bin/python scripts/benchmarks/materialize_caqr.py
cargo build --release --manifest-path tools/irene-experiment-worker/Cargo.toml
python3 scripts/experiments/run.py --tool irene \
  --manifest Irene/benchmarks/itertestq/manifest.toml --timeout 10 --jobs 8
python3 scripts/experiments/run.py --tool irene \
  --manifest Irene/benchmarks/caqr/manifest.toml --timeout 10 --jobs 8
```

runner 会复用已有结果；延长 timeout 复跑应使用新的 `--collection`，
否则不会重新运行已记录的 timeout。
已检查两个 TOML 的 case ID 唯一、所有程序/来源文件可解析路径、
OpenQASM 2 header、UTF-8/LF、truth 和显式非空 output_pairs。
新增 6 个接口测试全部通过，包括非 unitary 拒绝、复用后非同 index
classical 映射、被覆盖输出拒绝、链未完成拒绝及无 classical 输出拒绝。

下一步优先级：支持实际遇到的自定义 gate / 缺失门及科学记数法；
定位完整路径和聚合拒绝；长时限复跑 CaQR；再扩展 IterTestQ 全量
适配与测量类接口。当前没有把这些后续工作冒充为已完成。
