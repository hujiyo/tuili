# std-deduce

一个可废止的、带依赖类型的**规则演绎内核**，为法律与思想体系的形式化而写。

它不是数学证明助手。它不追求"证明定理"，而是追求一件更小但更难的事：
**把"条文 → 规则 → 推导"这条链条上的每一步都摊开、可查、可反驳。**

```
┌──────────────┐   ┌──────────────┐   ┌──────────────┐
│  kernel      │   │  lang        │   │  reason      │
│  可信核心    │◀──│  解析/精化   │   │  可废止推理  │
│  ~1200 行    │   │  不负责可信  │   │  推导 + 校验 │
└──────────────┘   └──────────────┘   └──────────────┘
```

## 四条不可动摇的设计承诺

这四条是这个项目存在的理由。任何功能请求如果与它们冲突，功能让路。

1. **没有否定即失败。** 规则只在**前提被推出**时触发，绝不在"推不出相反结论"时触发。
   `unless P` 只在 `P` **被推出**时阻断规则。这一点若搞错，"因未查证而驳回"就会变成一条定理。
2. **冲突不许被悄悄吞掉。** 两条规则得出相反结论时，系统报"冲突 / 未决"，而不是随便挑一条。
   矛盾由 `contrary` / `unique` 显式声明，裁决只认 `defeated_by` / `prefer`；没有优先级时两条结论都不进事实库，
   但两条推导都会打印出来，查询以非零退出码结束。
3. **没有 `sorry`。** 推不出的目标生成一个**缺口节点**，列出候选规则和缺哪些前提。洞是显示的，不是关掉的。
4. **出处是第一等公民。** 每条规则、每个事实都带着 `source` 字段（文本 / 条号 / 版本 / 引文 / 链接 / 管辖 / 抓取时间 / 哈希 / 备注），推导树的每个节点都打印它来自哪一条。
   加载时 `rule` 与 `axiom` 必须有出处：缺失或来源只有空白都会报错并指出声明名；`Reasoner::assume` 同样拒绝空来源与空白来源。
   `:given` 登记的事实来源是「用户输入交互会话」，不会打印空 `「」`。
   `:audit` 能把已填写的引文与仓库语料逐字核对；空 `quote` 的来源不参与核对，也不影响其退出码，但仍不会阻止加载。

## 推理语义：最小不动点

知识集不是"只增不减"地累积，而是**每轮从假设重新计算**，直到不再变化。

这不是实现细节，是正确性要求：`unless` 让推理算子变成**反单调**的——多推出一条事实、
反而可能撤回一条早先的结论。按"只插入、永不删除"的循环计算，刑法第二十条的例子就会出错：
`防卫过当` 成立之后，`不负刑事责任` 依然留着，两条互斥结论同时成立。按不动点计算，
被阻断的结论会被撤回，`#gap` 会告诉你"被 XXX 阻断了"，而不只是"缺前提"。

若两组结论来回振荡（两条规则互相以 `unless` 阻断），系统报错并拒绝裁决，而不是挑一个。

## 冲突：声明、裁决、报告

系统不会因为两个名字"看起来像反义"就认定矛盾。「该批准」和「不该批准」在账本里只是两个名字，
矛盾必须显式声明。两种声明覆盖两类冲突：

```
contrary 批准 不批准      -- 两个谓词互补：参数相同就不能同时成立
unique 应适用 1           -- 一个谓词的第 1 个参数单值：同一案件只能适用一条规范
```

声明之后，检测到冲突时只有三种结局：

| 情形 | 裁决 |
|---|---|
| 一侧是已知事实（`axiom` / `:given`） | 事实胜出，规则结论不进事实库 |
| 两侧都是规则，且一侧被另一侧 `defeated_by` / `prefer` | 胜出方进事实库，被否决方不进 |
| 两侧都是规则，没有优先级 | **未决**，两条结论都不进事实库 |

三种结局都不静默：`:why` 在未决时打印两条推导，在已裁决时打印胜出方与被否决方；
两种情况都以非零退出码结束。缺口是第四种结局，跟冲突分开报告。

优先级是局部的：`defeated_by X` 表示 X 胜过本规则，`prefer X` 表示本规则胜过 X；
它只在两条规则确实冲突时起作用，不改变无关规则的推导。

## 快速开始

```powershell
cargo run -p std-deduce-cli
```

无参数进入 REPL。也可以像 Lean 一样直接加载一个文件后退出：

```powershell
cargo run -q -p std-deduce-cli -- examples/constitution-39.std
```

二进制名是 `std-deduce`，包名仍是 `std-deduce-cli`。加载失败时的诊断采用 Lean 风格：
解析错误带源码行列，输出 `路径:行:列: error: ...`；精化与内核错误没有 AST span，
不伪造位置，输出 `路径: error: ...`。诊断里的路径会先转义换行、控制与不可见格式字符
（如 `\n`、`\u{202E}`），字面反斜杠保持单写，一条失败只占一行。
批处理入口把这条诊断原样写到 stderr 并以 `1`
退出，不再重复路径或另加前缀；`:load` 命令仍以 `错误：` 前缀报告同一条诊断。
`std-deduce check <文件.std>` 与直接给文件等价；`std-deduce repl` 显式进入 REPL；
`std-deduce env` 检查并加载默认法律环境。环境选项写在文件、子命令或冒号命令之前：
`--profile <名字>` 选择 `lawpacks/profiles` 里的 profile，`--no-default-packs` 关闭默认环境
（显式 `import` 仍可用），`--allow-community-packs` 允许 profile 包含非官方信任级别的包。
`--help` / `-h` 打印用法，`--version` / `-V` 打印 `std-deduce <版本>`；两者只能作为唯一参数。
选项只解析开头连续的一段；文件、`check`/`repl`/`env` 或冒号命令之后再出现 `-` 开头的参数仍按
未知选项报用法错误（`2`），不会被当成文件读取，也不会被静默忽略。`--profile` 缺值、重复使用或与
`--no-default-packs` 同时出现都是用法错误；`env` 后的多余参数也是用法错误，并提示选项要写在
`env` 之前。文件名本身以 `-` 开头时写 `./-名字`；文件名正好是 `env` 时写 `./env`。

交互命令：

| 命令 | 作用 |
|---|---|
| `:load <文件>` | 加载一份 `.std` 理论文件（逐条检查，任一失败则整体回滚）。默认环境在第一次 `:load` 时按 profile 预加载（失败则本次加载失败）。`import <包名>` 先看当前会话已加载的 namespace：未加载的才从当前目录的 `lawpacks` 扫描注册表、校验 `std.lock`，按依赖递归加载包内 `kind = "theory"` 的文件；已由包加载的仍复核版本/哈希漂移，已由文件加载的不读注册表。没有 import 且默认环境未启用/已关闭（或 import 全部已由文件加载）时不读取注册表 |
| `:inspect` | 打印声明台账（含出处与全部来源字段） |
| `:given <命题>` | 手工登记一条已知事实 |
| `:why <命题>` | 先由推理结果生成证书，从证书渲染并打印推导树，再用 `cert::check` 与 `cert::kernel_proof` 复核同一份证书；冲突未决时打印两条推导 |
| `:gap <命题>` | 说明为什么推不出，列出缺口；冲突与缺口分开报告 |
| `:cert <命题>` | 跑推理并把该目标的证书 JSON（缩进）写到 stdout；推不出的目标导出为缺口根，缺口与未决冲突写入 `open_obligations` |
| `:verify-cert <证书文件> [目标命题]` | 只凭**已加载的环境**检查证书 JSON：先跑 `cert::check`，再跑 `kernel_proof`，两段分开报告；必须先 `:load`，不重跑推理器。给了目标时，再要求证书根命题与目标内核等价；不等价、根为缺口或没有根都退出 `2`。路径含空格时在目标前用双引号括起路径；不加引号时，整串若正好是已存在文件则视为仅路径（兼容旧用法），否则按第一个空白分隔路径与目标 |
| `:packs [目录]` | 扫描目录（默认当前目录下的 `lawpacks`）并列出法律包清单：名称、版本、辖区/地域、生效范围、信任级别、描述与文件数；清单声明 `corpus` 时再读取链接的条级语料并打印覆盖计数与本体缺口；若目录里有 `std.lock`，再重新哈希并校验；不导入规则，不要求 `:load`。只校验清单与锁，不检查 namespace 唯一性，也不保证包可导入——这些由 `:load` 检查 |
| `:lock [目录]` | 对目录（默认 `lawpacks`）里的所有包计算内容哈希，写入 `<目录>/std.lock`；坏包/坏文件/重复包名时打印错误并退出 `2`，不写部分锁 |
| `:audit [目录]` | 只核对已加载理论里 `quote` 非空的 `source`：法名匹配语料标题/别名，版本、条号、引文（删除全部空白后逐字比较）、条文哈希（条文原文含换行的 SHA-256）与管辖逐项检查；`quote` 为空的来源不参与核对，单独计数且不影响退出码。默认语料目录 `law/corpus`，按 `<law>/<version>.json` 严格布局。至少一条带引文来源且全部命中才退出 `0`；一条带引文来源都没有时报“没有可核对的引文”并退出 `1`；坏语料退出 `2` |

`:cert` 的 JSON 写在 `:load` 报告之后，从第一个 `{` 起才是证书。保存证书后，
在另一个会话里加载同一理论再检查（`:check` 已改名为 `:verify-cert`）：

```powershell
cargo run -q -p std-deduce-cli -- ':load examples/constitution-39.std' ':cert 不受侵犯 张三 甲宅'
# 把上一条输出中第一个 { 起的内容保存为 cert.json
cargo run -q -p std-deduce-cli -- ':load examples/constitution-39.std' ':verify-cert cert.json'
```

非交互模式（命令行参数）的退出码如下：

| 命令 | `0` | `1` | `2` |
|---|---|---|---|
| `:why` | 两层证书检查都通过、根已证明且无未决义务 | 缺口、未决冲突、被否决的结论，或根已证明但仍有未决义务 | 命令/解析错误、证书生成或渲染失败，或任一层证书检查失败 |
| `:gap` | 目标可以推出 | 缺口、未决冲突或被否决的结论 | 命令或解析错误 |
| `:cert` | 根已证明 | 根是缺口 | 用法、解析、转换或序列化错误 |
| `:verify-cert` | 两段都通过、根已证明且无未决义务 | 两段都通过，但根是缺口 / 有 `open_obligations` / 有未决冲突 | 未加载、读不到、坏 JSON、逻辑校验失败、内核证明失败，或给了目标但根命题不等价/根为缺口/没有根 |
| `:packs` | 扫描成功；空目录也是成功 | 当前没有 `1` 的结局 | 目录不存在/不可读、坏清单/坏目录项，或 `std.lock` 校验失败（好包仍会列出） |
| `:lock` | 所有包成功扫描并写入锁 | 当前没有 `1` 的结局 | 目录/清单/包内文件错误、重复包名或写锁失败；不写部分锁 |
| `:audit` | 至少一条带引文来源，且全部命中 | 没有带引文来源（没有可核对的引文），或有引文来源未命中/未核对 | 尚未 `:load`，或语料本身坏了（坏布局、坏 JSON、重复 `(law, version)`） |
| `:load` | 文件（以及默认环境与 import 的包）加载成功 | 当前没有 `1` 的结局 | 文件、profile、注册表、锁、包路径、包 namespace 或 import 失败 |
| `std-deduce <文件.std>` | 文件加载成功，且后续命令全部成功 | 文件加载失败（含 profile/默认环境/import/注册表/锁失败），或后续查询是缺口/未决冲突 | 后续命令错误、未知选项或用法错误 |
| `std-deduce env` | 环境已加载，或自动模式下没有默认 profile 可加载 | 当前没有 `1` 的结局 | 没有 `lawpacks/`、坏 profile、坏锁、缺包、版本不符或信任不足等环境错误 |

也可以一次性执行：

```powershell
cargo run -q -p std-deduce-cli -- ':load examples/constitution-39.std' ':why 不受侵犯 张三 甲宅'
# 批处理入口：先加载文件，再依次执行后面的命令
cargo run -q -p std-deduce-cli -- examples/constitution-39.std ':why 不受侵犯 张三 甲宅'
```

输出示例：

```
▸ 不受侵犯 张三 甲宅  ⟨非法搜查即侵犯⟩ ← 「宪法第三十九条」
  实例：p ↦ 张三，h ↦ 甲宅
  · 非法搜查 张三 甲宅  [某次搜查非法]

推导已通过独立校验。
```

## 法律包与 `import`

案件或模块文件可以在开头写 `import <包名>`：

```text
import cn.constitution
namespace 我的案件
...
```

`:load` / 批处理先解析文件里的 `import`，再按当前会话的状态决定要不要读注册表：

- 没有 `import` 的文件本身不需要注册表；但默认环境开启时，第一次 `:load` 会先读
  `lawpacks/profiles` 校验并加载默认包。`--no-default-packs` 恢复纯文件行为：
  没有 `import` 就不读 `lawpacks/`，也不要求 `std.lock` 存在。
- 已经由本会话加载的 namespace 直接使用，不再查注册表：它可能来自模块文件（`:load module.std`），
  也可能来自包。
- 未加载的 namespace 才进入注册表；由包加载的 namespace 即使已加载也仍走注册表，以复核版本与
  哈希漂移。只有确实需要解析的 import 才扫描注册表；全部可跳过时，一次也不打开注册表。

需要注册表时：

1. 注册表根是**当前工作目录**下的 `lawpacks/`，不从二进制位置或仓库根推断；根不存在/不可读
   是错误，错误信息给出期望路径。
2. `lawpack::scan` 扫描注册表；坏清单、坏目录项、重复包名、重复 namespace 都让整次加载失败，
   所有扫描错误一起列出，不跳过坏包。
3. 必须存在 `lawpacks/std.lock` 并校验通过。缺锁、锁版本不符、包版本/哈希不符、缺包/多包、
   符号链接都在一次校验里报告，错误全部列出；一次 `:load` 只校验一次锁，不按 import 重复校验。
   锁校验是**校验时点**的语义：`verify_lock` 返回后文件再变化，本次加载不会重新发现；需要更强
   保证时重新 `:lock` 并重启会话。
4. 按包名找到清单。可导入包的清单必须声明 `namespace`，且 `namespace` 必须等于包名：`import`
   写的是包名，而 `Library` 又要求导入名等于已加载 namespace。包内每个 `kind = "theory"` 文件的
   namespace 必须等于清单的 `namespace`，否则加载失败并指出文件名和两个 namespace。
5. 只打开 `kind = "theory"` 的条目；`path` 必须是相对路径，不能是绝对路径、不能含 `..`，
   同一个包内不能重复，必须是普通文件、非符号链接、有效 UTF-8。路径分量不能含 `:`（Windows
   备用数据流：`theory.std:hidden` 会读写 `theory.std` 的隐藏流，目录扫描和锁哈希都看不到它，
   所以跨平台一律拒绝）；`:lock` 只哈希包目录里的普通文件，这种包仍能写出锁，但不能导入。
   一个 theory 文件都没有的包不能 import，报“包 `x` 没有可导入的 theory 文件”。
6. 包内 theory 文件按 manifest 顺序加载；每个文件先解析它的 `import`，递归加载依赖包，再交给
   `Library::load`。依赖先于 importer；多个包共用同一个依赖时只加载一次；`a → b → a` 报错
   并给出环路径。
7. 整个 `:load` 在 `Library` 克隆和包记录克隆上完成；任何一步失败都丢弃克隆，不留半加载的
   声明、包信息或 `loaded` 状态。
8. 加载成功后 `Session` 记录包的 `name`、`version`、`hash`、`namespace` 与该包实际声明的名字。
   `:inspect` 只给真正由该包声明的 namespaced 声明显示 `[name@version]`（如
   `[cn.constitution@0.4.0]`）；直接按文件加载的 namespaced 模块仍显示 `[ns]`；案件文件声明
   没有后缀。顶层文件的 namespace 若等于某个已加载包的 namespace，加载被拒绝并提示使用独立
   namespace，防止用户文件向官方 namespace 注入声明；包加载器内部的 theory 文件不走这条检查
   （它们的 namespace 必须等于清单 namespace）。

加载报告在 `已加载` 行后打印顶层文件自己的 `import`：`  导入 cn.constitution`；包内部的依赖
不会重复打印。有活动 profile 时，显式 import 的包若不在默认环境（profile 的直接包与依赖闭包）
里，该行追加环境外标记：`  导入 example（环境外：community）`；环境内的包保持原样。
没有活动 profile 时输出不变。

仓库里的官方包 `cn.constitution` v0.4.0 已经可以导入，案件文件只需写事实：

```powershell
cargo run -q -p std-deduce-cli -- examples/宪法第三十九条-导入包.std ':why cn.constitution.住宅受侵犯 张三 甲宅'
```

案件只声明 `cn.constitution.中国国籍 张三` 与 `cn.constitution.非法搜查 张三 甲宅`；包内
`中国国籍即公民` 先推出 `公民 张三`，`非法搜查侵犯住宅` 再推出
`▸ cn.constitution.住宅受侵犯 张三 甲宅 ⟨cn.constitution.非法搜查侵犯住宅⟩ ← 「宪法第三十九条」（2018）`，
最后打印 `推导已通过独立校验。`。官方包 v0.4.0 有 2 个 sort（`人`、`住宅`）、70 个 pred 与
56 条 rule，共 128 个声明，形式化第三十三至五十六条的**选定句子**；第二章第二批是第四十七、
四十八、五十二至五十六条。第三十三条的人权宣示、第三十四条的反歧视清单、第三十五条的自由边界、
第三十六条的正常宗教活动与不受外国势力支配、第三十九条的住宅范围、第四十条的合法检查程序、
第四十一条的机关义务与禁止诬告、第四十二条的国家就业政策、第四十三条的工时休假制度、
第四十四条的退休制度、第四十五条的军人优抚与残疾人帮助、第四十六条的国家培养条款、
第四十七条的国家鼓励、第四十八条的国家保护与同工同酬、第五十四条的禁止危害行为、
第五十五条的兵役制度仍是开放概念/说明，不是公理，也不是整部宪法或整条条文的完整形式化。
语料的 `coverage` 是 143 条完整台账：每条标为 `formalized`（至少一条核心操作性句子已写成规则，
不等于整条完整）、`partial`（有规则但实质性条款未建模）、`indexed`（只索引）或
`needs_ontology`（缺少具名本体，不是遗漏）。官方语料的计数是形式化 14、部分 7、仅索引 17、
待本体 105、开放概念 49；部分形式化的是第三十六、四十、四十四、四十七、四十八、五十四、
五十五条。第四十二条的劳动义务来自第一句“公民有劳动的权利和义务”，是无条件的法律义务；
第三句“有劳动能力的公民”评价的是“光荣职责”，不窄化第一句。第四十一条的申诉、控告、检举以
“国家机关或国家工作人员违法失职行为存在”为前提，不要求提出者本人受侵害；具体是哪个机关或人员
由案件事实作开放判断。
`0.4.0` 是**包版本**，不是法律文本年份——文本年份看 `source` 的 `version "2018"` 与语料版本
`2018`。`lawpacks/std.lock` 固定 `cn.constitution@0.4.0` 与包内容哈希，`:inspect` 对包内声明
显示 `[cn.constitution@0.4.0]`。清单的 `corpus = "cn.constitution/2018"` 把包和语料连起来，
`:packs` 会读取 `<注册表父目录>/law/corpus/cn.constitution/2018.json` 并打印覆盖计数与本体缺口。

### 默认法律环境与 profile

`lawpacks/profiles/*.toml` 声明默认法律环境。仓库里的 `lawpacks/profiles/cn.default.toml`：

```toml
name = "cn.default"
aliases = ["cn"]
default = true
description = "中国法默认环境：只含官方宪法包"
trust = "official"

[[packs]]
name = "cn.constitution"
version = "0.4"
```

- `name` 与 `aliases` 的字符集、长度和首尾限制与包名相同；alias 不能被两个 profile 共用，
  也不能与任何 profile 的 `name` 相同。`default = true` 最多一个。
- `profiles/` 里只允许普通 `.toml` 文件；子目录、符号链接、非 `.toml` 文件和坏 TOML 都让整次
  扫描失败，并列出全部错误，不静默跳过。
- `trust` 是环境要求的最低信任级别，profile 缺省 `official`；取值 `official` / `community` /
  `local` / `experimental`，排序 `official` > `community` > `local` > `experimental`。
  profile 里的包（包括依赖闭包）必须达到该级别。
- `[[packs]]` 的 `version` 是按点分段的前缀约束：`0.1` 接受 `0.1`、`0.1.0`、`0.1.9`，
  不接受 `0.10.0`、`0.2.0`；段按文本比较，不做数值归一化。
- profile 文件不进入包内容哈希，`std.lock` 不记录它。

清单的 `[pack]` 有可选 `trust` 字段（`official` / `community` / `local` / `experimental`），
缺省 `community`，所以没写 trust 的包不会被当成官方包。官方 `cn.constitution` 声明
`trust = "official"`。这个字段既用于默认环境的门禁，也在 `:packs` 的首行显示。

第一次加载理论文件时（`:load` 或批处理文件入口），如果当前目录有 `lawpacks/` 且其中有
`default = true` 的 profile，会话会先加载该环境；`--profile <名字>` 可按名称或别名显式选择，
`--no-default-packs` 关闭默认环境，显式 `import` 仍然工作。`--allow-community-packs` 只在
profile 默认环境生效，允许非官方包进入环境。没有 `lawpacks/`、没有 `profiles/` 或没有默认
profile 时不启用默认环境，也不打开注册表校验锁；纯逻辑文件照常工作。

`std-deduce env` 单独检查并加载环境，打印 profile、信任要求、包版本映射、注册表、锁校验与
环境加载结果，退出码只有 `0`（成功，或自动模式下没有默认 profile）与 `2`（环境错误）。
它总是校验注册表与 `std.lock`；启用 profile 时还会真正加载包，所以坏 theory 文件也以 `2` 失败。
依赖闭包中不在 profile 直接列表里的包标成 `（依赖）`。

默认环境只在第一次加载时懒加载，`:packs` / `:lock` / `:inspect` 和纯 REPL 启动不触发。
加载在克隆的 `Library` 与包记录上进行，失败不会留下半加载的声明或包记录。预加载报告只有在
**本次文件加载整体成功**后才打印；环境准备成功但文件随后失败时，报告被丢弃，REPL 下一次成功
加载会重新准备并打印一次。成功时预加载报告在文件加载报告之前打印：

```
默认环境 cn.default：已加载 1 个包
  cn.constitution@0.4.0（official）
```

依赖写成 `  dep.pack@0.1.0（community，依赖）`；用了 `--allow-community-packs` 且 profile
含非官方包时，首行追加 `（已允许非官方包）`。关闭或未启用默认环境时不打印预加载行。

`examples/宪法第三十九条-默认环境.std` 只写对象与事实，不写 `import`、`sort`、`pred` 或 `rule`：

```powershell
cargo run -q -p std-deduce-cli -- examples/宪法第三十九条-默认环境.std ':why cn.constitution.住宅受侵犯 张三 甲宅'
```

`--no-default-packs` 下文件本身加载失败、且错误是 `未知名称 \`...\`` 时，错误后追加一行提示：
只考虑当前 `lawpacks/` 注册表里 `namespace` 与 `name` 相同、因而可 `import` 的包，按包名最长前缀
匹配，指出该名字可能来自哪个法律包，并建议写 `import <包名>` 或去掉 `--no-default-packs`。
缺 namespace 或 namespace 与 name 不同的包不可导入，既不被建议，也不会用更长的 namespace
遮蔽同前缀的可导入包。文件已经 import 该包时不提示（名字不存在是文件自己的问题）；依赖闭包里
的包也能被命名。提示只做诊断，只在文件加载失败时出现，不改变退出码：批处理仍 `1`，`:load`
仍 `2`。显式 import 一个环境外的包仍是用户的决定，系统不禁止。

临时注册表示例：

```powershell
# lawpacks/example/lawpack.toml 声明 name = "example"、namespace = "example"、
# version = "0.1.0"，[[files]] 指向 kind = "theory" 的 example.std
cargo run -q -p std-deduce-cli -- ':lock lawpacks'
cargo run -q -p std-deduce-cli -- ':load case.std' ':inspect'
```

失败时批处理入口退出 `1`，显式 `:load` 退出 `2`；诊断仍以 `path: error: ...`（或带行列号的
`path:line:col: error: ...`）开头，包解析错误含包名与相关路径。默认环境的 profile、锁、版本、
信任或包错误同样让本次加载失败；`std-deduce env` 的环境错误单独以 `2` 退出。`:packs` / `:lock`
不参与这条加载路径；`--packs`、远程 registry、`std build/update` 仍未实现。证书也还不记录
包身份/哈希或默认环境（证书 v3）。

## 条级语料与 `:audit`

语料是仓库内的静态 JSON，按 `law/corpus/<law-id>/<version>.json` 存放（整本 txt 仍保留在 `law/`）：

```json
{
  "format": 2,
  "law": "cn.constitution",
  "title": "中华人民共和国宪法",
  "aliases": ["宪法"],
  "version": "2018",
  "jurisdiction": "CN",
  "effective_from": "1982-12-04",
  "source_url": "http://www.npc.gov.cn/...",
  "retrieved_at": "2026-11-22",
  "text_sha256": "sha256:...",
  "notes": "序言未入库；官方只维护宪法包。",
  "coverage": {
    "open_concepts": ["非法", "住宅", "侵犯", "人身自由"],
    "notes": "coverage.articles 是整个宪法的 143 条台账：formalized 表示该条至少一条核心操作性句子已写成规则，不等于整条完整形式化；partial 表示有规则但实质性条款未建模；indexed 表示只作索引、不作形式化声明；needs_ontology 表示缺少具名本体，不是遗漏。",
    "gaps": {
      "state_organs": "国家机关、职权、组成、任期与会议程序",
      "legal_norms": "法律规范、位阶、冲突与审查"
    },
    "articles": [
      { "number": "第一条", "status": "indexed" },
      { "number": "第二条", "status": "needs_ontology", "gap": "state_organs" },
      { "number": "第五条", "status": "needs_ontology", "gap": "legal_norms" },
      { "number": "第三十三条", "status": "formalized", "rules": ["cn.constitution.中国国籍即公民"] },
      { "number": "第三十六条", "status": "partial", "rules": ["cn.constitution.公民有宗教信仰自由"], "note": "未建模“正常宗教活动”“宗教团体和宗教事务不受外国势力支配”。" }
    ]
  },
  "articles": [
    { "number": "第一条", "text": "条文正文，不含“第X条”前缀；多段用 \n 连接" }
  ]
}
```

示例只节选台账里的几条；实际文件里 `coverage.articles` 与 `articles` 一一对应，共 143 条。

`format` 必须为 2；`law` 只允许小写 ASCII 字母、数字、`.`、`-`；`title`、`version`、
`jurisdiction` 非空；`effective_from` / `retrieved_at` 若存在必须是真实的 `YYYY-MM-DD`；
`text_sha256` 若存在必须是 `sha256:` 加 64 位小写十六进制；`articles` 非空，条号在文件内唯一
（空白归一化后比较），条文正文非空。`coverage` 可选；存在时 `coverage.articles` 必须与
`articles` 一一对应、顺序一致，每条按 `status` 携带字段：`formalized` / `partial` 必须有非空
`rules`，`partial` 还必须有非空 `note`；`indexed` 不得带 `rules` 或 `gap`；`needs_ontology`
必须有 `gap`，且该键在 `gaps` 中已定义。`gaps` 的每个键都必须被至少一条引用；一条规则名只能
出现在一个条号下；至少有一条 `formalized`。`open_concepts` 可以为空数组，但每个概念必须非空、
无首尾空白且不重复，`notes` 可选。未知字段（包括 `coverage` 内的未知字段）、坏 JSON、
重复 `(law, version)` 都报错，不跳过。
语料目录按 `<law>/<version>.json` 严格布局：根下只能有 `<law>` 目录，目录名必须等于语料的 `law`，
文件名主干必须等于 `version`；子目录、非 `.json` 文件、根下文件和布局外的 JSON 都报错，不静默跳过。
`text_sha256` 是整本官方文本的抓取哈希（取自 staging 的 provenance），**仅为出处元数据，
`:audit` 不重算、不校验它**；`source_url`、`retrieved_at`、`text_sha256` 与可选的 `notes` 都是出处元数据，
匹配只用 `title`/`aliases`、`version`、`jurisdiction` 与 `articles`。
仓库目前只有 `law/corpus/cn.constitution/2018.json`，收录第一至第一百四十三条完整条级语料，
按 staging `text.txt` 的段落结构保留换行；序言、目录、章/节标题不入库。它的 `coverage` 是
143 条完整台账：形式化 14 条、部分 7 条、仅索引 17 条、待本体 105 条，开放概念 49 个；
部分形式化的是第三十六、四十、四十四、四十七、四十八、五十四、五十五条。第二章第二批
覆盖第四十七、四十八、五十二至五十六条；第五条、第三章国家机构仍未进官方包
（第五条与三个宪法案例仍由各自的示例文件本地形式化）。
`effective_from` 是宪法原施行日 1982-12-04，条文为 2018 修正文本，不是 1982 年文本。

`:load` 之后，`:audit [目录]` 只核对账本里 `quote` 非空的来源；`quote` 为空的来源打印
`· 「…」：没有引文原文，不参与核对`，单独计数且不影响退出码。对带引文的来源：

1. `text` 或 `locator` 为空 → 失败；
2. `text` 与语料 `title`/`aliases` 都做空白归一化（trim + 连续空白折叠为空格）后匹配；找不到 → 未核对；
3. `source.version` 非空时必须与语料 `version` 相等；为空且同名有多个候选 → 歧义失败；
4. `locator` 与条号同样归一化匹配；找不到 → 失败；
5. `quote` 与条文正文删除**所有 Unicode 空白字符**后逐字比较；标点、数字、字母任一不同 → 失败；
6. `source.hash` 非空时必须是 `sha256:` 加 64 位小写十六进制，且等于条文正文原样 UTF-8（含换行）的 SHA-256；
7. `source.jurisdiction` 非空且与语料不同 → 失败。

输出逐条给出 `✓ 「宪法第三十九条」← cn.constitution@2018`、`✗ …：原因`、`? …：原因（未核对）`，
以及无引文来源的 `· …：没有引文原文，不参与核对`。最后汇总
`核对 N 条带引文来源：命中 H，不一致 M，未核对 U；另有 K 条来源无引文（不参与核对）`，
再给条文哈希状态：已固定并核验、未固定、未核验或格式非法。
至少一条带引文来源且全部命中才退出 `0`；一条带引文来源都没有时明确报“没有可核对的引文”并退出 `1`。
未核对（没有对应语料）不是通过。语料目录不存在或为空时，带引文来源逐条报未核对（退出 `1`）；
坏布局、坏 JSON 或重复 `(law, version)` 退出 `2`。来源文本、条号、版本、语料标识和路径在打印前都会转义
控制字符与不可见格式字符（含 U+2028/U+202E、ESC）以及字面反斜杠，引文里的换行或制表符不会破坏行结构。
遇到带 `text_sha256` 的语料时，`:audit` 会额外注明它仅是出处元数据、未重算、未校验。
汇总之后，每个加载的语料再打印覆盖声明与列表：
`覆盖 cn.constitution@2018：形式化 14 条 / 部分 7 条 / 仅索引 17 条 / 待本体 105 条 / 开放概念 49 个`、
`  形式化：「第三十三条」、「第三十四条」、…`、
`  部分：「第三十六条」、「第四十条」、…`、
`  待本体：state_organs 82、property_economy 11、…`、
`  开放概念：「非法」、「住宅」、「侵犯」、「人身自由」、…`。列表项逐项用 `「」` 括起，
概念本身含 `、` 时不会与分隔符混淆；空概念列表打印 `开放概念：（无）`。有 `coverage.notes`
时再打印 `  备注：…`；`待本体` 只列具名缺口及条数，不逐条列 105 个条号。没有 `coverage`
的语料打印 `覆盖 …：未声明`。覆盖计数是语料里的**声明**，`:audit` 只显示它，
不与已加载理论中的规则自动比对；自动核对尚未实现。

核对边界：`:audit` 只证明"引文与仓库语料中的条文一致"，不证明规则忠实于条文、不判断条文是否适用于
具体案件、也不判断法律结论正确。语料是仓库内的静态文件，没有爬取或版本历史；`:audit` 不读取
`lawpacks/` 或锁。条文哈希也没有写进证书。仓库里多数 `examples/` 的 `source` 仍没有 `quote`，
对它们运行 `:audit` 会逐条显示无引文，并因“没有可核对的引文”退出 `1`；
`examples/宪法第三十九条-导入包.std` 通过官方包引入带引文的规则，可以直接审计。

## 三个宪法案例

`examples/` 下的 `宪法案例-*.std` 不是"把判决重新演一遍"，而是把每条推导的
**步骤、前提与出处**摊开。三个案例各针对一条承诺：

### 齐玉苓案（2001 判决 / 2008 批复废止）

```powershell
cargo run -q -p std-deduce-cli -- `
  ':load examples/宪法案例-齐玉苓.std' `
  ':why 应承担民事责任 顶替 齐玉苓'
```

推导链是：宪法第四十六条 → 受教育权 → 冒名顶替侵害该权利 → 法释〔2001〕25号
→ 承担民事责任。每一步都打印出处。

然后再登记一条事实，看同一个理论如何改判：

```powershell
cargo run -q -p std-deduce-cli -- `
  ':load examples/宪法案例-齐玉苓.std' `
  ':given 批复已废止' `
  ':gap 应承担民事责任 顶替 齐玉苓'
```

最后一步被 `unless 批复已废止` 撤回，`#gap` 会说明**被什么阻断**——而不是
"推不出"三个字。这就是 2008 年第七批司法解释废止之后的状态。

### 孙志刚事件（2003）—— 否定即失败的正面演示

```powershell
cargo run -q -p std-deduce-cli -- `
  ':load examples/宪法案例-孙志刚.std' `
  ':gap 应当收容 孙志刚' `
  ':why 不得收容 孙志刚'
```

收容遣送办法第九条第六款要求「无合法证件、无正常居所、无正当生活来源」三项，
本案账本里只有一条「缺暂住证」。系统不会把"没证明他有证件"读成"证明他没证件"，
所以 `应当收容` 永远是缺口；同时法工委的解释独立地推出 `不得收容`。
两条结论并列，不互相否定。

### 河南种子案（2003）—— 冲突不许被吞掉

```powershell
cargo run -q -p std-deduce-cli -- ':load examples/宪法案例-河南种子案-冲突.std' ':why 应适用 种子法 汝阳种子公司案'
```

这份文件里两条规则都推得出「应适用」：种子法一条、省条例一条。它们不可能同时成立，
但这不是从名字里能看出来的，所以文件里有一行 `unique 应适用 1`——
同一个案子只能适用一条规范。

没有优先级时，两条结论都不进事实库，但两条推导都会打印出来，退出码非零：
系统不替你选，也绝不悄悄丢掉。

换一个会话加载 `宪法案例-河南种子案-裁决.std`，它多了三样：一条有出处的位阶判断
（立法法第七十九条）、一条把位阶翻译成结论的规则、一条 `defeated_by`。冲突被裁决，
推导树里能看见「优先于」这一步。两份文件只差这三样——这就是要说的事：
冲突不是被内核偏好消解的，是靠人补进一条**带出处的判断**，再显式指明谁更强。

互补谓词的最小例子是 `examples/冲突-互补谓词.std`：

```powershell
cargo run -q -p std-deduce-cli -- ':load examples/冲突-互补谓词.std' ':why 批准 甲'
```

## 表面语法

```
sort 公民                    -- 一个类别
obj 张三 : 公民              -- 一个个体（类型必须是类别，不能是命题）
pred 侵害 : 公民 → 住宅 → Prop
axiom 事实 : 非法搜查 张三 甲宅
def 别名 : 公民 := 某人

rule 住宅不受侵犯 :
  params p : 公民, h : 住宅       -- 全称量化的变量
  premise 非法搜查 p h            -- 前提，按顺序匹配已知事实
  conclude 不受侵犯 p h           -- 结论
  unless 依法搜查 p h             -- 只有被"推出"时才阻断
  defeated_by 另一条规则           -- 冲突时败给它；prefer 则相反
  source text "宪法" locator "第三十九条" version "2018"
         effective "1982-12-04" jurisdiction "CN"
         quote "中华人民共和国公民的住宅不受侵犯。禁止非法搜查或者非法侵入公民的住宅。"
         url "https://www.npc.gov.cn/..." retrieved_at "2026-11-21"
         hash "sha256:..." note "..."

contrary 批准 不批准               -- 声明的互补谓词：同一组参数不能同时成立
unique 应适用 1                    -- 第 1 个参数单值：同一案件只能适用一条规范

#proposition 命题                  -- 只检查该项的类型是否为 Prop，不证明命题成立
```

`#check` 打印项的类型，`#show` 打印声明的类型；`#proposition` 只做命题类型检查，
不证明命题成立——要断言成立，请用 `axiom` 写事实或用 `rule` 写规则。

模块文件与案件/示例文件都可以以可选的 `import` 块开头，模块随后写 `namespace`：

```
import cn.constitution

namespace cn.criminal
sort cn.criminal.罪名
pred cn.criminal.盗窃 : cn.constitution.人 → Prop
```

`namespace` 只能出现一次，且必须在所有 `import` 之后；之后所有声明名（`sort` / `obj` / `pred` /
`axiom` / `def` / `rule` / `interpret`）和所有对声明的引用都必须带 `<namespace>.` 前缀。规则参数、
前提 binder 和 `λ` / `∀` 的 binder 是局部名，不带前缀。不同模块可以用相同的后缀（`a.违法` 与
`b.违法` 可以同时存在），加载顺序不影响结果。没有 `namespace` 的文件是案件/示例文件：它可以引用
`a.违法` 这样的限定名，但不能自己声明带 `.` 的名字。

`import` 每行写一个带点包名，只能出现在 `namespace` 和所有声明之前；CLI 加载时先看当前会话
已加载的 namespace，未加载的才去 `lawpacks` 解析。`Library` 本身只接受已加载的 namespace，
否则加载失败并报告“包 `x` 尚未加载”。`import` 只写包名，不写版本；重复 import 同一个包合法，
加载报告与 `Theory.requires` 只记录一次。`import` 不是声明，也不会进入 `:inspect` 账本。

出处要求的当前范围：

- `rule` 与 `axiom` 必须有 `source`，且至少一条来源的 `text` 与 `locator` 去掉空白后都非空；否则加载失败，错误指出声明名。
- `sort` / `pred` / `obj` / `def` 豁免：类型、词汇与定义不是断言，其来源由法律包清单与审计层承担。
- `contrary` / `unique` 豁免：冲突与唯一性声明不是事实断言，来源核验留给审计层。
- `interpret` 可以解析，但加载期显式拒绝：解释语义尚未实现（M2-8），推理器不消费解释。

## 架构与职责边界

- **`crates/kernel`**：唯一可信的部分。依赖类型（含依赖函数类型）、检查器、可判断等价、范式化。
  没有合一、没有元变量、没有隐式参数、没有类型类。内核只回答"是 / 否"，不猜。
  规则在加载时得到类型 `∀ 参数, 前提 → 结论`：把规则常量依次应用到参数和各前提的证明上，
  得到的类型正是结论。内核只认这个类型关系，它不知道"哪一步推导引用了哪条规则"——
  推导由推理器按自己的语义产生；把证书的单调骨架翻译成证明项、再交给内核检查，
  是 `crates/cert::kernel_proof` 的职责。
- **`crates/lang`**：词法、语法、精化、理论文件加载。**不可信**——它产出的每个项都会被内核重新检查。
- **`crates/reason`**：可废止前向链、推导树、缺口诊断，以及推导到证书的转换。
  内部校验器 `verify` 从**引用的前提**重建规则实例（前提决定实例，结论必须由它推出），
  并拒绝以下情形：前提数目不符、前提不是本规则该位置的实例、参数未被任何前提约束、
  结论与实例化结果不一致、任一 `unless` 在树中已成立。
  `unless` 是否成立按内核定义等价判断（alpha/eta 也算同一个命题），不只比打印字符串；
  比较失败按“已阻断”处理，绝不当作未阻断。
  **它由 reason crate 自己的测试使用，不是 CLI 用户可见的校验路径**：它不构造证明项，也不读取证书；
  CLI 的校验走 `crates/cert`。
  `certificate` 把推导转换成证书：节点顺序、前提顺序、结构化绑定、来源、缺口、冲突和根原样保留；
  无法编码成证书表达式的项会报错，不会丢弃。
- **`crates/cert`**：证书的数据模型、JSON 序列化、从证书渲染推导树的 `render`、逻辑检查器 `check`
  与内核证明项构造 `kernel_proof`（版本化格式，反序列化拒绝未知版本与未知字段）。
  当前格式版本为 2；v1 证书会被拒绝（`unsupported certificate format version 1`），
  需要按当前理论重新生成。
  `render` 只读证书：从根递归打印；没有根时打印没有被其他规则步骤当作前提的节点和全部缺口，
  多个根之间空一行；引用索引越界或节点图成环会报出节点编号，不 panic，也不打印占位符冒充成功。
  `check` 从规则声明、记录的绑定和引用的前提重建每一步，
  检查规则实例与 `unless` 阻断条件，并拒绝处于未决冲突或败方的根。
  阻断检查不只看证书节点和环境公理，还计算一个**保守的环境规则闭包**：忽略 `unless`、冲突和优先级，
  从证书假设、环境公理和节点结论出发，按 ground matching 反复应用规则到不动点；闭包里出现、但证书
  没有给出推导的 blocker 会被拒绝。无法静态求值的规则（依赖前提 binder、或在前提里应用函数参数）
  把打开的结论作为**结论模式**加入闭包；模式可以带规则参数变量，并沿可静态求值规则的前提（整体或
  嵌套子项）传播到不动点。blocker 与事实用内核 `convertible` 比较，与模式先做一阶合一、再把实例交给
  `convertible`；alpha/eta 和“绑定变量与同名常量”都不会因打印形式相同而混淆。
  它只依赖 `crates/kernel`，**不依赖 `crates/reason`**；已记录的冲突与裁决会被读取，但
  `defeated_by` / `prefer` 的优先级来源不在这里核验（`priority_sources_checked = false`）。
- **`crates/lawpack`**：法律包清单、目录扫描、`std.lock`、内容哈希、默认环境 profile 与条级语料。清单记录
  `name`、`version`、`jurisdiction`、`territory`、`namespace`、信任级别、生效范围、描述和文件列表；只校验
  **格式**（必填、字符集、长度、真实日历日期），不导入规则、不打开清单里的文件、不判断法律内容。
  `[pack].trust` 是可选信任级别（`official` / `community` / `local` / `experimental`，缺省 `community`），
  未知值在清单解析期报错。扫描只把含普通 `lawpack.toml` 的直接
  子目录当作包；符号链接、越界 junction 与坏清单都进入错误，不静默跳过。锁文件记录每个包的
  `name@version` 与 SHA-256；哈希覆盖包内全部普通文件，路径用 `/`、内容做 CRLF→LF 归一化，并用长度前缀
  消除拼接歧义。`profile` 模块扫描 `<registry>/profiles/*.toml`：校验名称、别名、唯一默认 profile、
  版本前缀约束与最低信任级别，提供默认/按名选择；profile 不进入包哈希或锁。
  `corpus` 模块按 `<law-id>/<version>.json` 严格布局加载条级语料：目录名必须等于 `law`、
  文件名主干必须等于 `version`，子目录、非 `.json` 文件与根下文件都报错；同时校验 JSON 格式、真实日期、
  哈希形状、条号唯一与 `(law, version)` 唯一，以及可选的 `coverage`（`formalized` 非空、无重复且指向
  现有条号，`open_concepts` 的每个概念非空且不重复、列表可为空），并提供 `audit` 做引文核对
  （标题/别名、版本、条号、
  空白归一化后的逐字引文、条文原文含换行的 SHA-256、管辖）。`text_sha256` 只校验形状，是出处元数据，
  不重算也不校验。该 crate 依赖 `serde` / `serde_json` / `toml` / `sha2`。
- **`crates/cli`**：`std-deduce` 二进制的批处理入口把第一个文件参数交给与 `:load` 相同的加载路径，
  成功后执行剩余命令；加载失败打印 `路径:行:列: error: ...`（无位置时 `路径: error: ...`）
  并退出 `1`。诊断路径先转义换行、控制与格式字符，字面反斜杠保持单写；除单独使用的
  `--help`/`-h`/`--version`/`-V` 外，首参或剩余命令中以 `-` 开头的参数按未知选项退出 `2`，
  不当作文件读取，也不作为注释静默忽略。会话命令里，`:why` 生成证书、从证书渲染
  推导树，并对同一份证书依次运行 `cert::check` 与 `cert::kernel_proof`；冲突分支展示的推导同样从证书渲染
  并用 `cert::check` 复核。`:cert` 导出证书，`:verify-cert` 依次运行 `cert::check` 与 `cert::kernel_proof`，
  把逻辑、内核、侧条件和需人判断分成四行报告；
  可选的目标绑定要求证书根命题与目标内核等价。`:load` 遇到 `import` 时先看当前会话已加载的
  namespace；未加载的（以及已由包加载、需要复核漂移的）才扫描当前目录的 `lawpacks`、校验
  `std.lock`，按依赖递归加载包内 `kind = "theory"` 的文件，并把包信息与包实际声明的名字记入
  `Session` 供 `:inspect` 显示 `[name@version]`；没有 `import` 且默认环境未启用/已关闭、或 import
  全部已由文件加载时不读取注册表。环境选项只在开头连续解析；第一次 `:load` 时 `environment` 模块
  按 profile 在克隆的库与包记录上加载默认环境（失败整体回滚），`std-deduce env` 独立检查并加载
  环境且只用 `0`/`2` 退出码；`--no-default-packs` 关闭预加载，并给文件本身加载失败时的缺包
  错误追加诊断提示（已 import 该包或查询错误不提示）。
  `:packs` 扫描清单、显示信任级别，并在清单声明 `corpus` 时读取链接语料、打印覆盖计数与具名
  本体缺口；目录里有锁时重新哈希校验。`:lock` 生成锁；`:audit` 只核对带 `quote` 的来源，无
  `quote` 的来源不参与核对、不影响退出码；汇总后按语料打印形式化/部分/仅索引/待本体计数、
  条号列表、本体缺口与开放概念。除 `:load` 的包文件外，三者都只读不导入规则，并转义外部文本
  （含不可见格式字符与字面反斜杠）。

官方只维护宪法包：`lawpacks/cn.constitution`、`lawpacks/profiles/cn.default.toml` 与
`law/corpus/cn.constitution/2018.json`（143 条完整语料与完整覆盖台账；
官方包 v0.4.0 有 2 个 sort、70 个 pred、56 条 rule，共 128 个声明，形式化第三十三至五十六条
中的选定句子；第二章第二批是第四十七、四十八、五十二至五十六条。第五条、第三章国家机构仍未
进入官方包；第五条与三个宪法案例由各自的示例文件本地形式化）。其他法律不进入
官方注册表或默认环境；社区包可以放在本地 `lawpacks/` 并由显式 `import` 加载，但不能当成官方文本。

### 证书链的当前边界

- `:why` 先生成证书，再从证书渲染推导树；打印的树就是随后被检查的那份证书。两层都通过、根已证明、
  且没有 `open_obligations` / 未决冲突时，才打印 `推导已通过独立校验。` 并以 `0` 退出；
  根是缺口时明确说明"证书有效，但根为缺口，结论未被证明。"并以 `1` 退出；
  任一层失败时报告失败层并以 `2` 退出。冲突分支展示的推导同样先转成证书再渲染，并用 `cert::check` 复核。
  `:why` 送检的是整份推导证书（含与目标无关的事实节点），不是只检查根可达子图；
  保守闭包若拒绝无关节点，`:why` 也会以 `2` 退出，与 `:verify-cert` 的立场一致。
- `:verify-cert` 依次运行两段：`cert::check` 检查规则实例、阻断条件与根冲突状态，
  `kernel_proof` 再把单调骨架翻译成证明项交给内核。逻辑通过但内核失败时退出 `2`，
  不会把"逻辑有效"当成"证书有效"；`kernel_proof` 本身仍不检查 `unless` 和优先级。
  带目标时还要求证书根命题与目标内核等价：证书本身合法但证明的是另一个命题，仍以 `2` 退出。
  这一绑定只在调用者给出目标时生效；`:verify-cert <file>` 单独使用仍只回答"这份证书自身是否有效"。
- `:packs` 只读清单与锁：坏清单、悬空符号链接、越界 junction 都会报错并退出 `2`，好包仍会列出；
  清单里的 description、路径与错误文本会先转义控制字符，不能借换行或终端转义伪造输出行。
  目录里有 `std.lock` 时会重新扫描并哈希：缺包、多包、版本不符、哈希不符或锁本身是符号链接都退出 `2`；
  没有锁时只提示“未锁定”，仍按清单结果返回；清单本身有错时锁校验标记为“未运行（清单错误）”，先修清单。
  `:lock` 遇到坏包不写任何锁；写锁前拒绝符号链接目标。
  `:packs` 不检查 namespace 唯一性，也不保证包可导入：两个包声明同一 namespace、清单 `path`
  含 `:` 等问题只在 `:load` / 包加载器里报错。锁校验是**校验时点**的语义，不是已解决的 TOCTOU：
  校验返回后文件再变化，不会被本次加载重新发现；需要更强保证时重新 `:lock` 并重启会话。
- `cert::check` 只检查根命题是否处于未决冲突或败方；非根冲突不在这里裁决，
  `defeated_by` / `prefer` 的优先级来源也未核验（`priority_sources_checked = false`）。
  `:cert` 把缺口写成 `MissingPremise`、把未决冲突写成 `UnresolvedConflict` 的
  `open_obligations`；它们只设置 `requires_human`，不会让逻辑校验失败。
- `cert::check` 的 blocker 检查是**保守过近似**：闭包忽略 `unless`、冲突和优先级，可能比 reasoner
  推出更多，因此可能拒绝一份合法证书；它不会放行省略的 blocker。结论模式减少了“同谓词名就误杀”
  的问题，但仍不精确：不可静态求值的规则按最一般结论模式处理，不利用其前提约束；高阶应用或绑定
  变量下的应用会退化为通配符；嵌套子项匹配和同一事实复用都是有意放宽。闭包有轮次/事实/模式/
  单条项大小/匹配上限，超限一律报错拒绝，不能当成"没有 blocker"。
- 证书 assumption 表里的每一条都进入上下文，即使没有任何节点引用；未使用的 blocker assumption
  也会阻断当前规则，未使用的非命题 assumption 直接报错。
- 根是 assumption 节点时，`root_proved` 只表示它在这份证书列出的 N 条假设下成立
  （`root_is_assumption = true`、`assumption_count = N`），是**在 N 条假设下的条件证明**，
  不是无条件结论。
- "证书通过"只表示它和当前加载的理论、规则声明及检查规则一致，**不表示法律结论正确**。
- 证书仍是 v2：不记录 profile、默认环境的包集合或信任级别。环境身份、语料哈希与 `as_of` /
  管辖一起留给证书 v3。

## 已知的、故意留白的地方

这些不是 bug，是还没做的决定。它们是下一步该讨论的东西：

- **否定没有作为连接词。** `¬P` 仍由"另立一个互补谓词 + `contrary` 声明"表达。要给系统一个真正的否定算子，需要先决定：它是经典的、直觉主义的，还是"有理由的否定"（如缺省逻辑）。对法律而言最后一种更合理。
- **规则匹配是链前的**：前提按书写顺序依次匹配已推出的事实。这够用，但对多前提交叉约束的规则（例如"同一行为在两个条款下"）需要更强的合一。
- **优先级只有 `defeated_by` / `prefer`，且作用在规则名上。** 它们只在冲突时参与裁决。真实法体系里还有"特别法优于一般法""上位法优于下位法"：可以写成带出处的规则间优先级，但尚未区分到规则实例级，也没有处理优先级环。
- **时间和地域不是一等公民。** `source` 里有 `effective` / `jurisdiction` / `retrieved_at` 字段，
  但它们只是记录：查询还没有"在 T 时刻""在 X 地"这样的参数，推理器也不检查案件发生地或时间。
  事实本身没有发生时间、发生地点。

### 宇宙：Prop 不可预测，Type 层可预测

`∀ x : A, P x` 的宇宙由共域决定：**共域是命题时，整体就是命题**，与量化域的层级无关。
这是 `Prop` 的不可预测性（impredicativity），也是「凡公民皆有受教育权」能被写成命题的前提。
`Type` 层仍严格预测：`∀ (A : Type), A` 落在 `Type 1`，不会造成 Type-in-Type。

### `:why` 的校验判据

`:why` 不调用 `reason::verify`。它把推导转换成证书，从证书渲染推导树，再让两层检查器读取同一份证书：

- `crates/cert::check` 从规则声明、记录的绑定和引用的前提重建每一步，检查规则实例与证书内可见的
  `unless` 阻断条件，并检查根命题是否处于未决冲突或败方；
- `crates/cert::kernel_proof` 把证书的单调骨架翻译成证明项，逐条交给内核检查。

两层都通过、根已证明且证书没有 `open_obligations` 和未决冲突时，才打印 `推导已通过独立校验。`；
根是缺口时打印明确的未证明说明；任一层失败即报错并以 `2` 退出。
`kernel_proof` 本身不检查 `unless`（阻断条件不在内核类型里），所以两层都要跑，不能只看内核结果。

`reason::verify` 保留为 reason crate 的内部校验器，由 reason 自己的测试使用。它从节点引用的**前提**
重建规则实例，再要求结论恰好是它的实例化结果。具体拒绝：前提数目不符；某前提不是本规则该位置前提的实例；
参数未被任何前提约束（此时伪造者可自由挑选个体）；结论与实例化结果不一致；某个 `unless` 在整棵树中
已成立。除「参数未被任何前提约束」外，其余四条各有用例。它不构造证明项、不读取证书，
也不处理环境的 blocker 闭包与根冲突状态；这些属于 `crates/cert` 的校验路径。

非根冲突的裁决与优先级来源不在 `verify`（也不在 `cert::check`）的范围内：
校验器只回答“这一步是不是该规则的合法实例”，它不判断两条结论谁优先。
冲突的裁决与报告由推理器负责，且冲突分支展示的两条推导各自从证书渲染并用 `cert::check` 复核。

### 其余已确认缺陷

- **`interpret` 只有语法，没有语义。** 解析器能读 `interpret 名称 : from → to`，但加载期
  显式拒绝，错误说明“解释语义尚未实现（M2-8），推理器不消费解释”。`Env::interpretations()`
  没有调用点，M2-8 实现解释语义后再放开加载。
- **规则参数必须被前提约束。** 出现在结论却没有出现在任何前提里的参数，
  加载时即被拒绝——否则实例化后结论会是 `?x`，那是一个不闭合的洞。
  代价是完全没有前提的规则暂时写不了；「凡公民皆有 X」现在可以写成
  `premise 公民 x → conclude X x`，不需要量词公理的实例化支持。
- **非命题声明不被拒。** `pred` / `axiom` / `def` 的共域不校验必须是 `Prop`。
  推理时已跳过声明型 axiom（`axiom 假 : Prop` 这类只声明常量、不断言命题），
  但账本本身仍接受形状不对的声明。
- **法律包导入已接通；官方宪法包 v0.4.0 形式化第三十三至五十六条中的选定句子。** `:load` 遇到
  `import` 时先看已加载的 namespace，未加载的才扫描 `lawpacks`、校验 `std.lock`，并递归加载
  `kind = "theory"` 的包文件，`:inspect` 显示 `[包名@版本]`；默认环境还会在第一次加载时按 profile
  预加载官方包。`lawpacks/cn.constitution/constitution.std` 有 2 个 sort、70 个 pred、56 条 rule
  （共 128 个声明），形式化第三十三至五十六条中的选定句子；第二章第二批落在第四十七、四十八、
  五十二至五十六条，其余句子仍是开放概念/说明，不是整条条文的完整翻译；第五条、第三章国家机构
  与三个案例不在官方包内（第五条与三个案例由各自的示例文件本地形式化）。
  `law/corpus/cn.constitution/2018.json` 已收宪法 143 条并维护完整覆盖台账（14 formalized /
  7 partial / 17 indexed / 105 needs_ontology），`:audit` 显示它、`:packs` 通过清单的 `corpus`
  链接显示计数与本体缺口；`:load` 不读取语料。证书还不记录包身份/哈希、profile 或默认环境
  （v3），多个文件加载后仍合并成一个扁平环境。
- **同一结论多路径只留一条。** `build_nodes` 用 `or_insert`，另一条推导及其出处丢失。

### 修复顺序

量词公理的实例化 → 否定语义 → 最后才加公理。

## 本地检查

工具链由 `rust-toolchain.toml` 固定（1.99.1，含 `rustfmt` / `clippy`），格式由 `rustfmt.toml` 约束。

```powershell
pwsh -NoProfile -File scripts/check.ps1
```

脚本依次执行下面三条命令，任一步失败就以非零码退出：

```powershell
cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

## 测试

`cargo test --workspace` 共 561 个：kernel 19、lang 76、reason 41、cert 101、cli 193、lawpack 131（含 1 个 doc test）。

- `crates/kernel/tests/kernel.rs`（19）：内核黄金用例（Type-in-Type 被拒、η、delta、规则良构、作用域），
  两条宇宙规则：`forall_over_individuals_stays_in_prop`（个体上的量词仍是命题）、
  `types_stay_predicative`（Type 层不许自包含），以及规则常量的两条：
  类型是 `∀ 参数, 前提 → 结论`，应用到全部参数与前提后正好得到结论；
  少给一个前提时剩下的是函数类型而不是结论，证明本身也不能当命题用。
  另有一条固定的加载期拒绝：参数与前提 binder 重名；以及来源渲染的几条：
  `one_line` 保持旧格式并转义控制字符、字面反斜杠与不可见格式字符，`full` 逐行列出全部非空字段并转义。
- `crates/lang/tests/lang.rs`（19）：最小规则和 `contrary` 声明能加载；参数/前提 binder 重名、
  未命名前提生成的 `_p{i}` 重名、参数只出现在 `unless` 里、以及完全未使用的参数都拒绝加载；
  规则与断言事实缺 `source` 或来源只有空白时加载失败且错误指出声明名，补上后加载成功；
  缺来源先于类型错误报告，失败的加载不改变库内容；
  `sort`/`pred`/`obj`/`def`/`contrary`/`unique` 无来源仍可加载；解析错误把行列保留在
  `LoadError` 里，消息不再内嵌“第 X 行第 Y 列”，`render` 输出 Lean 风格诊断。
- `crates/lang/src/module.rs`（4 个单元测试）：`LoadError` 的 Lean 风格渲染——有位置时
  `x.std:2:3: error: ...`，无位置时 `x.std: error: ...`；`Display` 始终只输出消息本身；
  `escape_path` 保留 Windows 反斜杠，把换行/回车/制表符与控制、格式字符写成短转义或
  `\u{XXXX}`，`render` 用它将路径压成一行。
- `crates/lang/tests/source.rs`（15）：字符串字面量的转义、CJK/URL 字符、未闭合/未知转义/裸换行与
  裸控制字符的行列号；“无法识别的字符”把 ESC/U+202E/BOM 写成 `\u{...}` 而不是原样回显；
  source 全字段按任意顺序跨行解析；重复键的报错列指向键；CRLF 输入、注释中的引号；
  缺/空 `text`/`locator` 与旧位置式写法都拒绝。
- `crates/lang/tests/namespace.rs`（22）：限定名词法/解析、`namespace` 第一条/唯一/格式与缺参位置；
  模块声明前缀与空段、未限定类型/结论/unless/`defeated_by`/`prefer`/`contrary`/`unique`/解释/`def`
  体/`obj`/`axiom`/`#check`/`#show` 的拒绝、局部 binder 豁免；两模块同名后缀与加载顺序无关；
  案件文件不能声明带点名字但仍可引用限定名；同名 theory 的 namespace 冲突；`defeated_by`/`prefer`
  目标必须存在且是规则并允许同文件前向引用；`interpret` 可解析但加载期拒绝；`LoadReport` 不含 namespace。
- `crates/lang/tests/import.rs`（16）：`import` 语法与加载校验——import 块可跨空行且位于 namespace 与
  所有声明之前，空 import 报在 import 行、行尾多 token 被拒、`import x@2018` 被词法拒绝、重复 import
  由解析层保留；案件与模块文件都可 import 已加载 namespace，报告按首次出现去重，未加载时报“尚未加载”
  且不改变库，同名但非 namespace 的 theory 不满足 import，模块可 import 已加载模块（含带点包名），
  失败加载不记录 import，重载同一 theory 时 `requires` 合并去重，import 不豁免声明名检查。
- `crates/cert/tests/json.rs`（16）：证书 JSON 的往返与格式稳定性——紧凑和缩进两种输出往返一致、
  快照比对、字段名与节点标签固定、未知版本或未知字段被拒、真正的 v1 证书因版本不符被拒并报告版本，
  缺少 v2 新字段的 v2 证书按默认值解析；全部来源字段（含引文、链接、管辖、抓取时间、哈希）的 JSON
  往返，以及内核表达式与 `CertExpr` 的双向转换。
- `crates/cert/tests/render.rs`（15）：从证书渲染推导树——假设与规则树（label、source、note、bindings、
  多前提）、缺口与候选（缺失前提、阻断条件）、无根时的多根与空行、`Source::one_line` 与内核格式一致，
  以及越界根/越界假设/越界前提和可达、不可达的节点环都返回带节点编号的错误；来源备注、假设标签、
  规则名、绑定参数、缺口备注、候选规则名与表达式常量/binder 名中的换行及控制/格式字符会被转义，
  不能伪造 `▸` 推导行。
- `crates/cert/tests/check.rs`（60）：检查器自己的契约——合法证书通过；前提数不符、未知规则、
  缺失/重复/未闭合绑定、结论或前提漂移、已成立的 `unless`、缺口当前提、越界索引和
  非命题假设等伪造都会被拒绝；根是缺口时 `root_proved = false`。
  环境规则推出的 blocker 不能被“删掉推导节点”绕过：直接、多跳、ground/变量结论模式、链式传播、
  嵌套前提、参数头、未使用的 blocker assumption 都拒绝；alpha/eta 变体按内核 `convertible` 命中；
  高阶应用、绑定变量下的应用和超出项大小上限的传播失败关闭；
  无 `unless` 的证书不触发闭包及其上限。
- `crates/cert/src/key.rs`（2 个单元测试）：表达式身份按 AST 结构编码，`Var(i)` 与同名 `Const`
  不同键，binder 名不影响键。
- `crates/cert/tests/kernel_proof.rs`（8）：证书的单调骨架到内核证明项——合法证书的根逐步通过内核；
  绑定漂移、结论不是命题、缺绑定、缺口当前提等错误带节点位置；已成立的 `unless` 仍能通过
  `kernel_proof`（阻断条件不在内核类型里），但会被 `cert::check` 拒绝。
- `crates/reason/tests/certificate.rs`（4）：推导到证书的转换——宪法第三十九条的证书往返并通过
  `cert::check`（根已证明）；缺口目标导出后 `root_proved = false`；冲突的左右命题、
  provenance 和裁决保留；无法编码的 de Bruijn 索引给出带节点位置的错误。
- `crates/reason/tests/reason.rs`（37）：各条承诺的回归测试，含三条关键的：
  "阻断条件撤回早先结论"、"阻断条件未被证明时不阻断"、"伪造推导被校验器拒绝"；
  另有三条 alpha/eta 用例：两种变体的 blocker 都阻断规则，`verify` 也拒绝 alpha 变体的伪造步骤。
  伪造一类另有四条独立用例钉住：跳过前提、引用无关前提、绑定漂移（结论与前提不一致）、
  阻断条件已成立。此外 `a_rule_with_an_unconstrained_parameter_is_rejected_at_load`
  钉住"参数只出现在结论或 `unless` 里、没有前提约束的规则不许加载"，
  `an_assumption_without_a_source_is_rejected` 与 `an_assumption_with_a_blank_source_is_rejected`
  钉住空来源和空白来源假设被拒绝，且拒绝的假设不进事实库。
- 冲突一组：`conflict_requires_a_contrary_declaration`（没有声明就不猜）、
  `contrary_assumptions_are_unresolved_and_kept_out_of_the_fact_base`（未决胜出方不进库）、
  `superiority_resolves_a_conflict_and_the_loser_stays_out`（优先级裁决且下游不触发）、
  `prefer_points_the_other_way`（`prefer` 与 `defeated_by` 方向相反）、
  `unique_declaration_makes_same_predicate_instances_conflict`（同一谓词不同参数互斥）、
  `unique_does_not_conflict_when_the_other_arguments_differ`（其余参数不同则相容），
  以及五条加载期拒绝（未知谓词、参数个数不同、重复 contrary、越界 unique、重复 unique）。
- `crates/cli/tests/examples.rs`（19）：`examples/` 下除默认环境示例外的每个 `.std` 一条端到端用例
  （默认环境示例由 `environment.rs` 覆盖）——
  加载文件、执行查询，断言退出码（证成 0，缺口 / 冲突 1）和关键输出；
  其中 `宪法第三十九条-导入包.std` 以仓库根为工作目录，经官方包与锁导入后证明查询；另有两条例外路径：
  根已证明但仍有无关未决冲突时不打印成功行；保守闭包无法清除 blocker 时 `:why` 失败关闭、退出 `2`。
  另有一条 `:inspect` 用例：结构化来源字段逐行输出，引文中的换行被转义、不会破坏行结构；
  两条 `:given` 用例（argv 与 stdin 交互）：登记事实的来源显示为「用户输入交互会话」，不出现空 `「」`。
- `crates/cli/tests/environment.rs`（30）：默认环境与 `std env` 端到端——仓库根下 `env` 打印
  `cn.default`、description、`official`、版本映射与锁哈希、锁校验与环境加载通过；`--profile cn`
  解析别名；`--no-default-packs` 下 env 报告未启用但仍校验锁，事实-only 示例加载失败并追加
  包名与 `import` 提示，显式导入示例仍通过；事实-only 示例在默认环境下 `:why` 证明并先打印预加载行；
  `:packs`/纯 REPL 启动不预加载；未知 profile、缺值/重复/互斥选项、选项写在文件/`env` 之后都是用法错误；
  临时注册表验证 profile 只加载环境内 official 包（`:inspect` 不含社区声明）、显式导入社区包标
  `（环境外：community）`、依赖闭包计入环境与预加载计数、社区包进 profile 需
  `--allow-community-packs`、版本不符/缺包/坏 profile/坏 theory/坏锁的错误与回滚；没有默认 profile 时
  批处理不打开注册表；没有 `lawpacks/` 时纯逻辑文件照常工作；环境准备成功但文件随后失败时
  不打印预加载行、REPL 重试只打印一次；缺包提示只出现在文件加载失败、已 import 的包不提示、
  profile 依赖包能被命名、`:why` 等查询错误不追加提示；namespace 与 name 不同或缺少 namespace
  的包不被建议 import，更长的不可导入 namespace 不会遮蔽同前缀可导入包。
- `crates/cli/tests/official_pack.rs`（12）：官方宪法包端到端——`:packs lawpacks` 列出
  `cn.constitution 0.4.0`、v0.4.0 描述、信任级别、文件数、覆盖计数、本体缺口与通过锁校验；
  导入示例的 `:why` 证明第三十九条；`:inspect` 对包内 128 个声明显示 `[cn.constitution@0.4.0]`；
  加载官方示例后，用户文件若声明 `namespace cn.constitution` 会被拒绝，`:inspect` 不出现注入的
  声明；`:audit` 命中 56 条带引文来源、核验条文哈希并打印 14/7/17/105 覆盖率与开放概念 49；
  临时案件只写国籍、非法拘禁、非法搜查事实时，包内规则推出第三十三/三十五/三十七/三十九/
  四十六条的七条结论；另一份临时案件用年龄、宗教强制、侮辱、非法检查通信、国家机关侵权损失、
  违法失职行为存在、劳动者、退休人员与年老事实，证明第二章第一批的十六条结论；只有国籍、没有
  违法失职行为事实时，申诉/控告/检举三项均保持缺口；只断言违法失职行为存在、没有任何个人受侵害
  或损失事实时，检举权仍能证明；第二章第二批用国籍加单一触发事实逐条证明第四十七、四十八、
  五十二至五十六条的十五条新规则；第三十四条在 `依法被剥夺政治权利` 成立时以 `unless` 阻断
  选举权和被选举权并保持缺口；在临时副本里改坏 `constitution.std` 后，`:packs` 因哈希不符
  退出 `2`、批处理 `:load` 退出 `1`。
- `crates/cli/tests/namespace.rs`（4）：模块与案件文件的端到端——`:inspect` 只给 namespaced 声明追加
  `[ns]` 后缀；限定名 `:why` 通过证书复核；`a` 的事实不满足 `b` 的目标；交换两个模块的加载顺序后
  `:why` / `:cert` 结果一致；模块内未限定引用加载失败。
- `crates/cli/tests/imports.rs`（31）：注册表导入端到端——临时 `lawpacks` + `std.lock` 后案件
  `import` 一个包并 `:why`；无 import 时没有注册表也能加载；缺锁、哈希不符（两个包的错误都列出）、
  锁缺包/多包、版本不符；坏清单、重复包名、重复 namespace、缺包；两个包同名后缀的限定名各自解析；
  包依赖 A→B 先加载 B，A/B 共用 C 时 C 只加载一次；后续 `:load` 复用已加载包，注册表随后变化时
  仍复核版本/哈希漂移；A→B→A 报环并给出路径；`../`、绝对路径、含 `:` 的 ADS 路径（`:lock` 仍可
  写锁，但包不可导入）、缺失文件、非 UTF-8、符号链接、重复 path、缺 path 的 theory 条目；
  manifest 缺 namespace、theory namespace 不符、没有 theory 文件；非 theory 条目被忽略；失败加载
  回滚声明与包信息；向自己 import 的包 namespace 声明同样被拒绝；`:inspect` 显示 `[a@0.1.0]`，
  直接按文件加载的 namespaced 模块仍是 `[a]`；已由文件加载的 namespace 被 import 时跳过注册表，
  混合 import 只解析包；批处理失败退出 `1`、显式 `:load` 退出 `2`。
- `crates/cli/tests/cert.rs`（21）：`:cert` / `:verify-cert` 端到端——导出的 JSON 往返并通过检查器；
  `:verify-cert` 分行报告逻辑与内核两段；缺口证书退出 `1` 且产生 `MissingPremise`；
  未决冲突产生 `UnresolvedConflict`；篡改结论或绑定在逻辑层失败；
  逻辑层接受、内核因绑定类型不符拒绝时退出 `2` 并给出节点；证书不存在、不是 JSON、未 `:load` 时失败。
  另含目标绑定与单点变异：删前提、换绑定、换结论、复用错误节点、追加已成立 blocker、
  改根后带目标失败/不带目标仍合法、合法目标通过、缺口根不能绑定目标、定义等价目标通过；
  以及含空格路径（不加引号只当路径、加引号可带目标）、缺根、目标无法解析；
  读证书失败的路径把换行/ESC/U+202E 转义成一行诊断；
  旧 `:check` 不再作为别名，报改名错误并退出 `2`。
- `crates/cli/tests/entry.rs`（19）：二进制入口端到端——批处理加载成功退出 `0` 并打印加载报告；
  坏文件退出 `1`，stderr 带路径与错误且不执行后续命令；坏语法批处理输出 `路径:行:列: error:`
  且路径只出现一次、不出现 `错误：` 前缀；`:load` 坏语法保留 `错误：` 前缀并带同样位置；
  精化错误没有 AST span 时输出 `路径: error: ...`，不伪造行列号；含空格路径按单个参数加载；
  `check` 子命令与直接给文件输出一致；加载后继续执行 `:why`；`--help` / `-h` 列出批处理与
  `:verify-cert`；`--version` / `-V` 输出 `std-deduce <版本>`；无参数与 `repl` 都进入 REPL；
  `check` 缺文件与 `repl` 带多余参数报用法错误（`2`）；文件后的 `--help`、首参未知选项、
  `check --help` 与 REPL 中的 `--foo` 都按未知选项退出 `2`，不静默忽略也不当文件；
  加载失败路径中的换行/ESC/U+202E 只产生一行转义诊断，Windows 反斜杠不被双写。
- `crates/cli/tests/audit.rs`（29）：`:audit` 端到端——带引文来源命中与正确哈希退出 `0`；规则带正确 `quote`
  加事实 `axiom` 无 `quote` 时仍退出 `0`（1 命中、1 无引文）；只有无引文来源时退出 `1` 并报“没有可核对的引文”，
  但仍打印覆盖声明；改一个字、哈希不符或格式非法、版本不符、无条号、多版本歧义、无对应语料、管辖不符退出 `1`；
  语料目录缺失或为空逐条报未核对并退出 `1`；坏 JSON、未知字段、布局错误（文件主干不符/嵌套目录）退出 `2`；
  未 `:load` 拒绝运行；来源字段含换行，或含 U+2028/U+202E/ESC/字面反斜杠时报告仍是正确的单行转义；
  多条来源分别计数；带 `text_sha256` 的语料会注明它只是未校验的出处元数据；非法 hash 不计入“已固定”；
  `coverage` 存在时按语料逐条打印形式化/部分/仅索引/待本体计数、形式化与部分条号、本体缺口计数与
  开放概念列表（多项、空列表、无 `notes`、多语料顺序），没有时打印“未声明”，覆盖率文本同样转义。
- `crates/cli/tests/packs.rs`（28）：`:packs` / `:lock` 端到端——合法清单逐行输出、信任级别、
  含空格目录、好包+坏清单、根不存在/空目录、默认 `lawpacks`、悬空清单符号链接、description/错误/
  路径中的换行、不可见格式字符、ESC、字面反斜杠与控制字符转义；清单 `corpus` 链接读取语料并打印
  覆盖与本体缺口、缺失语料退出 `2`、非法链接由清单校验拒绝；`:lock` 写锁、锁缺失/版本不符/
  哈希不符/多包/锁符号链接、坏包不覆盖旧锁、示例锁一致。
- `crates/lawpack/tests/corpus.rs`（52）：语料 JSON 必填/可选字段、未知字段、格式版本、`law` 字符集、
  坏日期、坏哈希、空 `articles`、空白归一化后的重复条号；v2 台账的解析、状态计数、条号一一对应与
  顺序、缺条/多条/重复、`formalized` 无 `rules`、`partial` 无 `note`、`needs_ontology` 无 `gap`/
  未知 `gap`、`indexed` 带 `rules` 或 `gap`、死 `gaps` 条目、规则名跨条重复等拒绝；开放概念空白/
  首尾空白/重复与 `coverage` 内未知字段；扫描的稳定顺序、坏 JSON、缺失根目录，以及严格布局拒绝根下
  文件、非 `.json` 文件、嵌套目录、空法律目录、目录名与 `law` 不符、文件名主干与 `version` 不符；
  引文核对的精确命中、空白/换行差异、改字/标点/大小写/数字失败、无 quote/无语料/无条号/版本不符/
  多版本歧义、哈希命中/不符/格式非法与“未到达时不标记为已核验”、管辖不符、标题与别名匹配；
  仓库内宪法语料的字段、143 条连续且规范的条号、六条条文精确正文、14/7/17/105 与 82/11/3/3/2/1/1/1/1
  的覆盖计数、56 条规则名与 `.std` 条号逐条一致，以及条文正文不含条号前缀。
- `crates/lawpack/tests/lawpack.rs`（28）：清单必填/可选字段、字符集与长度、真实日历日期（含闰年）、
  未知字段、空日期、目录扫描、坏清单、悬空清单 symlink、symlink 越界、junction 越界与 `load` 的全有或全无语义；
  信任级别缺省 `community`、`official` 解析、未知值拒绝与排序；`corpus` 链接可选、空值视为未声明、
  格式与路径分隔符/`..` 校验。
- `crates/lawpack/tests/profile.rs`（23）：profile 解析与扫描——必填/可选字段、profile 缺省 `official`、
  无效名称/别名、重复包条目、空 packs、坏版本约束、未知字段、多个 default、重复 profile 名/alias、
  alias 与 profile 名冲突、缺失 `profiles/`、非 `.toml` 文件、子目录、文件与目录符号链接、坏 TOML、
  一次列出全部错误；版本前缀匹配正反例；默认/按名/按别名选择与未知 profile 的可用列表。
- `crates/lawpack/tests/lock.rs`（27）：锁文件往返、哈希确定性、改一字节即变、CRLF/LF 同哈希、
  NUL 拼接歧义回归、包内 `std.lock` 参与哈希、包内 symlink/非普通文件拒绝、缺锁/缺包/多包/
  版本与哈希不符、锁符号链接、坏锁版本与坏 TOML、示例锁校验。
