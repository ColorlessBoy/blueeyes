# BlueEyes

这是一个 Lean 4 + Mathlib 小项目，用来形式化“红眼睛 / 绿眼睛”经典逻辑题。项目包含一层
Kripke-style 认识逻辑模型、有限参与者上的具体计数模型，并在其上给出经典解法使用的计数归纳证明。

## 问题背景

经典题目可以概括为：

- 每个人都能看见其他人的眼睛颜色，但看不见自己的眼睛颜色；
- 公开宣布：至少有一个人是红眼睛；
- 如果某人能够推出自己是红眼睛，就会在当晚离开；
- 如果连续若干晚没有人离开，这件事本身也会成为公共信息。

项目现在分成两层：

- 认识逻辑层：定义世界、观察不可区分关系、知识算子、公共知识、公开公告、无人离开的公共更新；
- 状态转移层：定义夜晚状态、离开报告，以及观察到离开名单后的模型更新；
- 有限计数层：使用 Mathlib 的 `Fintype` 和 `Finset` 定义红眼者集合、总红眼人数、某人看到的红眼人数；
- 计数归纳层：把具体世界按“看到多少红眼者 / 总共有多少红眼者”抽象，证明经典解法的核心归纳。

最关键的归纳结构是：

> 公开宣布后，连续 `k` 晚无人离开，会排除所有“红眼人数不超过 `k`”的可能世界。

因此，如果实际有 `r > 0` 个红眼者，每个红眼者都会看到 `r - 1` 个红眼者；经过 `r - 1`
个安静夜晚后，“自己不是红眼者”的可能世界会被排除，于是他们能推出自己是红眼者。

## 项目结构

- `BlueEyes/Puzzle.lean`：主要形式化文件
- `BlueEyes.lean`：库入口
- `docs/index.html`：面向阅读的 HTML 展示页
- `lakefile.lean`：Lake 项目配置
- `lean-toolchain`：Lean 版本固定为 `leanprover/lean4:v4.28.0`
- Mathlib：`lakefile.lean` 中依赖 `mathlib4` 的 `v4.28.0`

## HTML 展示页

项目包含一个静态文档页，用更直观的方式展示逻辑题、交互推演和 Lean 4 形式化细节：

```text
docs/index.html
```

直接用浏览器打开该文件即可阅读。

## 核心定义

`World Agent`

表示一个可能世界，即从每个参与者到其眼睛颜色的赋值。

`indistinguishable i w v`

表示参与者 `i` 在世界 `w` 和 `v` 中看到的其他人完全相同，因此无法区分这两个世界。

`Knows M i w P`

表示在当前公共模型 `M` 中，参与者 `i` 在世界 `w` 知道命题 `P`。

`publicAnnouncement M A`

表示公开宣布命题 `A` 后，将当前模型 `M` 限制到满足 `A` 的世界。

`afterQuietNights n`

表示公开宣布“至少有一个红眼者”之后，又连续经历 `n` 个无人离开的夜晚后剩余的公共模型。

`CommonKnowledge M P`

表示命题 `P` 在模型 `M` 中成为公共知识，即所有有限层级的“人人知道、人人知道人人知道、...”都成立。

`NightState Agent`

表示一个夜晚开始时的动态状态，包括当前公共模型和仍在场的参与者。

`nextNightState S actual`

根据实际世界 `actual` 中会离开的参与者生成离开报告，并用这个报告更新公共模型和在场者集合。

`redAgents w`

在具体有限世界 `w` 中，所有红眼者组成的 `Finset`。

`totalRed w`

世界 `w` 中红眼者总数，即 `redAgents w` 的基数。

`seenRed i w`

参与者 `i` 在世界 `w` 中看到的红眼者数量，也就是把 `i` 自己从红眼者集合中移除后的基数。

`compatibleWithObservation seen totalRed`

表示一个人看到 `seen` 个红眼者时，认为总红眼人数 `totalRed` 与观察相容。可能性只有两个：

- `totalRed = seen`：自己不是红眼者；
- `totalRed = seen + 1`：自己是红眼者。

`possibleAfterQuietNights quietNights seen totalRed`

表示在公开宣布“至少有一个红眼者”，并且已经有 `quietNights` 个夜晚无人离开后，
`totalRed` 仍然是一个与观察相容的可能总红眼人数。

## 核心定理

`afterGuruAnnouncement_iff`

公开宣布后的模型恰好排除了没有红眼者的世界。

`afterOneQuietNight_iff`

一个无人离开的夜晚会把模型更新为“仍在模型中，并且没有任何人知道自己是红眼者”的世界。

`commonKnowledge_unfold`

公共知识的固定点展开：`P` 是公共知识，当且仅当 `P` 成立，并且人人都知道 `P` 是公共知识。

`updateModelBy_empty_report_eq_quiet`

当观察到的离开报告为空时，显式状态转移中的模型更新等于原先的 quiet-night 更新。

`not_knows_red_if_green_variant_possible`

如果把某人的眼睛改成绿色后得到的世界仍然可能，且这个改变对该人不可观察，那么该人不能知道自己是红眼者。

`seenRed_eq_of_indistinguishable`

不可区分世界中，参与者看到的红眼人数相同。

`compatibleWithConcreteObservation`

具体有限世界会导出计数相容性：某人看到 `seenRed i w` 个红眼者时，真实总数一定是
`seenRed i w` 或 `seenRed i w + 1`。

`possibleAfterQuietNights_of_concrete`

把具体有限世界接入计数归纳层：只要公告成立，并且安静夜晚给出 `quietNights < totalRed w`，
就得到 `possibleAfterQuietNights quietNights (seenRed i w) (totalRed w)`。

`afterQuietNights_count_lower_bound`

从 Kripke 更新语义直接推出计数下界：如果世界 `w` 仍在 `afterQuietNights n` 中，
那么 `n < totalRed w`。

`possibleAfterQuietNights_of_afterQuietNights`

把具体 Kripke 模型中的剩余世界自动送入计数谓词；这里的下界不再是外部假设，而是由
`afterQuietNights_count_lower_bound` 归纳推出。

`not_afterQuietNights_of_totalRed_le`

如果世界 `w` 的红眼总数不超过 `n`，它不可能在 `n` 次安静夜晚更新后仍然存在。

`redAgent_wouldLeave_after_seenQuietNights`

具体 Kripke 层的叙事结论：红眼者在经历“自己看到的红眼人数”那么多个安静夜晚后，会知道自己是红眼者并离开。

`allRedAgents_wouldLeave_on_decisiveNight`

所有红眼者在同一个决定性夜晚离开：如果实际世界 `w` 经过 `totalRed w - 1` 个安静夜晚仍然是当前世界，
那么每个红眼者都会在这一晚知道自己是红眼者。

`allRedTwo_everyoneKnows_atLeastOneRed`

两个人都红的实际世界中，在初始模型下，每个人都知道“至少有一个红眼者”。

`allRedTwo_not_commonKnowledge_atLeastOneRed`

但同一个实际世界中，“至少有一个红眼者”并不是公共知识。原因是：某人仍认为自己可能是绿眼；
在那个可能世界里，另一个人又会认为全绿世界可能。

`allRedTwo_not_commonKnowledge_everyoneKnows_atLeastOneRed`

更强地说，即使实际世界里“每个人都知道至少有一个红眼者”为真，这件事本身也不是公共知识。

`redEyedPerson_knows_concrete_total`

具体世界版本的决定性结论：红眼者经过自己看到的红眼人数那么多个安静夜晚后，任何仍相容的总红眼人数都等于实际总数。

`redEyedPerson_knows_after_quietNights`

如果实际红眼人数是 `r > 0`，那么红眼者看到 `r - 1` 个红眼者。经过 `r - 1`
个安静夜晚后，任何仍然可能的总红眼人数都必须等于 `r`。

`oneRedPerson_knows_immediately`

单个红眼者的基础情形：如果某人看不到其他红眼者，公开宣布“至少有一个红眼者”后，
他立即能推出自己是红眼者。

`redEyedPerson_knows_after_seeing_n`

用“看到 `n` 个红眼者”的方式陈述一般结论：经过 `n` 个安静夜晚后，
该红眼者能推出总红眼人数是 `n + 1`。

`greenEyedPerson_still_has_two_possibilities`

绿眼者看到 `r` 个红眼者时，在 `r - 1` 个安静夜晚后仍然有两个相容可能：
总红眼人数是 `r` 或 `r + 1`。这说明决定性夜晚离开的是红眼者，而不是绿眼者。

`eliminated_by_quietNights`

如果 `totalRed ≤ quietNights`，那么经过 `quietNights` 个安静夜晚后，
该总红眼人数已经被排除。

## 具体示例

文件末尾定义了一个固定三人世界：

```lean
def twoRedOneGreen : World (Fin 3)
```

其中 `0` 和 `1` 是红眼者，`2` 是绿眼者。Lean 已证明：

- `twoRedOneGreen_totalRed : totalRed twoRedOneGreen = 2`
- `twoRedOneGreen_seenRed_zero : seenRed 0 twoRedOneGreen = 1`
- `twoRedOneGreen_seenRed_one : seenRed 1 twoRedOneGreen = 1`
- `twoRedOneGreen_after_one_quiet_night`：第一晚确实无人离开；
- `twoRedOneGreen_reds_leave_together`：第二晚两个红眼者一起离开。

文件还包含一个两人全红的认识逻辑反例：

```lean
def allRedTwo : World (Fin 2)
```

Lean 证明了：

- `allRedTwo_everyoneKnows_atLeastOneRed`：每个人都知道至少有一个红眼者；
- `allRedTwo_not_commonKnowledge_atLeastOneRed`：但“至少有一个红眼者”不是公共知识；
- `allRedTwo_not_commonKnowledge_everyoneKnows_atLeastOneRed`：甚至“每个人都知道至少有一个红眼者”这件事也不是公共知识。

同样也包含你关心的五人全红版本：

```lean
def allRedFive : World (Fin 5)
```

Lean 已证明：

- `allRedFive_everyoneKnows_atLeastOneRed`：五人全红时，每个人都知道至少有一个红眼者；
- `allRedFive_not_commonKnowledge_atLeastOneRed`：但“至少有一个红眼者”仍然不是公共知识；
- `allRedFive_not_commonKnowledge_everyoneKnows_atLeastOneRed`：甚至“每个人都知道至少有一个红眼者”也不是公共知识。

证明使用的可能世界链是：

```text
RRRRR ~ GRRRR ~ GGRRR ~ GGGRR ~ GGGGR ~ GGGGG
```

每一步只改变当前观察者自己的颜色，因此对该观察者不可区分。最后到达全绿世界，与
`AtLeastOneRed` 矛盾。

## 检查方式

在项目根目录运行：

```bash
lake build
```

也可以只检查主文件：

```bash
lake env lean BlueEyes/Puzzle.lean
```

## 形式化边界与后续扩展

当前版本已经包含认识逻辑的核心构件、公共知识固定点、显式离开状态转移、公共更新语义、
有限世界计数，以及从 `afterQuietNights` 的 Kripke 更新自动推出计数下界的归纳证明。
也就是说，文件中既有具体世界层，也有把具体世界压缩成红眼人数后的归纳证明层。

如果后续要继续扩展，可以进一步加入：

- 把“非空离开报告”与“所有红眼者同晚离开”的故事结论进一步包装成高层定理；
- 为固定人数的具体岛民构造可执行示例；
- 将 HTML 文档中的交互推演直接映射到 Lean 中的具体 `Fin n` 世界。
