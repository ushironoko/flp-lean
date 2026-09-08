# flp-lean

FLP 不可能性定理 (Fischer, Lynch, Paterson 1985) の Lean 4 による形式化。
Mathlib には依存せず、Lean 4 core (v4.33.1) のみで証明が完結する。
`sorry` はなく、依存する公理は `propext` / `Classical.choice` / `Quot.sound` のみ。

```
lake build
```

## 定理

```lean
theorem FLP.flp_impossibility
    (P : Protocol n State Msg) (hn : 0 < n)
    (g : Nat → Event n Msg) (hg : ∀ e, ∃ m, g m = e)
    (hAgree : Agreement P) (hNT : Nontrivial P) (hTerm : Terminating P) : False
```

非同期メッセージ通信モデル上の決定的プロトコル `P` が、合意 (Agreement)・
非自明性 (Nontrivial)・1 故障許容の停止性 (Terminating) を同時に満たすことはない。
`g` はイベント集合が可算であるという仮定で、メッセージ集合が可算なら自動的に得られる
(`flp_impossibility_countable`)。

## モデル (`Model.lean`)

FLP 論文の定義に従う。

| 概念 | 定義 |
|---|---|
| プロセス | `Fin n` |
| プロトコル | `Protocol n State Msg`: 遷移関数 `step : Fin n → State → Option Msg → State × List Msg`、決定出力 `out : State → Option Bool`、初期状態 `initSt` |
| 配置 | `Config`: 各プロセスの状態 `st` と、メッセージバッファ `buf : Msg → Nat` (多重集合) |
| イベント | `Event = Fin n × Option Msg`: プロセス `p` がメッセージ `m` (または空メッセージ `none`) を受信 |
| `enabled c e` | `none` は常に可能。`some m` は `m` の宛先が `p` かつバッファに存在 |
| `apply c e` | `p` の状態を遷移させ、`m` をバッファから 1 つ除き、送信メッセージを追加 |
| `decided c v` | ある状態が `out = some v` |

プロトコルに課す公理は「初期状態は未決定」(`out_init`) と「一度決定したら変わらない」(`out_stable`) の 2 つだけ。

モデルから証明される基本性質:
- 永続性 `enabled_apply_of_ne`: 別のイベントを適用しても有効なイベントは有効なまま
- 可換性 `apply_comm`: 異なるプロセスのイベントは可換 (FLP Lemma 1)
- 安定性 `decided_run`: 決定は以後の配置でも保たれる

## 仮定 (`Runs.lean`, `FLP.lean`)

- `Agreement P`: 到達可能な配置で `true` と `false` が同時に決定されることはない
- `Nontrivial P`: 各値 `v` について、`v` を決定しうる初期配置が存在する
- `Terminating P`: 初期配置から始まる任意の admissible run は決定に至る

`OmegaRun` は無限実行 (有限スケジュールの列 `sched` と配置列 `cfg`)。
`correct r q` は「`q` が無限回ステップし、`q` 宛の有効なイベントがいつか必ず実行される」。
`admissible r` は「任意の 2 プロセスのうち少なくとも一方は correct」、すなわち故障プロセスは高々 1 つ。

## 証明の構成

1. `Runs.lean` `finTerm_of_terminating`: `Terminating` から有限形の停止性 `FinTerm`
   (到達可能な任意の配置から、任意のプロセス `p` を除いた有限スケジュールで決定に至れる) を導く。
   `p` を最初から故障させ、他のプロセスに公平なスケジューラ (`cfgSeq` / `stageSched`) を構成する。
2. `Bivalence.lean` `exists_bivalent_init`: 両価な初期配置が存在する (FLP Lemma 2)。
   入力を 1 プロセスずつ反転させる列 `mix` と `agreeExcept` による論証。
3. `Bivalence.lean` `bivalent_step`: 両価な配置と有効なイベント `e` に対し、
   `e` を含むスケジュールで再び両価な配置に到達できる (FLP Lemma 3)。
4. `FLP.lean` `flp_impossibility`: Lemma 3 を各イベントに順に適用する公平なスケジューラで
   admissible かつ永遠に両価な run を構成し、`Terminating` と `Agreement` に矛盾させる。

公平スケジューラは `Nat → Event` の全射 `g` を使い、第 `k` 段で `g 0, …, g k` を順に処理する。
これにより、有効になったイベントは必ずいつか実行される (`cfgSeq_fair`)。

## 健全性チェック (`Sanity.lean`)

仮定が不整合ではないことを具体例で確認する。

| プロトコル | Agreement | Nontrivial | Terminating |
|---|---|---|---|
| `constP` (常に false を決定) | ✓ | ✗ | ✓ (n ≥ 2) |
| `ownP` (自分の入力を決定) | ✗ | ✓ | ✓ (n ≥ 2) |
| `leaderP` (プロセス 0 のみ決定) | ✓ | ✓ | ✗ (主定理より) |

## 原論文との対応

- 停止性は「admissible run はすべて決定する」という原論文の形で仮定し、
  証明内で使う有限形 `FinTerm` はそこから導出している。
- イベント集合の可算性 `g` は、原論文がスケジュールをキューで構成する箇所を
  全射による列挙で置き換えるために必要となる。メッセージが有限ビット列である通常の設定では自動的に満たされる。
- 原論文は `n ≥ 2` を仮定するが、本形式化では `0 < n` で十分である
  (`n = 1` では唯一のプロセスが故障した run が決定しないため、仮定が直ちに矛盾する)。
