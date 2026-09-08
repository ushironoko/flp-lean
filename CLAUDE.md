# flp-lean

FLP 不可能性定理 (Fischer–Lynch–Paterson 1985) の Lean 4 形式化。

## ビルドと検証

```
lake build
```

- ツールチェーンは `lean-toolchain` に固定 (Lean 4.33.1、elan 管理)
- Mathlib には依存しない。Lean 4 core のみで完結させる。新たな依存を追加しない
- 完了条件は 3 つ: `lake build` が警告ゼロで通る、`sorry`/`admit` がゼロ、主定理の公理が `propext` / `Classical.choice` / `Quot.sound` のみ
- 公理チェックは一時ファイルに `import FlpLean` と `#print axioms FLP.flp_impossibility` を書き `lake env lean <file>` で行う

## 構成

依存は上から下への一方向。

| ファイル | 内容 |
|---|---|
| `FlpLean/Model.lean` | プロトコル・配置・イベント・`run`/`applicable`/`reach`・決定。永続性 `enabled_apply_of_ne`、可換性 `apply_comm` (Lemma 1)、安定性 `decided_run` |
| `FlpLean/Bivalence.lean` | `canDecide`/`bivalent`/`valent`、有限形停止性 `FinTerm`、Lemma 2 `exists_bivalent_init`、Lemma 3 `bivalent_step` |
| `FlpLean/Runs.lean` | 無限実行 `OmegaRun`、`admissible`、`Terminating`、公平スケジューラ構成 (`BlockSpec`/`procList`/`cfgSeq`/`cfgSeq_fair`)、`finTerm_of_terminating` |
| `FlpLean/FLP.lean` | 主定理 `flp_impossibility`、可算メッセージ版 `flp_impossibility_countable` |
| `FlpLean/Sanity.lean` | 3 仮定のどの 2 つも充足可能であることを示す具体プロトコル |

## 形式化上の決定 (変更しない)

- 停止性は原論文の形 (admissible な無限実行はすべて決定する) で仮定し、証明で使う有限形 `FinTerm` はそこから導出する。`FinTerm` を仮定に格上げしない
- イベント可算性は全射 `g : Nat → Event` として明示する。原論文のキュー構成の代替
- プロセス数の仮定は `0 < n`。`n ≥ 2` は不要
- `Sanity.lean` は仮定が不整合でないことの証拠なので、仮定の定義を変えたら必ず追随させる

## Lean core での書き方

- `by_contra`、`set`、`split_ifs` は Mathlib のもので使えない。`Classical.byContradiction`、`by_cases`、`split` を使う
- `rcases`/`obtain`/`rintro`/`omega` は core にあるので使ってよい
- `open Classical in` で `if` を使う定義は `noncomputable def` にする
- セクション変数 `[DecidableEq Msg]` を使わない定理は `omit [DecidableEq Msg] in` を前置して警告を消す
- `simp [leaderP]` のように構造体定義を丸ごと展開すると `run` の項が壊れて `rw` が失敗する。射影ごとの `rfl` 補題を用意して `rw` する
- Nat の切り捨て減算を含む算術は `by_cases` で `if` を消してから `omega`

## ドキュメント

- docstring と README は日本語。原論文の Lemma 番号との対応を必ず書く
- README の対応表 (`Sanity.lean` の表、原論文との差分) は定理や仮定を変えたら更新する
