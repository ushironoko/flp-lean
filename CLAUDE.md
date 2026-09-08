# flp-lean

## 制約

- Mathlib に依存しない。Lean 4 core のみで完結させ、新たな依存を追加しない
- 完了条件: `lake build` が警告ゼロで通る、`sorry`/`admit` ゼロ、主定理の公理が `propext` / `Classical.choice` / `Quot.sound` のみ
- 公理チェックは一時ファイルに `import FlpLean` と `#print axioms <定理名>` を書き `lake env lean <file>` で行う

## 変更しない決定

- 停止性は原論文の形 (admissible な無限実行はすべて決定する) で仮定し、有限形はそこから導出する。有限形を仮定に格上げしない
- イベント可算性は全射 `g : Nat → Event` として明示する
- プロセス数の仮定は `0 < n` のまま
- `Sanity.lean` は仮定が不整合でないことの証拠なので、仮定の定義を変えたら必ず追随させる

## Lean core での書き方

- `by_contra`、`set`、`split_ifs` は Mathlib のもので使えない。`Classical.byContradiction`、`by_cases`、`split` を使う
- `open Classical in` で `if` を使う定義は `noncomputable def` にする
- セクション変数を使わない定理は `omit [...] in` を前置して警告を消す
- 構造体定義を `simp` で丸ごと展開すると `run` の項が壊れて `rw` が失敗する。射影ごとの `rfl` 補題を用意して `rw` する
- Nat の切り捨て減算を含む算術は `by_cases` で `if` を消してから `omega`

## ドキュメント

- docstring と README は日本語。原論文の Lemma 番号との対応を書く
- 定理や仮定を変えたら README の表も更新する
