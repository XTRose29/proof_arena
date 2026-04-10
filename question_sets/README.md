# Question Sets

Put one subfolder per question here.

Suggested layout:

```text
proof_arena/question_sets/
  thick_thin_decomposition/
    solution_a.lean
    solution_b.lean
  liyau1d/
    human.lean
    model_x.lean
    model_y.lean
```

Rule:

- Each subfolder should contain only solutions for the same question.
- Different questions should go in different subfolders.
- The app now uses this folder structure as the primary grouping rule.

How to add data:

1. Create a new subfolder for the question.
2. Put one or more `.lean` solutions in that subfolder.
3. Restart the proof arena server if it is already running.

Notes:

- The folder name becomes the question key shown by the app.
- Each `.lean` file is treated as one full proof.
- `NODE` annotations are used for node-level comparison modes.
- If a file has no `NODE` blocks, it can still appear in full-proof comparisons.
