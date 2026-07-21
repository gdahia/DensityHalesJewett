# Repository Guidelines

## Lean proof style

Prefer goal-directed, linear proofs over accumulating many named intermediate facts.

When writing or refactoring proofs:

1. Normalize the goal early using `rw`, `unfold`, `dsimp`, or `simp` when this reveals the relevant theorem or definition.
2. Apply the main closing theorem as soon as possible.
3. Prefer

   ```lean
   refine theorem_name existing_arg ?_ existing_hypothesis ?_
   ```

   followed by bullet subgoals, rather than proving all premises with separate `have` statements first.
4. Pass hypotheses already present in the context directly as theorem arguments. Do not create subgoals whose proof is only `exact h`.
5. Use `?_` placeholders for premises that require actual derivations. Solve the resulting goals with bullets in argument order.
6. Use `suffices P by ...` only when `P` is a meaningful logical or mathematical reduction of the goal. Do not use `suffices h : lhs = rhs by rw [h]` merely to manufacture a one-use rewrite rule.
7. Avoid parenthesized inline proofs such as `(by ...)` inside long theorem applications. Expose substantial proofs as bullet subgoals instead.
8. Refrain from using `calc` blocks. Prefer a linear sequence of `rw`, `simp`, `apply`, `refine`, `suffices`, and direct closing tactics. Keep or introduce a `calc` block only when the intermediate expressions themselves communicate an essential mathematical chain more clearly than goal-directed steps would.
9. Avoid a named `have` when:
   - the fact is used exactly once;
   - it merely supplies the next theorem argument; and
   - turning it into a subgoal does not obscure its meaning.
   In particular, if the only use of a `have` is that its fact is later picked up implicitly from the local context by `linarith`, `nlinarith`, `omega`, `grind`, or similar automation, remove the `have`. Replace it with a more linear argument following the rules above: normalize the goal first, pass the fact explicitly to the tactic when supported, apply or refine the theorem that needs the fact and prove it as a bullet subgoal, or restructure the final automation call so it closes the goal directly. A fact's implicit presence in an automation tactic's context does not count as reuse and does not justify naming it with `have`.
10. Keep a named `have` when:
    - the fact is reused;
    - its name communicates an important mathematical idea;
    - it separates logically distinct phases of the proof; or
    - inlining it would make elaboration or error messages significantly harder to understand.
11. Avoid non-idiomatic lambda expressions. Prefer named lemmas, direct theorem application, eta-reduced functions, or `intro` and bullet subgoals over embedding substantial proofs in `fun x => ...` terms. Use a lambda only when the function itself is the natural object required by the surrounding theorem or construction.
12. Do not use the `show P by ...` pattern. State or expose the intended goal with `change`, `suffices`, or a typed theorem application instead. If an explicitly typed inline proof is strictly necessary, write `(by ... : P)` rather than `show P by ...`.
13. Keep rewriting linear and idiomatic. Do not place tactic-generated equalities or substantial proof terms inside an `rw` list, such as `rw [(by ... : lhs = rhs)]`, and do not use lambdas merely to manufacture rewrite rules. When expressions do not yet match, use the following order of preference:
    1. Rewrite directly with an existing lemma using `rw [lemma]`.
    2. Normalize the goal directly with `simp`, `ring_nf`, `norm_num`, `field_simp`, `push_cast`, or another appropriate normalization tactic.
    3. Use `change` when the desired statement is definitionally equal to the current goal.
    4. Use `simpa [lemmas] using theorem_or_hypothesis` when an existing result has the desired content after simplification.
    5. Use `convert theorem_or_hypothesis using 1` when the main result is already clear and only propositional equalities between its conclusion and the goal remain; solve those equality subgoals directly.
    6. Use `suffices` only when the intermediate proposition has genuine mathematical or logical meaning, not merely as a one-use rewrite equality.
    Use `nth_rewrite` when only a particular occurrence should change, and `conv` when a rewrite must target a precise subexpression.
14. After refactoring, build the affected Lean module with Lake, for example
    `lake build DenseSetsWithoutLargeSumsets.RuzsaSumOfSets`, rather than relying only on
    `lake env lean DenseSetsWithoutLargeSumsets/RuzsaSumOfSets.lean`. The direct Lean command
    may compile successfully without running the project linters used by
    `lake build`. Inspect the complete Lake output and resolve every warning
    and associated `info:` message attributed to the affected file. In
    particular, replace flexible goal-modifying tactics with the explicit
    `simp only [...]` form suggested by `simp?` when appropriate, and use
    bullets whenever a tactic would otherwise operate while multiple goals
    are active. Rebuild until the affected module emits no warnings or info
    messages. Do not suppress linters merely to hide messages without explicit
    justification, and do not trade readability for fragile elaboration or
    substantially slower proofs.
15. Never increase Lean's maximum heartbeat limit without explicit user instruction or approval. This includes local `set_option maxHeartbeats` declarations and project-wide heartbeat settings. Refactor or optimize the proof first; if a higher limit still appears necessary, ask the user before changing it.

For example:

```lean
-- Avoid when the facts are used only once:
have hx : P := by
  ...
have hy : Q := by
  ...
apply final_theorem hx hy h

-- Prefer:
refine final_theorem ?_ ?_ h
· ...
· ...
```

These guidelines do not prohibit `have` entirely. Named intermediate facts remain useful when they represent meaningful mathematical milestones or are used more than once.
