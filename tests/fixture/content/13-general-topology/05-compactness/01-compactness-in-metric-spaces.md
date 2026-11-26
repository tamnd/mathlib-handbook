---
title: Compactness in metric spaces
kind: theory
modules:
  - Mathlib.Topology.MetricSpace.Bounded
explains:
  E3: [Metric.isCompact_iff_isClosed_bounded]
  E1: auto
families: [F-simp]
requires: [V13.C02]
reads_with: ["Rud76 §2.C"]
lean: [MathlibHandbook/V13/C05/Examples.lean]
mathlib: 4472534b607bbff9621756cca1be340c60e7272a
status: drafted
drafted_by: writer@fixture
reviewed_by: []
---

## Compactness in metric spaces

### Overview

In a proper metric space, a set is compact if and only if it is closed and bounded. This section states the result and shows the form that Mathlib gives.

### Definitions

**Definition (Bounded set).** A set $S$ of a metric space is bounded when it is in a ball.

### Theorems and proofs

**Theorem (Heine and Borel).** In a proper metric space, a set is compact if and only if it is closed and bounded.

*Proof.* A closed ball is compact in a proper space, and a closed subset of a compact set is compact. $\square$

::: mathlib
`Metric.isCompact_iff_isClosed_bounded` · `Mathlib.Topology.MetricSpace.Bounded`

Mathlib states the result for a `ProperSpace`. The lemma `Metric.isBounded_closedBall` gives the bound. See [the page](/decl/Metric.isCompact_iff_isClosed_bounded/).

<?decl Metric.isCompact_iff_isClosed_bounded?>
:::

### Examples

**Example (The unit ball).** The closed unit ball of $\mathbb{R}$ is compact.

<?lean MathlibHandbook/V13/C05/Examples.lean#closedUnitBall?>

**Counterexample (An open interval).** The interval $(0, 1)$ is bounded and not closed, and it is not compact.

### The library around it

The simp lemmas of the module give the bounds of balls.

### Exercises

1. (A) Show that a finite set is compact.
2. (A) Show that a closed ball of $\mathbb{R}$ is bounded.
3. (B) Show that $\mathbb{Z}$ is closed and not compact.
4. (L) Prove in Lean that the closed unit ball is compact.

### Notes and history

The result is due to Heine and Borel.

### Reference

<?reference?>
