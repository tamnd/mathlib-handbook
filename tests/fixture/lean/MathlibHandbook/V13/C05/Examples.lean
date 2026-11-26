import Mathlib

-- anchor: closedUnitBall
example : IsCompact (Metric.closedBall (0 : ℝ) 1) :=
  isCompact_closedBall 0 1
-- end: closedUnitBall
