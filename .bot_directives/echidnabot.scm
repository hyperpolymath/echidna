;; SPDX-License-Identifier: PMPL-1.0-or-later
(bot-directive
  (bot "echidnabot")
  (scope "formal verification and fuzzing")
  (allow ("analysis" "fuzzing" "proof checks"))
  (deny ("write to core modules" "write to bindings"))
  (notes "May open findings; code changes require explicit approval"))
