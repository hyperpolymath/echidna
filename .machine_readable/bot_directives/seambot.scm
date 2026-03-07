;; SPDX-License-Identifier: PMPL-1.0-or-later
(bot-directive
  (bot "seambot")
  (scope "integration health")
  (allow ("analysis" "contract checks" "docs updates"))
  (deny ("code changes without approval"))
  (notes "May add integration test suggestions"))
