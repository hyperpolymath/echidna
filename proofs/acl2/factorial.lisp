; SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
; SPDX-License-Identifier: MIT OR Palimpsest-0.6

;; Factorial function with guards
;; Demonstrates ACL2's guard verification and executable specifications

(defun fact (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (fact (- n 1)))))

(defthm fact-positive
  (implies (natp n)
           (posp (fact n)))
  :hints (("Goal" :induct (fact n)))
  :rule-classes :type-prescription)

(defun fact-tail (n acc)
  (declare (xargs :guard (and (natp n) (posp acc))))
  (if (zp n)
      acc
    (fact-tail (- n 1) (* n acc))))

(defthm fact-tail-correct
  (implies (and (natp n) (posp acc))
           (equal (fact-tail n acc)
                  (* (fact n) acc)))
  :hints (("Goal" :induct (fact-tail n acc))))
