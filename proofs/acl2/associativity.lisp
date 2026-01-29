; SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
; SPDX-License-Identifier: MIT OR Palimpsest-0.6

;; Associativity of addition
;; Demonstrates ACL2's automated proof with induction

(defun plus (x y)
  (if (zp x)
      y
    (+ 1 (plus (- x 1) y))))

(defthm plus-associative
  (implies (and (natp x) (natp y) (natp z))
           (equal (plus (plus x y) z)
                  (plus x (plus y z))))
  :hints (("Goal" :induct (plus x y))))
