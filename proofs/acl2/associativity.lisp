; SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
; SPDX-License-Identifier: AGPL-3.0-or-later

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
