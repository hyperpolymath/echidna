; SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
; SPDX-License-Identifier: MPL-2.0

(in-package "ACL2")

(include-book "std/lists/top" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)

(defconst *one* 1)

(defun double (x)
  (* 2 x))

(defthm double-of-zero
  (equal (double 0) 0)
  :hints (("Goal" :in-theory (enable double))))

(defthm double-is-even
  (evenp (double x))
  :hints (("Goal" :induct (double x)
                  :in-theory (e/d (double) (evenp)))))

; HAZARD: defaxiom — postulates without proof.
(defaxiom sketchy-ax
  (equal (foo x) (bar x)))

; HAZARD: skip-proofs — trusts the wrapped form unconditionally.
(skip-proofs
 (defthm wholly-trusted
   (equal 1 2)))
