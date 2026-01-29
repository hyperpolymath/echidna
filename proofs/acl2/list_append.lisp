; SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
; SPDX-License-Identifier: MIT OR Palimpsest-0.6

;; List append properties
;; Demonstrates recursive definitions and list reasoning

(defun my-append (xs ys)
  (if (endp xs)
      ys
    (cons (car xs) (my-append (cdr xs) ys))))

(defthm append-nil
  (implies (true-listp xs)
           (equal (my-append xs nil) xs))
  :hints (("Goal" :induct (my-append xs nil))))

(defthm append-associative
  (equal (my-append (my-append xs ys) zs)
         (my-append xs (my-append ys zs)))
  :hints (("Goal" :induct (my-append xs ys))))

(defun list-length (xs)
  (if (endp xs)
      0
    (+ 1 (list-length (cdr xs)))))

(defthm length-append
  (equal (list-length (my-append xs ys))
         (+ (list-length xs) (list-length ys)))
  :hints (("Goal" :induct (my-append xs ys))))
