; SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
; SPDX-License-Identifier: MIT OR Palimpsest-0.6

;; Binary tree operations
;; Demonstrates data structure reasoning

(defun tree-p (x)
  (if (atom x)
      (equal x nil)
    (and (tree-p (car x))
         (tree-p (cdr x)))))

(defun tree-size (tree)
  (if (atom tree)
      0
    (+ 1
       (tree-size (car tree))
       (tree-size (cdr tree)))))

(defun tree-height (tree)
  (if (atom tree)
      0
    (+ 1 (max (tree-height (car tree))
              (tree-height (cdr tree))))))

(defun mirror (tree)
  (if (atom tree)
      nil
    (cons (mirror (cdr tree))
          (mirror (car tree)))))

(defthm mirror-involutive
  (implies (tree-p tree)
           (equal (mirror (mirror tree)) tree))
  :hints (("Goal" :induct (mirror tree))))

(defthm mirror-preserves-size
  (equal (tree-size (mirror tree))
         (tree-size tree))
  :hints (("Goal" :induct (mirror tree))))
