; SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
; SPDX-License-Identifier: MIT OR Palimpsest-0.6

;; Insertion sort correctness
;; Demonstrates algorithm verification

(defun insert (x xs)
  (cond ((endp xs) (list x))
        ((<= x (car xs)) (cons x xs))
        (t (cons (car xs) (insert x (cdr xs))))))

(defun insertion-sort (xs)
  (if (endp xs)
      nil
    (insert (car xs) (insertion-sort (cdr xs)))))

(defun ordered (xs)
  (if (or (endp xs) (endp (cdr xs)))
      t
    (and (<= (car xs) (cadr xs))
         (ordered (cdr xs)))))

(defun member-equal (x xs)
  (cond ((endp xs) nil)
        ((equal x (car xs)) t)
        (t (member-equal x (cdr xs)))))

(defthm insert-ordered
  (implies (ordered xs)
           (ordered (insert x xs)))
  :hints (("Goal" :induct (insert x xs))))

(defthm insertion-sort-ordered
  (ordered (insertion-sort xs))
  :hints (("Goal" :induct (insertion-sort xs))
          ("Subgoal *1/2" :use (:instance insert-ordered
                                          (x (car xs))
                                          (xs (insertion-sort (cdr xs)))))))

(defthm member-insert
  (iff (member-equal y (insert x xs))
       (or (equal y x)
           (member-equal y xs)))
  :hints (("Goal" :induct (insert x xs))))
