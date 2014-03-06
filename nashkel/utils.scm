;;  -*-  indent-tabs-mode:nil; coding: utf-8 -*-
;;  Copyright (C) 2014
;;      "Mu Lei" known as "NalaGinrut" <NalaGinrut@gmail.com>
;;  Nashkel is free software: you can redistribute it and/or modify
;;  it under the terms of the GNU General Public License as published by
;;  the Free Software Foundation, either version 3 of the License, or
;;  (at your option) any later version.

;;  Nashkel is distributed in the hope that it will be useful,
;;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;  GNU General Public License for more details.

;;  You should have received a copy of the GNU General Public License
;;  along with this program.  If not, see <http://www.gnu.org/licenses/>.

(define-module (nashkel utils)
  #:use-module (rnrs records syntactic)
  #:use-module (rnrs records procedural)
  #:use-module (rnrs records inspection)
  #:use-module (ice-9 q)
  #:export (list-swap!
            vector-swap!
            make-counter
            nashkel-default-error 
            ->list
            %q-remove-with-key!))

(define-syntax-rule (list-swap! lst i j)
  (let ((x (list-ref lst i)))
    (list-set! lst i (list-ref lst j))
    (list-set! lst j x)))

(define-syntax-rule (vector-swap! vec i j)
  (let ((x (vector-ref vec i)))
    (vector-set! vec i (vector-ref vec j))
    (vector-set! vec j x)))

(define* (make-counter #:key (first 0) (next 1))
  (let ((i first))
    (lambda ()
      (let ((j (next i)))
        (set! i j)
        j))))

(define (%q-remove-with-key! q key)
  (assoc-remove! (car q) key)
  (sync-q! q))

(define (nashkel-default-error proc . args)
  (apply error proc args))

;; record -> list, only for debug
(define (->list n) (and n (if (record? n) (record->list n) n)))

(define* (record->list record #:optional (alist #f))
  (define (record-ref rtd k)
    ((record-accessor rtd k) record))
  (define (gen-val rtd k i)
    (let ((v (record-ref rtd i)))
      (if alist
          (cons k v)
          v)))
  (let* ((rtd (record-rtd record))
         (p (record-type-parent rtd))
         (name (record-type-name rtd))
         (pfields (if p (vector->list (record-type-field-names p)) '()))
         (plen (if p (length pfields) 0))
         (fields (vector->list (record-type-field-names rtd)))
         (len (length fields)))
    (append `(,name 
              ,@(map (lambda (k i) (gen-val p k i)) pfields (iota plen))
              ,@(map (lambda (k i) (gen-val rtd k i)) fields (iota len))))))
