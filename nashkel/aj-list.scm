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

;; --------------------------------------------------------------------------
;; This is an Ajacency List implementation, which is usually used for graphs.

(define-module (nashkel aj-list)
  #:use-module (nashkel utils)
  #:use-module (ice-9 vlist)
  #:use-module (srfi srfi-26)
  #:use-module (srfi srfi-1)
  #:use-module ((rnrs) #:select (define-record-type))
  #:export (new-aj-list
            aj-list?
            aj-list-count
            aj-list-add!
            aj-list-add-rel!
            aj-list-change-rel!
            aj-list-remove!
            aj-list-find
            aj-list-rel-count
            aj-list-neighbor
            aj-list-ajacent!
            aj-list-ajacent?
            aj-list-neighbor-remove!
            aj-list-get-value
            aj-list-set-value!
            aj-list-count-directed-edges))

;; What an ajacency-list looks like in an imaginary way:
;; (elem-list)  
;; [0] -> [2, 3] (aj-relations)
;;  || 
;;  \/
;; [1] -> [7]
;;  ||
;;  \/
;; [2] -> [9, 12]
;; ...
(define-record-type aj-list
  (fields
   (mutable count)
   ;; elem-list is vlist: ((1 . e1) (2 . e2) ...)
   (mutable elem-list)))

(define-record-type aj-elem
  (fields
   (mutable index)
   (mutable val)
   (mutable rel-count) ; relation counts used for counting edges
   ;; elem-relations is vlist: ((1 . e1) (2 . e2) ...)
   (mutable relations)))

(define-syntax-rule (new-elem-list) vlist-null)

(define (new-aj-list)
  (make-aj-list (make-counter) (new-elem-list)))

(define-syntax-rule (ajl-ref ajl index)
  (vlist-ref (aj-list-elem-list ajl) index))

(define-syntax-rule (aje-delete-rel! aje index pred)
  (let ((rl (aj-elem-relations aje)))
    (aj-elem-relations-set! aje (vlist-delete index rl pred))))

(define-syntax-rule (make-aj-relations ajl relations)
  (let ((el (aj-list-elem-list ajl)))
    (vlist-map (cut vlist-ref el <>) relations)))

(define (new-aj-elem ajl new index relations)
  (make-aj-elem index new (length relations) (make-aj-relations ajl relations)))

;; (aj-list-add! ajl new 5 '(1 49 8 9 10)) means add a new node connected to node
;; 5th contains the relations nodes indexed by 1 49 8 9 10.
;; NOTE: aj-list-add! only add new nodes, if you need add new relation to a elem,
;;       you have to use aj-list-add-rel!
(define (aj-list-add! ajl new index relations)
  (let ((e (new-aj-elem ajl new index (make-aj-relations ajl relations)))
        (el (aj-list-elem-list ajl))
        (cnt (aj-list-count ajl)))
    (aj-list-count-set! ajl (1+ cnt))
    (aj-list-elem-list-set! ajl (vlist-cons (cons index e) el))))

(define* (aj-list-ajacent! ajl i1 i2 #:key (pred =))
  (aj-list-add-rel! ajl i1 (list i2) #:pred pred))  

;; check if i2 is in i1's relations
(define (aj-list-ajacent? ajl i1 i2 #:key (pred =))
  (let ((rl (aj-elem-relations (ajl-ref i1))))
    (vlist-ref i2 rl)))

;; remove i2 from relations of i1
(define (aj-list-neighbor-remove! ajl i1 i2 #:key (pred =))
  (let ((e1 (ajl-ref ajl i1))
        (e2 (ajl-ref ajl i2)))
    (aje-delete-rel! e1 i1 pred)
    (aje-delete-rel! e2 i2 pred)))

;; add a new relation
(define (%add-to-relation! to i)
  (let* ((e (ajl-ref ajl i))
         (rl (aj-elem-relations to)))
    (aj-elem-relations-set! rl (vlist-cons (cons i e) rl))))

;; only for directed graph
(define (%aj-sync! i rl)
  ;; async all the node relations in rl of node i 
  (vlist-for-each (cut %add-to-relation! <> i) rl))

;; NOTE: aj-list-add-rel! only add new relations, if you need to change its all
;;       relations, you have to use aj-list-change-rel!
(define* (aj-list-add-rel! ajl index new-relations #:key (pred =))
  (let* ((e (ajl-ref ajl index))
         (rl (aj-elem-relations e))
         (new-rel (lset-union pred rl new-relations))
         (rcnt (length new-rel)))
    (vlist-for-each (cut %add-to-relation! e <>) new-relations)
    ;; FIXME: how about undirected graph?
    (%aj-sync! index rl)
    ;; update relations count
    (aj-elem-rel-count-set! e rcnt)))

;; Set! brand new relations to a specified node
(define (aj-list-change-rel! ajl index new-relations)
  (let* ((e (ajl-ref ajl index))
         (el (list->vlist 
              (map (lambda (i) (cons i (ajl-ref ajl i))) new-relations)))
         (rl (aj-elem-relations e)))
    (aj-elem-rel-count-set! e (length new-relations))
    (%aj-sync! index rl)
    (aj-elem-relations-set! e el)))

(define* (aj-list-remove! ajl index #:key (pred =))
  (define-syntax-rule (drop-it i e0)
    (vlist-delete i e0 (lambda (x y) (pred x (aj-elem-index y)))))
  (let ((e (ajl-ref ajl index))
        (el (aj-list-elem-list ajl))
        (cnt (aj-list-count ajl)))
    (aj-list-count-set! ajl (1- cnt))
    (aj-list-elem-list-set! ajl (drop-it index e))))

(define-syntax-rule (aj-list-find ajl index) 
  (ajl-ref ajl index))

;; get the connections count of specified index of node
(define-syntax-rule (aj-list-rel-count ajl index)
  (aj-elem-rel-count (ajl-ref ajl index)))

(define-syntax-rule (aj-list-neighbor ajl index)
  (aj-elem-relations (ajl-ref ajl index)))

(define-syntax-rule (aj-list-get-value ajl index)
  (aj-elem-val ajl (ajl-ref ajl index)))

(define-syntax-rule (aj-list-set-value! ajl index v)
  (aj-elem-val-set! (ajl-ref ajl index) v))

(define-syntax-rule (aj-list-count-directed-edges ajl)
  (let ((el (aj-list-elem-list ajl))
        (cnt 0))
    (vlist-for-each (lambda (e)
                      (vlist-length (aj-elem-relations e)))
                    el)))

