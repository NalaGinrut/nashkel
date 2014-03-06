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
  #:use-modules (nashkel utils)
  #:use-modules (ice-9 vlist)
  #:use-modules (ice-9 match)
  #:use-modules (srfi srfi-26)
  #:use-modules (srfi srfi-1)
  #:use-modules ((rnrs) #:select (define-record-type))
  #:export (new-aj-list
            aj-list?
            aj-list-add!
            aj-list-add-rel!
            aj-list-change-rel!
            aj-list-remove!))

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
   (mutable elem-list)))

(define-record-type aj-elem
  (fields
   (mutable index)
   (mutable val)
   (mutable rel-count) ; relation counts used for counting edges
   (mutable relations)))

(define-syntax-rule (new-elem-list) vlist-null)

(define (new-aj-list)
  (make-aj-list (make-counter) (new-elem-list)))

(define-syntax-rule (ajl-ref ajl index)
  (vlist-ref (aj-list-elem-list ajl) index))

(define-syntax-rule (make-aj-relations ajl relations)
  (let ((el (aj-list-elem-list ajl)))
    (map (cut vlist-ref el <>) relations)))

(define (new-aj-elem ajl new index relations)
  (make-aj-elem index new (length relations) (make-aj-relations ajl relations)))
    
;; (aj-list-add! ajl new 5 '(1 49 8 9 10)) means add a new node connected to node
;; 5th contains the relations nodes indexed by 1 49 8 9 10.
;; NOTE: aj-list-add! only add new nodes, if you need add new relation to a elem,
;;       you have to use aj-list-add-rel!
(define (aj-list-add! ajl new index relations)
  (let ((e (new-aj-elem ajl new index (make-aj-relations relations)))
        (el (aj-list-elem-list ajl)))
    (aj-list-elem-list-set! ajl (vlist-cons (cons index e) el))))

;; NOTE: aj-list-add-rel! only add new relations, if you need to change its all
;;       relations, you have to use aj-list-change-rel!
(define (aj-list-add-rel! ajl index new-relations)
  (define (is-in-relation? l i)
    (any (lambda (e) (and (eq? i (aj-elem-index e)) e))
         l))
  ;; add a new relation
  (define (add-to-relation! adl0 to i)
    (let* ((e (ajl-ref adl0 index))
           (rl (aj-elem-relations to)))
      (set! rl (vlist-cons (cons index e) rl))
      e))
  (let* ((e (ajl-ref ajl index))
         (rl (aj-elem-relations e)))
    (cond
     ((is-in-relation? rl index)
      ;; redundant add, just return the elem
      => identity)
     (else (add-to-relation! ajl e)))))

;; Set! brand new relations to a specified node
(define (aj-list-change-rel! ajl index new-relations)
  (let* ((e (ajl-ref ajl index))
         (el (aj-list-elem-list ajl)))
    (aj-elem-relations-set! e (map (cut vlist-ref el <>) new-relations))))

(define (aj-list-remove! ajl index)
  (define (drop-it i e0)
    (vlist-delete i e0 (cut = <> (aj-elem-index <>))))
  (let ((e (ajl-ref ajl index))
        (el (aj-list-elem-list ajl)))
    (aj-list-elem-list-set! ajl (drop-it index e))))

