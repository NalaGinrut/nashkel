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
;; This is a graph implementation based on ajecent-list.

(define-module (nashkel graph)
  #:use-module (nashkel utils)
  #:use-module (nashkel aj-list)
  #:use-module (srfi srfi-26)
  #:use-module (srfi srfi-1)
  #:use-module ((rnrs) #:select (define-record-type))
  #:export ())

;; the inner interface
(define %new-graph new-aj-list)
(define %graph? aj-list?)
(define %graph-count aj-list-count)
(define %graph-add! aj-list-add!)
(define %graph-add-rel! aj-list-add-rel!)
(define %graph-change-rel! aj-list-change-rel!)
(define %graph-remove! aj-list-remove!)
(define %graph-find aj-list-find)
(define %graph-rel-count aj-list-rel-count)
(define %graph-neighbors aj-list-neighbor)
(define %graph-ajacent? aj-list-ajacent?)
(define %graph-ajacent! aj-list-ajacent!)
(define %graph-delete-neighbor! aj-list-neighbor-remove!)
(define %graph-get-node-value aj-list-get-value)
(define %graph-set-node-value! aj-list-set-value!)
(define %directed-graph-edges aj-list-count-directed-edges)

;; the imlementation of graph
(define-record-type graph
  (fields 
   inner ; the actual implementation, now it's ajacent-list
   type ; directed or undirected
   (mutable edges) ; how many edges
   ;; how many vertices
   (mutable vertices)))

(define* (new-graph #:optional (type 'directed-graph))
  (make-graph (%new-graph) type 0 0))

;; update all the info of graph, include edges and vertices
(define (graph-sync! g)
  (let ((ig (graph-inner g)))
    (graph-edges-set! g (%graph-count-edges ig))
    (graph-vertices-set! g (%graph-count-vertices ig))))

(define (graph-vertices g)
  (aj-list-count (graph-inner g)))

(define (graph-edges g)
  (case (graph-type g)
    ((directed-graph) (%directed-graph-edges (graph-inner g)))
    ((undirected-graph) (%undirected-graph-edges (graph-inner g)))
    (else (error graph-edges "wrong type of graph!" (graph-type g)))))

;; tests whether there is an edge from node x to node y.
(define (graph-ajacent g index0 index1)
  (%graph-ajacent? (graph-inner g) index0 index1))

;; lists all nodes y such that there is an edge from x to y.
(define (graph-neighbors g index)
  (%graph-neighbors (graph-inner g) index))

;; adds to G the edge from x to y, if it is not there.
(define (graph-add-neighbor! g index0 index1)
  (%graph-ajacent! (graph-inner g) index0 index1))
  
;; removes the edge from x to y, if it is there.
(define (graph-delete-neighbor! g index0 index1)
  (%graph-delete-neighbor! (graph-inner g) index0 index1))

;; returns the value associated with the node x.
(define (graph-get-node-value g index)
  (%graph-get-node-value (graph-inner g) index))

;; sets the value associated with the node x to a.
(define (graph-set-node-value! g index v)
  (%graph-set-node-value! (graph-inner g) v))

Structures that associate values to the edges usually also provide:
get_edge_value(G, x, y): returns the value associated to the edge (x,y).
set_edge_value(G, x, y, v): sets the value associated to the edge (x,y) to v
