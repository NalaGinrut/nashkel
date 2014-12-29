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

;; ====================================================================

;; NOTE: 
;; I was planning to implement "Left-leaning red–black tree"
;; Ref: Left-leaning Red-Black Trees - Robert Sedgewick
;; Link: http://www.cs.princeton.edu/~rs/talks/LLRB/LLRB.pdf
;; BUT
;; It's *NEVER* LLRB now, because of this discussion:
;; Ref: Left-Leaning Red-Black Trees Considered Harmful
;; Link: http://read.seas.harvard.edu/~kohler/notes/llrb.html

;; NOTE: This RB tree follows the algorithm from <<Introduction to Algorithm>>.

;; ====== Red Black Trees ======
;; 1. Every node has a value.
;; 2. The value of any node is greater than the value of its left child and less than the value of its right child.
;; 3. Every node is colored either red or black.
;; 4. Every red node that is not a leaf has only black children.
;; 5. Every path from the root to a leaf contains the same number of black nodes.
;; 6. The root node is black.

(define-module (nashkel rbtree)
  #:use-module (nashkel utils)
  #:use-module (nashkel meta-tree)
  #:use-module ((rnrs) #:select (define-record-type))
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-26)
  #:export (rb-tree?
            new-rb-tree
            rb-tree-search
            rb-tree-successor
            rb-make-PRED
            rb-tree-remove!
            rb-tree-add!
            rb-tree-minimum rb-tree-floor
            rb-tree-maximum rb-tree-ceiling
            rb-tree-select
            rb-tree->dot))

(define-record-type rb-tree (parent tree-node)
  (fields 
   (mutable key)
   (mutable val)
   (mutable color)))

;; NOTE: Which type could be used for color?
;;       Symbol stored here is a address actually, which means it costs a 32/64
;;       bits(all for SCMs), but it's not easy to handle with logical operations.
;;       Although small integers(1~127) costs only 8bits, it's not efficient to
;;       add one byte in three address size: parent, left, right in Cee language
;;       struct. Of course, the size of these types are depened on VM
;;       implementation, but use boolean is a nice choice.
(define (red? node) (and (non-leaf? node) (eq? (rb-tree-color node) 'red)))
(define (red! node) (rb-tree-color-set! node 'red))
(define (black? node) (or (leaf? node) (eq? (rb-tree-color node) 'black)))
(define (black! node) (rb-tree-color-set! node 'black))
(define (!color node)
  (rb-tree-color-set! node
                      (if (eq? (rb-tree-color node) 'black)
                          'red
                          'black)))

;; root node is black
(define (make-rb-tree-root)
  (make-rb-tree #f '(#f #f) #f #f 'black))

(define (rb-root? rbt)
  (and (rb-tree? rbt) (black? rbt) (root? rbt)))

(define (new-rb-tree)
  (let* ((rbt (make-rb-tree-root))
         (head (make-head-node 'RB-TREE 0 rbt)))
    head))

;; NOTE: new node is red in default that could cut some steps.
(define (new-rb-tree-node key val)
  (make-rb-tree #f '(#f #f) key val 'red))

;; don't copy the color
(define (rb-node-copy! from to)
  (rb-tree-key-set! to (rb-tree-key from))
  (rb-tree-val-set! to (rb-tree-val from)))

;; left rotate for adding larger node then try to be balanced
;;       [5,red]*                                [7,red]*
;;        /    \           left rotate           /     \
;; [1,black]   [7,black]        ==>       [5,black]     [8,black]
;;               /    \                    /     \         /   \
;; *brk*-->[6,black]  [8,black]       [1,black] [6,black] ... ...
;;
;; for the code:
;;        px                      px 
;;        |                       |
;;        x                       y
;;       / \    left rotate      / \
;;      lx  y       ==>         x  ry
;;         / \                 / \
;;        ly ry               lx  ly
;; NOTE: left rotate only cut left child, so it's ly was cut. 
(define (%rotate-left! head x)
  (define y (tree-right x))
  (tree-right-set! x (tree-left y)) ; x.right = y.left
  (when (non-leaf? (tree-left y)) ; if y.left is not leaf
    (tree-parent-set! (tree-left y) x)) ; y.left.p = x
  (tree-parent-set! y (tree-parent x)) ; y.p = x.p
  (if (root? x) ; if x is root
      (tree-root-set! head y) ; T.root = y
      (if (is-left-child? x) ; elseif x == x.p.left
          (tree-left-set! (tree-parent x) y) ; x.p.left = y
          (tree-right-set! (tree-parent x) y))) ; else x.p.right = y
  (tree-left-set! y x) ; y.left = x
  (tree-parent-set! x y)) ; x.p = y

;; right rotate for adding smaller node then try to be balanced
;;            [5,red]*                               [3,red]*
;;            /    \           right rotate          /     \
;;     [3,black]   [7,black]        ==>       [2,black]    [5,black]
;;       /    \                                 / \            /  \
;; [2,black] [4,black] <-- *brk*              ... ...  [4,black]  [7,black]
;; 
;; for the code:
;;        px                      px
;;        |                       |
;;        x                       y
;;       / \   right rotate      / \
;;      y  rx     ==>          ly   x
;;     / \                         / \
;;    ly ry                       lx  lx
;; NOTE: right rotate only cut right child, so ry was cut.
(define (%rotate-right! head x)
  (define y (tree-left x))
  (tree-left-set! x (tree-right y)) ; x.left = y.right
  (when (non-leaf? (tree-right y)) ; if y.right is not leaf
    (tree-parent-set! (tree-right y) x)) ; y.right.p = x
  (tree-parent-set! y (tree-parent x)) ; y.p = x.p
  (if (root? x) ; if x is root
      (tree-root-set! head y) ; T.root = y 
      (if (is-right-child? x) ; elseif x == x.p.right
          (tree-right-set! (tree-parent x) y) ; x.p.right = y 
          (tree-left-set! (tree-parent x) y))) ; else x.p.left = y
  (tree-right-set! y x) ; y.right = x 
  (tree-parent-set! x y)) ; x.p = y

(define (rbt-next< t) (tree-left t))
(define (rbt-next> t) (tree-right t))

;; NOTE: PRED follow the convention "is new key larger/less than current key?"
(define (rbt-make-PRED tree =? >? <? new-key)
  (match tree
    (($ rb-tree _ key _ _)
     (cond
      ((=? new-key key) 0)
      ((>? new-key key) 1) ; new key > current key
      ((<? new-key key) -1) ; new key < current key
      (nashkel-default-error rbt-make-PRED "Fatal0: shouldn't be here!" (->list tree))))
    (else nashkel-default-error rbt-make-PRED "Fatal1: shouldn't be here!" (->list tree))))

(define (rbt-default-PRED tree key)
  (rbt-make-PRED tree = > < key))

(define (rbt-default-return-value tree)
  (when (not (rb-tree? tree))
    (nashkel-default-error rbt-default-return-value "Invalid rb tree node!" (->list tree)))
  (rb-tree-val tree))

(define* (rb-tree-search head key #:key (PRED rbt-default-PRED) 
                         (next< rbt-next<) (next> rbt-next>)
                         (op rbt-default-return-value)
                         (err nashkel-default-error))
  (let ((rbt (head-node-tree head)))
    (meta-tree-BST-find rbt key rb-tree? op next< next> PRED err)))

(define (rb-tree-successor tree)
  (meta-tree-BST-successor tree rb-tree? nashkel-default-error))

;; NOTE: we have to fetch parent each time rather than store it for all.
;;       There're so many side-effects here!
(define (%delete-fixup-rec head x next1 next2 rotate1 rotate2)
  (let ((w (next2 (tree-parent x))))
    (cond
     ((red? w) ; if w.color == RED
      ;;(display "fr 0\n")
      (black! w) ; w.color = BLACK
      (red! (tree-parent w)) ; w.p.color = RED
      (rotate1 head (tree-parent x)) ; ROTATE1(T, x.p)
      (set! w (next2 (tree-parent x)))) ; w = x.p.next2
     ((and (black? (next1 w)) (black? (next2 w)))
      ;; if w.next1.color == BLACK and w.next2.color == BLACK
      ;;(display "fr 1\n")
      (red! w) ; w.color = RED
      (set! x (tree-parent x))) ; x = x.p
     (else
      (when (black? (next2 w)) ; elseif w.next2.color == BLACK
        ;;(display "fr 2\n")    
        (black! (next1 w)) ; w.next1.color = BLACK
        (red! w) ; w.color = RED
        (rotate2 head w) ; ROTATE2(T, w)
        ;;(format #t "x: ~a~%" (->list x))
        (set! w (next2 (tree-parent x)))) ; w = x.p.next2
      ;;(display "fr 4\n")
      ;;(format #t "w: ~a~% x: ~a~%" (->list w) (->list x))
      (rb-tree-color-set! w (rb-tree-color (tree-parent x))) ; w.color = x.p.color
      ;;(display "a\n")
      (black! (tree-parent x)) ; x.p.color = BLACK
      ;;(display "b\n")
      (black! (next2 w)) ; w.next2.color = BLACK
      ;;(display "c\n")
      (rotate1 head (tree-parent x)))))) ; ROTATE1(T, x.p)

(define (%delete-fixup head x)
  (format #t "fix node: ~a:~a~%" x (->list x))
  (let lp((x x))
    (cond
     ;; if x is T.root or x.color == RED then:
     ((or (root? x) (red? x))
      ;;(display "f0\n")
      (black! x)) ; x.color = BLACK, and END LOOP
     (else
      (cond
       ((is-left-child? x)
        ;;(display "f1\n")
        (%delete-fixup-rec head x tree-left tree-right %rotate-left! %rotate-right!))
       (else
        ;;(display "f2\n")
        (%delete-fixup-rec head x tree-right tree-left %rotate-right! %rotate-left!)))
      (lp (tree-root head)))))) ; x = T.root then LOOP

;; replace u with v in the subtree
(define (%transplant! head u v)
  (cond
   ((root? u) ; if u is root
    ;;(display "t0\n")
    (tree-root-set! head v)) ; T.root = v
   ((is-left-child? u) ; else if u == u.p.left
    ;;(display "t1\n")
    ;;(format #t "u: ~a~%" (->list u))
    (tree-left-set! (tree-parent u) v)) ; u.p.left = v
   (else
    ;;(display "t2\n")
    ;;(format #t "u: ~a~%" (->list u))
    (tree-right-set! (tree-parent u) v))) ; u.p.right = v
  ;;(display "t3\n")
  (and (non-leaf? v) (tree-parent-set! v (tree-parent u)))) ; v.p = u.p

;; We use the optimized algorithm here.
;; Borrowed from Higepon(Taro Minowa) <higepon@users.sourceforge.jp>
(define (%remove-node! head z)
  (let* ((y (if (or (leaf? (tree-left z)) (leaf? (tree-right z)))
                z
                (rb-tree-successor z))) ; since z.right is non-leaf, it's actually tree-minimum
         (x (if (non-leaf? (tree-left y)) (tree-left y) (tree-right y))))
    (%transplant! head y x)
    (when (not (eq? y z))
      ;; NOTE: Optimized! we're not going to tweak the deleted node,
      ;;       just overwrite it!
      (rb-node-copy! y z))
    (and (black? y)
         (non-leaf? x)
         (%delete-fixup head x))))

(define* (rb-tree-remove! head key #:key (PRED rbt-default-PRED)
                          (next< rbt-next<) (next> rbt-next>)
                          (err nashkel-default-error))
  (define rbt (head-node-tree head))
  (define (remove! node) (%remove-node! head node))
  (and (meta-tree-BST-find rbt key rb-tree? remove! next< next> PRED err)
       (count-1! head)))

;; NOTE: getter will be tree-left or tree-right
;; NOTE: This is a high-order-function abstracted from RB-INSERT-FIXUP
;;       in <<Introduction of Algorithm>>.
(define (%insert-fixup-rec! head new fetch rotate1! rotate2!)
  (define x (fetch (tree-grand-parent new))) ; x == n.p.p.getter
  (define n new) ; set a tmp var for the later side-effect handling.
  (cond
   ((red? x) ; if x.color == RED then
    (black! (tree-parent n)) ; n.p.color = BLACK
    (black! x) ; x.color = BLACK
    (red! (tree-grand-parent n)) ; n.p.p.color = RED
    (%insert-fixup! head (tree-grand-parent n))) ; LOOP(n.p.p)
   (else
    (when (eq? n (fetch (tree-parent n))) ; else if n == n.p.getter then
      (set! n (tree-parent n)) ; n = n.p
      (rotate1! head (tree-parent n))) ; LEFT-ROTATE(T, n.p)
    (black! (tree-parent n)) ; n.p.color = BLACK
    (red! (tree-grand-parent n)) ; n.p.p.color = RED
    ;; RIGHT-ROTATE(T, n.p.p)
    (rotate2! head (tree-grand-parent n))
    (%insert-fixup! head n)))) ; LOOP(n)

(define (%insert-fixup! head new)
  (cond
   ((and (non-root? new) (red? (tree-parent new)))
    (cond
     ((eq? (tree-parent new) (tree-left (tree-parent (tree-parent new))))
      ;; new node is left grand child of certain node
      (%insert-fixup-rec! head new tree-right %rotate-left! %rotate-right!))
     (else ; new node is right grand child of certain node
      (%insert-fixup-rec! head new tree-left %rotate-right! %rotate-left!))))
   (else #f)) ; what's the proper return value?
  ;; fix root color
  (black! (tree-root head)))

;; NOTE: node is the proper entry which was founded in meta-tree-BST-add!
;; NOTE: according to meta-tree-BST-add!, y can't be leaf in anyway!
(define (%add-node! head y key val PRED)
  ;; NOTE: new node is red in default.
  (define z (new-rb-tree-node key val))
  (tree-parent-set! z y)
  (if (< (PRED y (rb-tree-key z)) 0)
      (tree-left-set! y z)
      (tree-right-set! y z))
  (if (%insert-fixup! head z) '*success* '*failed*))

(define* (rb-tree-add! head key val #:key (PRED rbt-default-PRED)
                       (overwrite? #t) (err nashkel-default-error))
  (define rbt (head-node-tree head))
  ;; FIXME: add to where the finder stop
  (define (adder! t) (%add-node! head t key val PRED))
  (define (overwrite! t) (and overwrite? (rb-tree-val-set! t val)))
  (cond
   ((tree-empty? head) ; empty tree, add to root.
    ;; (black! node) ; root is black in default.
    (rb-tree-val-set! rbt val)
    (rb-tree-key-set! rbt key)
    (count+1! head))
   (else
    (let ((status (meta-tree-BST-add! rbt key rb-tree? adder! PRED overwrite! err)))
      (match status
       ((or '*overwrited* '*occupied* '*failed*) status)
       ('*success* (count+1! head))
       (else (error rb-tree-add! "Something wrong!" status)))))))

(define* (rb-tree-floor head #:key (err nashkel-default-error))
  (let ((rbt (head-node-tree head)))
    (meta-tree-BST-floor rbt rb-tree? err)))
(define rb-tree-minimum rb-tree-floor)

(define* (rb-tree-ceiling head #:key (err nashkel-default-error))
  (let ((rbt (head-node-tree head)))
    (meta-tree-BST-ceiling rbt rb-tree? err)))
(define rb-tree-maximum rb-tree-ceiling)

(define* (rb-tree-select head n #:key (err nashkel-default-error))
  (let ((rbt (head-node-tree head)))
    (meta-tree-BST-select rbt n err)))

(define* (rb-tree->dot rb #:optional (port #f))
  (define (print-node-color node port)
    (if (black? node)
        (format port "    ~a [style = filled, fillcolor = \"#cccccc\"];\n" (rb-tree-key node))
        (format port "    ~a [style = filled, color = \"#336666\", fillcolor = \"#CC9999\"];\n" (rb-tree-key node))))
  (let ((port (or port (current-output-port))))
    (format port "digraph rbtrees {\n")
    (node-fold '()
               (lambda (accum node)
                 (let ((left (tree-left node))
                       (right (tree-right node)))
                   (print-node-color node port)
                   (cond
                    ((leaf? left) #f) ; skip
                    (else
                     (print-node-color left port)
                     (format port "    ~a -> ~a;\n" (rb-tree-key node) (rb-tree-key left))))
                   (cond
                    ((leaf? right) #f) ; skip
                    (else
                     (print-node-color right port)
                     (format port "    ~a -> ~a;\n" (rb-tree-key node) (rb-tree-key right))))))
               (tree-root rb))
     (display "}\n" port)))
