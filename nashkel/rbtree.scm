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

(define-module (nashkel meta-tree)
  #:use-modules (nashkel meta-tree)
  #:use-modules ((rnrs) #:select (define-record-type))
  #:use-modules (ice-9 match)
  #:use-modules (srfi srfi-26)
  #:export (rb-tree?
            new-rb-tree
            rb-tree-search
            rb-tree-successor
            rb-tree-remove!
            rb-tree-add!
            rb-tree-minimum rb-tree-floor
            rb-tree-maximum rb-tree-ceiling
            rb-tree-select))

(define-record-type rb-tree
  (parent tree-node)
  (fields key val color))

;; NOTE: Which type could be used for color?
;;       Symbol stored here is a address actually, which means it costs a 32/64
;;       bits(all for SCMs), but it's not easy to handle with logical operations.
;;       Although small integers(1~127) costs only 8bits, it's not efficient to
;;       add one byte in three address size: parent, left, right in Cee language
;;       struct. Of course, the size of these types are depened on VM
;;       implementation, but use boolean is a nice choice.
(define BLACK #f)
(define RED #t)
(define-syntax-rule (red? c) c)
(define-syntax-rule (red! node)
  (rb-tree-color-set! node RED))
(define-syntax-rule (black? c) (not c))
(define-syntax-rule (black! node)
  (rb-tree-color-set! node BLACK))
(define-syntax-rule (!color color) (not color))

(define (make-rb-tree-root)
  (make-rb-tree #f '(#f #f) #f #f BLACK))

(define-syntax-rule (rb-root? rbt)
  (and (rb-tree? rbt) (eq? (black? rbt)) (not (tree-parent rbt))))

(define (new-rb-tree)
  (let* ((rbt (make-rb-tree-root))
         (head (make-head-node 'RB-TREE 0 rbt)))
    head))

;; NOTE: new node is red in default that could cut some steps.
(define (new-rb-tree-node key val)
  (make-rb-tree #f '(#f #f) key val RED))

(define-syntax-rule (rb-node-copy! from to)
  (rb-tree-key-set! to (rb-tree-key from))
  (rb-tree-val-set! to (rb-tree-val from))
  (rb-tree-color-set! to (rb-tree-color from)))

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
(define-syntax-rule (%rotate-left! head x)
  (tree-right-set! x (tree-left y)) ; x.right = y.left
  (when (non-leaf? (tree-left y)) ; if y.left != T.nil
    (tree-parent-set! (tree-left y) x)) ; y.left.p = x
  (tree-parent-set! y (tree-parent x)) ; y.p = x.p
  (if (root? x) ; if x.p == T.nil
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
(define-syntax-rule (%rotate-right! head x)
  (tree-left-set! x (tree-right y)) ; x.left = y.right
  (when (non-leaf? (tree-right y)) ; if y.right != T.nil
    (tree-parent-set! (tree-right y) x)) ; y.right.p = x
  (tree-parent-set! y (tree-parent x)) ; y.p = x.p
  (if (root? x) ; if x.p == T.nil
      (tree-root-set! head y) ; T.root = y 
      (if (is-right-child? x) ; elseif x == x.p.right
          (tree-right-set! (tree-parent x) y) ; x.p.right = y 
          (tree-left-set! (tree-parent x) y))) ; else x.p.left = y
  (tree-right-set! y x) ; y.right = x 
  (tree-parent-set! x y)) ; x.p = y

(define (rbt-next< tree)
  (match tree
    (($ rb-tree ($ tree-node _ _ (left right)) _ _ _)
     ;;(and (verbose?) (show-something))
     left)
    (else (nashkel-default-error rbt-next< "Fatal: shouldn't be here!" (->list tree)))))

(define (rbt-next> tree)
  (match tree
    (($ rb-tree ($ tree-node _ _ (left right)) _ _ _)
     right)
    (else (nashkel-default-error rbt-next> "Fatal: shouldn't be here!" (->list tree)))))

(define (rbt-make-PRED tree =? >? <? key)
  (match tree
    (($ rb-tree _ key0 _ _)
     (cond
      ((=? key0 key) 0)
      ((>? key0 key) 1)
      ((<? key0 key) -1)
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
(define (%delete-fixup-rec head x next1 next2)
  (let ((w (next2 (tree-parent x))))
    (when (red? w)
      (black! w)
      (red! (tree-parent w))
      (%rotate-left! head (tree-parent x))
      (set! w (next2 (tree-parent x))))
    (cond
     ((and (black? (next1 w)) (black? (next2 w)))
      (red! w)
      (set! x (tree-parent x)))
     ((black? (next2 w))
      (black! (next1 w))
      (red! w)
      (%rotate-right! head w)
      (set! w (next (tree-parent x))))
     (else #f)) ; FIXME: what's the proper return value here?
    (rb-tree-color-set! w (rb-tree-color (tree-parent x)))
    (black! (tree-parent x))
    (black! (next2 w))
    (%rotate-left! head (tree-parent x))))

(define (%delete-fixup head x)
  (let lp((x x))
    (cond
     ((or (eq? x (tree-root head)) (red? x))
      (black! x))
     (else 
      (cond
       ((is-left-child? x)
        (%delete-fixup-rec tree x tree-left tree-right))
       (else 
        (%delete-fixup-rec tree x tree-right tree-left)))
      (lp (tree-root head))))))

;; Pseudo code:
;; REF: http://staff.ustc.edu.cn/~csli/graduate/algorithms/book6/chap14.htm
;;
;; RB-DELETE (T, z)
;; if left[z] = nil[T] or right[z] = nil[T]
;;    then y <- z
;;    else y <- TREE-SUCCESSOR(z)
;; endif
;; if left[y] != nil[T] then      
;;    then x <- left[y]
;;    else x <- right[y]
;; endif
;; p[x] <- p[y]
;; if p[y] = nil[T]
;;    then root[T] <- x
;;    else if y = left[p[y]]
;;    then left[p[y]] <- x
;;    else right[p[y]] <- x
;; if y != z
;;    then key[z] <- key[y]
;;         if y has other fields, copy them, too.
;; end if
;; if color[y] = BLACK
;;    then RB-DELETE-FIXUP (T,x)
;; endif
;; return y         
(define (%remove-node! head z)
  (let* ((y (if (or (not (tree-left z)) (not (tree-right z)))
                z
                (rb-tree-successor z)))
         (x (if (tree-left y) (tree-left y) (tree-right y))))
    (when x
      (tree-parent-set! x (tree-parent y)))
    (cond
     ((root? y) (tree-root-set! head (tree-parent y)))
     ((is-left-child? y)
      (tree-left-set! (tree-parent y) x))
     (else
      (tree-right-set! (tree-parent y) x)))
    (when (not (eq? y z))
      (rb-node-copy! y z))
    (when (and (black? y) (non-leaf? x))
      (%delete-fixup head x))
    y))

(define* (rb-tree-remove! head key #:key (PRED rbt-default-PRED)
                          (next< rbt-next<) (next> rbt-next>)
                          (err nashkel-default-error))
  (define rbt (head-node-tree head))
  (define (remove! node) (%remove-node! head node))
  (meta-tree-BST-find rbt key rb-tree? remove! next< next> PRED err)
  (count-1! head)
  #t)

(define (%insert-fixup-rec! head new fetch rotate1! rotate2!)
  (define x (fetch (tree-grand-parent new)))
  (cond
   ((and x (red? x))
    (black! (tree-parent new))
    (black! x)
    (red! (tree-grand-parent new))
    (%insert-fixup! head (tree-grand-parent new)))
   (else
    (when (eq? new (fetch (tree-parent new)))
      (rotate1! (tree-root head) (tree-parent new)))
    (black! (tree-grand-parent new))
    (red! (tree-parent (tree-grand-parent new)))
    (rotate2! (tree-root head) (tree-parent (tree-grand-parent new)))
    (%insert-fixup! head (tree-parent new)))))

(define (%insert-fixup! head tree new)
  (cond
   ((and (non-root? new) (red? (tree-parent new)p))
    (cond
     ((is-left-left-grand-child? new)
      (%insert-fixup-rec! head new tree-right %rotate-left! %rotate-right!))
     (else 
      (%insert-fixup-rec! head new tree-left %rotate-right! %rotate-left!))))
   (else #f)) ; what's the proper return value?
  ;; fix root color
  (black! (tree-root head)))

;; NOTE: node is the proper entry which was founded in meta-tree-BST-find
(define (%add-node! head node key val PRED)
  (define new (new-rb-tree-node key val))
  ;; NOTE: new node is red in default.
  (match (PRED node key)
    ((? positive?) (tree-left-set! node new))
    ((? negative?) (tree-right-set! node new))
    (else
     ;; overwrite shouldn't be here!
     (nashkel-default-error 
      %add-node! "Fatal: Shouldn't be here!" (->list node) key)))
  (%insert-fixup! head node new)
  #t)

(define* (rb-tree-add! head key val #:key (PRED rbt-default-PRED)
                          (next< rbt-next<) (next> rbt-next>)
                          (err nashkel-default-error))
  (define rbt (head-node-tree head))
  (define (adder! node)
    (cond
     ((rb-root? node) ; empty tree, add to root.
      ; (black! node) ; root is black in default.
      (rb-tree-val-set! node val)
      (rb-tree-key-set! node key))
     ((zero? (PRED entry key))
      ;; key already exists. 
      (and overwrite? (rb-tree-val-set! node val) '*dumplicated-val*))
     (else
      ;; normal insertion.
      (%add-node! head node key val PRED overwrite?))))
  (meta-tree-BST-find! rbt key rb-tree? adder! next< next> PRED err)
  (count+1! head)
  #t)

(define rb-tree-minimum rb-tree-floor)
(define* (rb-tree-floor head #:key (err nashkel-default-error))
  (let ((rbt (head-node-tree head)))
    (meta-tree-BST-floor rbt rb-tree? err)))

(define rb-tree-maximum rb-tree-ceiling)
(define* (rb-tree-ceiling head #:key (err nashkel-default-error))
  (let ((rbt (head-node-tree head)))
    (meta-tree-BST-ceiling rbt rb-tree? err)))

(define* (rb-tree-select head n #:key (err nashkel-default-error))
  (let ((rbt (head-node-tree head)))
    (meta-tree-BST-select rbt n err)))
