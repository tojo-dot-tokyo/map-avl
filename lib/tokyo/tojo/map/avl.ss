#!r6rs
(library (tokyo tojo map avl)
  (export map? empty? empty
          insert search
          (rename (avl:remove remove))
          size
          (rename (avl:map map)
                  (avl:map/key map/key)
                  (avl:filter filter)
                  (avl:filter/key filter/key)
                  (avl:partition partition)
                  (avl:partition/key partition/key)
                  (avl:for-each for-each)
                  (avl:for-each/key for-each/key)
                  (avl:fold-left fold-left)
                  (avl:fold-left/key fold-left/key)
                  (avl:fold-right fold-right)
                  (avl:fold-right/key fold-right/key))
          union union/key)
  (import (rnrs))

  (define map?
    (lambda (x)
      (or (empty? x) (node? x))))

  ;; (define empty (list 'avl:empty))
  ;; (define empty? (lambda (x) (eq? x empty)))
  
  ;; (define node (list 'node))
  ;; (define node? (lambda (x)
  ;;                 (and (pair? x)
  ;;                      (eq? (car x) node))))
  ;; (define make-node
  ;;   (lambda (kv l r h)
  ;;     (list node kv l r h)))
  
  ;; (define key&value (lambda (node) (cadr node)))
  ;; (define left (lambda (node) (caddr node)))
  ;; (define right (lambda (node) (cadddr node)))
  ;; (define %height (lambda (node) (cadddr (cdr node))))
  
  (define-record-type (avl:empty make-empty empty?)
    (opaque #t))

  (define empty (make-empty))

  (define-record-type (avl:node make-node node?)
    (fields (immutable kv key&value)
            (immutable l left)
            (immutable r right)
            (immutable h %height))
    (opaque #t))

  (define error-not-map-tree
    (lambda (name x)
      (unless (map? x)
        (assertion-violation name "not map tree" x))))

  (define height
    (lambda (tr)
      (if (empty? tr)
          0
          (%height tr))))

  (define balance-factor
    (lambda (node)
      (- (height (left node))
         (height (right node)))))

  (define height+
    (lambda (l r)
      (+ 1 (max (height l)
                (height r)))))

  ;; (-> (a p (b q c))
  ;;     ((a p b) q c))
  (define rotate-left
    (lambda (p)
      (let ([q (right p)])
        (let ([a (left p)]
              [b (left q)]
              [c (right q)])
          (let ([p (make-node (key&value p)
                              a b
                              (height+ a b))])
            (make-node (key&value q)
                       p c
                       (height+ p c)))))))

  ;; (-> ((a p b) q c)
  ;;     (a p (b q c)))
  (define rotate-right
    (lambda (q)
      (let ([p (left q)])
        (let ([a (left p)]
              [b (right p)]
              [c (right q)])
          (let ([q (make-node (key&value q)
                              b c
                              (height+ b c))])
            (make-node (key&value p)
                       a q
                       (height+ a q)))))))


  ;; (-> ((a p (b q c)) r d)
  ;;     (((a p b) q c) r d)  ; left rotation
  ;;     ((a p b) q (c r d))) ; right rotation
  (define rotate-left-right
    (lambda (r)
      (let* ([p (left r)]
             [q (right p)])
        (let ([a (left p)]
              [b (left q)]
              [c (right q)]
              [d (right r)])
          (let ([p (make-node (key&value p)
                              a b
                              (height+ a b))]
                [r (make-node (key&value r)
                              c d
                              (height+ c d))])
            (make-node (key&value q)
                       p r
                       (height+ p r)))))))

  ;; (-> (a p ((b q c) r d))
  ;;     (a p (b q (c r d)))  ; right rotation
  ;;     ((a p b) q (c r d))) ; left rotation
  (define rotate-right-left
    (lambda (p)
      (let* ([r (right p)]
             [q (left r)])
        (let ([a (left p)]
              [b (left q)]
              [c (right q)]
              [d (right r)])
          (let ([p (make-node (key&value p)
                              a b
                              (height+ a b))]
                [r (make-node (key&value r)
                              c d
                              (height+ c d))])
            (make-node (key&value q)
                       p r
                       (height+ p r)))))))

  (define balance
    (lambda (tr)
      (if (empty? tr)
          empty
          (case (balance-factor tr)
            [(2)
             (case (balance-factor (left tr))
               [(0 1) (rotate-right tr)]
               [(-1) (rotate-left-right tr)]
               [else (assertion-violation 'blanace "error")])]
            [(-2)
             (case (balance-factor (right tr))
               [(0 -1) (rotate-left tr)]
               [(1)  (rotate-right-left tr)]
               [else (assertion-violation 'blanace "error")])]
            [(-1 0 1) tr]
            [else
             (assertion-violation 'balance "error"
                                  (balance-factor tr)
                                  tr)]))))

  (define insert
    (case-lambda
      [(<? =? tr k v)
       (error-not-map-tree 'insert tr)
       (let f ([tr tr])
         (if (not (or (node? tr) (empty? tr)))
             (assertion-violation 'insert "not map tree" tr))
         (if (empty? tr)
             (make-node (cons k v) empty empty 0)
             (let ([kv (key&value tr)])
               (cond
                [(=? k (car kv))
                 (make-node (cons k v)
                            (left tr) (right tr)
                            (height tr))]
                [(<? k (car kv))
                 (let ([l (f (left tr))]
                       [r (right tr)])
                   (balance (make-node (key&value tr)
                                       l r
                                       (height+ l r))))]
                [else
                 (let ([l (left tr)]
                       [r (f (right tr))])
                   (balance (make-node (key&value tr)
                                       l r
                                       (height+ l r))))]))))]
      [(tr k v)
       (insert < = tr k v)]))

  (define search
    (case-lambda
      [(<? =? tr k)
       (error-not-map-tree 'search tr)
       (let f ([tr tr])
         (if (empty? tr)
             #f
             (let ([kv (key&value tr)])
               (cond
                [(=? k (car kv)) (key&value tr)]
                [(<? k (car kv)) (f (left tr))]
                [else (f (right tr))]))))]
      [(tr k) (search < = tr k)]))

  (define node-max
    (lambda (node)
      (if (empty? (right node))
          (values (left node) (key&value node))
          (let-values ([(tr m) (node-max (right node))])
            (values (balance
                     (make-node (key&value node)
                                (left node) tr
                                (height+ (left node) tr)))
                    m)))))

  

  (define avl:remove
    (case-lambda
      [(<? =? tr k)
       (define rem
         (lambda (node)
           (cond
            [(empty? (left node)) (right node)]
            [(empty? (right node)) (left node)]
            [else
             (let-values ([(tr kv) (node-max (left node))])
               (balance
                (make-node kv
                           tr (right node)
                           (height+ tr (right node)))))])))
       (error-not-map-tree 'remove tr)
       (let f ([tr tr])
         (if (empty? tr)
             empty
             (let ([kv (key&value tr)])
               (cond
                [(=? k (car kv)) (rem tr)]
                [(<? k (car kv))
                 (let ([l (f (left tr))]
                       [r (right tr)])
                   (balance
                    (make-node kv
                               l r
                               (height+ l r))))]
                [else
                 (let ([l (left tr)]
                       [r (f (right tr))])
                   (balance
                    (make-node kv
                               l r
                               (height+ l r))))]))))]
      [(tr k)
       (avl:remove < = tr k)]))
  
  (define avl:map
    (lambda (f tr)
      (error-not-map-tree 'map tr)
      (avl:map/key (lambda (k v) (f v)) tr)))
  
  (define avl:map/key
    (lambda (f tr)
      (error-not-map-tree 'map/key tr)
      (let g ([tr tr])
        (if (empty? tr)
            empty
            (let ([kv (key&value tr)])
              (make-node (cons (car kv) (f (car kv)
                                           (cdr kv)))
                         (g (left tr))
                         (g (right tr))
                         (height tr)))))))
  
  (define avl:for-each
    (lambda (f tr)
      (error-not-map-tree 'for-each tr)
      (avl:for-each/key (lambda (k v) (f v)) tr)))
  
  (define avl:for-each/key
    (lambda (f tr)
      (error-not-map-tree 'for-each/key tr)
      (let g ([tr tr])
        (if (empty? tr)
            (if #f #f)
            (let ([kv (key&value tr)])
              (g (left tr))
              (f (car kv) (cdr kv))
              (g (right tr)))))))
  
  (define avl:fold-left
    (lambda (f init tr)
      (error-not-map-tree 'fold-left tr)
      (avl:fold-left/key (lambda (acc k v) (f acc v))
                         init tr)))
  
  (define avl:fold-left/key
    (lambda (f init tr)
      (error-not-map-tree 'fold-left/key tr)
      (let g ([acc init] [tr tr])
        (if (empty? tr)
            acc
            (let ([kv (key&value tr)])
              (g (f (g acc (left tr))
                    (car kv)
                    (cdr kv))
                 (right tr)))))))

  (define avl:fold-right
    (lambda (f init tr)
      (error-not-map-tree 'fold-right tr)
      (avl:fold-right/key (lambda (k v acc) (f v acc))
                          init tr)))
  
  (define avl:fold-right/key
    (lambda (f init tr)
      (error-not-map-tree 'fold-right/key tr)
      (let g ([acc init] [tr tr])
        (if (empty? tr)
            acc
            (let ([kv (key&value tr)])
              (g (f (car kv) (cdr kv)
                    (g acc (right tr)))
                 (left tr)))))))
  
  (define size
    (lambda (tr)
      (error-not-map-tree 'size tr)
      (avl:fold-left (lambda (acc v) (+ acc 1)) 0 tr)))

  (define avl:filter
    (lambda (p? tr)
      (error-not-map-tree 'filter tr)
      (avl:filter/key (lambda (k v) (p? v)) tr)))
  
  (define avl:filter/key
    (lambda (p? tr)
      (error-not-map-tree 'filter/key tr)
      (avl:for-each/key (lambda (k v)
                          (if (not (p? k v))
                              (set! tr (avl:remove tr k))))
                        tr)
      tr))
  
  (define avl:partition
    (lambda (p? tr)
      (error-not-map-tree 'filter tr)
      (avl:partition/key (lambda (k v) (p? v)) tr)))

  (define avl:partition/key
    (lambda (p? tr)
      (error-not-map-tree 'filter tr)
      (let ([t tr]
            [f tr])
        (avl:for-each/key (lambda (k v)
                            (if (p? k v)
                                (set! f (avl:remove f k))
                                (set! t (avl:remove t k))))
                          tr)
        (values t f))))

  (define union
    (case-lambda
      [(f m1 m2)
       (union < = f m1 m2)]
      [(<? =? f m1 m2)
       (union/key <? =? (lambda (k v1 v2) (f v1 v2)) m1 m2)]))

  (define union/key
    (case-lambda
      [(f m1 m2)
       (union < = f m1 m2)]
      [(<? =? f m1 m2)
       (let ([l1 (avl:fold-right/key (lambda (k v acc)
                                       (cons (cons k v) acc))
                                     '() m1)]
             [l2 (avl:fold-right/key (lambda (k v acc)
                                       (cons (cons k v) acc))
                                     '() m2)])
         (let loop ([l1 l1] [l2 l2] [acc empty])
           (cond [(null? l1)
                  (fold-left
                   (lambda (acc p) (insert <? =? acc
                                           (car p) (cdr p)))
                   acc l2)]
                 [(null? l2)
                  (fold-left (lambda (acc p)
                               (insert <? =? acc
                                       (car p) (cdr p)))
                             acc l1)]
                 [(=? (caar l1) (caar l2))
                  (loop (cdr l1) (cdr l2)
                        (insert <? =? acc
                                (caar l1)
                                (f (caar l1) (cdar l1) (cdar l2))))]
                 [(<? (caar l1) (caar l2))
                  (loop (cdr l1) l2
                        (insert <? =? acc
                                (caar l1) (cdar l1)))]
                 [else
                  (loop l1 (cdr l2)
                        (insert <? =? acc
                                (caar l2) (cdar l2)))])))])))
