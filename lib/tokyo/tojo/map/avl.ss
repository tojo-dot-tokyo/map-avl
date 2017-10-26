#!r6rs
(library (tokyo tojo map avl)
  (export map? empty? empty
          insert search (rename (avl:remove remove))
          size
          (rename (avl:map map)
                  (avl:filter filter)
                  (avl:partition partition)
                  (avl:for-each for-each)
                  (avl:fold-left fold-left)
                  (avl:fold-right fold-right)))
  (import (rnrs))

  (define map?
    (lambda (x)
      (or (empty? x) (node? x))))
  
  (define-record-type (avl:empty make-empty empty?)
    (opaque #t))
  
  (define error-not-avl-tree
    (lambda (name x)
      (unless (map? x)
        (assertion-violation name "not avl tree" x))))

  (define empty (make-empty))

  (define-record-type (avl:node make-node node?)
    (fields (immutable kv key&value)
            (immutable l left)
            (immutable r right)
            (immutable h %height))
    (opaque #t))

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
       (error-not-avl-tree 'insert tr)
       (let f ([tr tr])
         (if (not (or (node? tr) (empty? tr)))
             (assertion-violation 'insert "not avl tree" tr))
         (if (empty? tr)
             (make-node (cons k v) empty empty 0)
             (let ([kv (key&value tr)])
               (cond
                [(=? k (car kv))
                 (make-node (cons k v) (left tr) (right tr) (height tr))]
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
       (error-not-avl-tree 'search tr)
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

  (define avl:remove
    (case-lambda
      [(<? =? tr k)
       (error-not-avl-tree 'remove tr)
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
      (error-not-avl-tree 'map tr)
      (let g ([tr tr])
        (if (empty? tr)
            empty
            (let ([kv (key&value tr)])
              (make-node (cons (car kv) (f kv))
                         (g (left tr))
                         (g (right tr))
                         (height tr)))))))

  (define avl:for-each
    (lambda (f tr)
      (error-not-avl-tree 'for-each tr)
      (let g [(tr tr)]
        (if (empty? tr)
            (if #f #f)
            (begin
              (g (left tr))
              (f (key&value tr))
              (g (right tr)))))))

  (define fold
    (lambda (f init tr)
      (if (empty? tr)
          init
          (f (fold f init (left tr))
             (key&value tr)
             (fold f init (right tr))))))

  (define avl:fold-left
    (lambda (f init tr)
      (error-not-avl-tree 'fold-left tr)
      (let g [[acc init] (tr tr)]
        (if (empty? tr)
            acc
            (g (f (g acc (left tr))
                  (key&value tr))
               (right tr))))))

  (define avl:fold-right
    (lambda (f init tr)
      (error-not-avl-tree 'fold-right tr)
      (let g [[acc init] (tr tr)]
        (if (empty? tr)
            acc
            (g (f (key&value tr)
                  (g acc (right tr)))
               (left tr))))))

  (define size
    (lambda (tr)
      (error-not-avl-tree 'size tr)
      (avl:fold-left (lambda (acc v) (+ acc 1)) 0 tr)))

  (define avl:filter
    (lambda (p? tr)
      (error-not-avl-tree 'filter tr)
      (avl:for-each (lambda (kv)
                      (if (not (p? kv))
                          (set! tr (avl:remove tr (car kv)))))
                    tr)
      tr))
  
  (define avl:partition
    (lambda (p? tr)
      (error-not-avl-tree 'filter tr)
      (let ([t tr]
            [f tr])
        (avl:for-each (lambda (kv)
                        (if (p? kv)
                            (set! f (avl:remove f (car kv)))
                            (set! t (avl:remove t (car kv)))))
                      tr)
        (values t f)))))
