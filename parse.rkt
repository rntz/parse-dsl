#lang racket

(require (for-syntax syntax/parse))
(require (prefix-in stream/ racket/stream))
(require racket/generator)

;;; ---------- Utility code ----------
;;; mostly for streams

(define ((curry f . args) . more-args)
  (apply f (append args more-args)))

(define (pairwise test l)
  (match l
    [(cons x (and xs (cons y _)))
      (and (test x y) (pairwise test xs))]
    [_ #t]))

(define (set-disjoint a b)
  (set-empty? (set-intersect a b)))

;; right-biased by default
(define (hash-union/2 a b #:combine [combine #f])
  (define combine (or combine (lambda (k x y) y)))
  (for ([(k v) b])
    (set! a
      (hash-set a k
        (if (hash-has-key? a k) (combine k (hash-ref a k) v) v))))
  a)

(define (hash-union* hs #:combine [combine #f])
  (foldr (lambda (a b) (hash-union/2 a b #:combine combine)) (hash) hs))

(define (hash-union #:combine [combine #f] . hs)
  (hash-union* hs #:combine combine))

(define-syntax-rule (for/stream clauses body ... last)
  (sequence->stream (in-generator (for clauses body ... (yield last)))))

(define-syntax-rule (for*/stream clauses body ... last)
  (sequence->stream (in-generator (for* clauses body ... (yield last)))))

(define-match-expander stream-cons
  (syntax-parser
    [(_ first rest)
      #'(and (not (? stream-empty?))
          (app stream-first first)
          (app stream-rest rest))])
  ;; (make-rename-transformer #'stream/stream-cons)
  (syntax-parser
    [_:id #'stream/stream-cons]
    [(_ a ...) #'(stream/stream-cons a ...)])  )

;; ;; lazy stream-append
;; (define (stream-foldr s i f)
;;   (match s
;;     [(? stream-empty?) (i)]
;;     [(stream-cons x xs) (f x (lambda () (stream-foldr xs i f)))]))

;; ;; func : () -> stream
;; ;; func is an "extra-lazy" stream, we don't even know whether it's empty or not
;; (define (stream-append-lazy a func)
;;   (stream-foldr a func (lambda (x xs) (stream-cons x (xs)))))

;; ;; a more lazy stream-append
;; (define-syntax stream-append
;;   (syntax-parser
;;     [(_ x) #'x]
;;     [(_ x xs ...)
;;       #'(stream-append-lazy x (lambda () (stream-append-lazy xs ...)))]))

;;; lazily concatenates a sequence of streams
(define (stream-concat streams)
  ;; (match streams
  ;;   [(? stream-empty?) empty-stream]
  ;;   [(stream-cons a as) (stream-append a (stream-concat as))])
  (for*/stream ([s streams] [x s]) x))

(define (stream-bind k f) (stream-concat (stream-map f k)))

(define/match (stream-take n s)
  [(0 _) empty-stream]
  [(n (stream-cons x xs)) (stream-cons x (stream-take (- n 1) xs))]
  [(_ _) empty-stream])

(define/match (stream-drop n s)
  [(0 s) s]
  [(n (stream-cons _ s)) (stream-drop (- n 1) s)]
  [(_ _) empty-stream])

;; ;;; Bound identifier sets
;; ;;; TODO: come up with a good hash function.
;; ;;; by default this degenerates to O(n^2) perf, I think.
;; (define-custom-set-types bound-identifier-set bound-identifier=?)


;;; ---------- Types ----------
;; For now, we use naive parser combinators:
;;
;;   parser T = stream Token -> stream (T, stream Token)
;;
;; for some implicit type Token of tokens, usually "char".

;; A record-parser additionally indicates which variables it binds:
;;
;;   record-parser = {fields: bound-identifier-set, parser: parser hash}
(struct record-parser (fields parser) #:transparent)

;;; Convenience functions
(define (parse parser str #:eof [eof #f])
  (when eof (set! parser (p/first parser p/eof)))
  (for/list ([result (parser (sequence->stream str))])
    (match-define (list x rest) result)
    (list x (list->string (stream->list rest)))))


;;; ---------- Parser constructors ----------
(define-syntax-rule (p/delay e) (lambda (s) (e s)))

(define ((p/error msg . args) s)
  ;; for now, just a debugging aid, since we're using naive parser-combinators
  ;; (printf "parse error: ~a\n" (apply format msg args))
  empty-stream)

(define p/record record-parser-parser)

;;; Functor
(define ((p/map1 f p) s)
  (stream-map (match-lambda [(list x rest) (list (f x) rest)]) (p s)))

;;; Monad
(define (p/pure x) (lambda (s) (stream (list x s))))

(define (p/join p)
  (define run (match-lambda [(list inner-parser left) (inner-parser left)]))
  (lambda (s) (stream-bind (p s) run)))
(define (p/bind k f) (p/join (p/map1 f k)))
(define-syntax-rule (p/let pattern parser body ...)
  (p/bind parser (match-lambda
                   [pattern body ...]
                   [_ (p/error "pattern match failure")])))

(define (p/list . ps) (p/sequence ps))
(define (p/sequence ps)
  (let loop ([ps ps] [accum '()])
    (match ps
      ['() (p/pure (reverse accum))]
      [(cons p ps) (p/let x p (loop ps (cons x accum)))])))

(define (p/map f . ps)
  (p/map1 (curry apply f) (p/sequence ps)))

;;; p/replace is like <$ in Parsec.
(define (p/replace x p) (p/let _ p (p/pure x)))

(define (p/first p . ps) (p/let x p (p/replace x (p/ignore* ps))))

(define/match (p/ignore* ps)
  [('()) (p/pure (void))]
  [((cons p ps)) (p/let _ p (p/ignore* ps))])

;;; Alternative
(define ((p/sum ps) s) (stream-bind ps (lambda (p) (p s))))
(define (p/alt . ps) (p/sum ps))

(define (p/some p) (p/map cons p (p/many p)))
(define (p/many p)
  (p/alt (p/map cons p (p/delay (p/many p))) (p/pure '())))

(define (p/option default parser) (p/alt parser (p/pure default)))

(define (p/filter test p)
  (p/let x p (if (test x) (p/pure x) (p/error "filter test failed"))))

;;; Miscellaneous combinators
(define ((p/not p) s)
  (if (stream-empty? (p s)) ((p/pure (void)) s) empty-stream))

;; (define ((p/lookahead p) s)
;;   (stream-map (match-lambda [(list x rest) (list x s)]) (p s)))

(define (p/one s)
  (if (stream-empty? s) empty-stream
    (stream (list (stream-first s) (stream-rest s)))))

(define p/eof (p/not p/one))

(define (p/satisfy test) (p/filter test p/one))

(define ((p/string str_) s)
  (define str (sequence->list str_))
  (define n (length str))
  (define pre (stream->list (stream-take n s)))
  (define post (stream-drop n s))
  (if (equal? pre str)
    (stream (list (void) post))
    ((p/error "expected ~a" str_) post)))

(define (p/between pre post p)
  (p/let _ pre (p/let x p (p/replace x post))))

(define p/braces (curry p/between (p/string "{") (p/string "}")))
(define p/parens (curry p/between (p/string "(") (p/string ")")))
(define p/brackets (curry p/between (p/string "[") (p/string "]")))


;;; ---------- Operator precedence parsing ----------
;; type optable Expr = hash int (set (op Expr))
;; maps from precedence levels to sets of operators
(define optable-empty (hash))
(define (optable-join . as)
  (hash-union* as #:combine (lambda (k x y) (set-union x y))))

;; type op Expr
;; op-assoc: 'l, 'r, or #f
;; op-parse: parser (int, Expr -> parser Expr)
;;
;; The value resulting from op-parse is passed the current precedence level and
;; the left-hand-argument expression.
;;
;; Expr is the type of whatever it is we're actually trying to parse, usually
;; expressions of some sort.
(struct op (assoc parse) #:transparent)

;; parser Expr, optable Expr -> int -> parser Expr
(define ((p/ops parse-prefix table) prec)
  (define (parse-rest left-expr)
    (p/option left-expr
      (p/sum
        (for/list ([(op-prec opers) table]
                    #:when (<= prec op-prec)
                    [oper opers])
          (define new-prec
            (match (op-assoc oper)
              ['l (+ 1 op-prec)]
              ['r op-prec]
              [#f (error "nonassociativity unimplemented")]))
          (p/bind (p/let post (op-parse oper) (post new-prec left-expr))
            parse-rest)))))
  (p/let left-expr parse-prefix (parse-rest left-expr)))


;;; ---------- Record parser constructors ----------

;;; We hook into the internals of Racket's match implementation so that we can
;;; ask what the variables a pattern binds are.
(require
  (for-syntax
    (prefix-in match/
      (combine-in
        (only-in racket/match/parse parse)
        (only-in racket/match/patterns bound-vars)))))

;; (r/pat pat parser)
;; produces a record parser which matches `pat' against the result of `parser'
(define-syntax r/pat
  (syntax-parser
    [(_ pat parser)
      (define vars (match/bound-vars (match/parse #'pat)))
      (define/syntax-parse (var:id ...) vars)
      #'(record-parser
          (set 'var ...)
          (p/let pat parser
            (p/pure (make-immutable-hash (list (cons 'var var) ...)))))]))

(define r/empty (record-parser (set) (p/pure (hash))))
;;; TODO: better handling of zero's field list
(define r/zero (record-parser (set) (p/error "r/zero called")))

(define (r/seq2 r1 r2)
  (match-define (record-parser f1 p1) r1)
  (match-define (record-parser f2 p2) r2)
  (unless (set-disjoint f1 f2) (error "r/seq: record fields not disjoint"))
  (record-parser
    (set-union f1 f2)
    (p/map hash-union p1 p2)))

(define (r/sequence ps) (foldr r/seq2 r/empty ps))
(define (r/seq . ps) (r/sequence ps))

(define (r/alt . rs) (r/sum rs))
(define (r/sum rs)
  ;; todo: better handling of empty sum fields
  (define fields (match rs ['() (set)] [(cons (record-parser f _) _) f]))
  (unless (andmap (match-lambda [(record-parser f _) (equal? f fields)]) rs)
    (error "r/sum: record field sets are not equal"))
  (record-parser
    fields
    (p/sum (map record-parser-parser rs))))

(define (r/filter test r)
  (match-define (record-parser rf rp) r)
  (record-parser rf (p/filter test rp)))

(define (r/many r #:by [iterate p/many])
  (match-define (record-parser rf rp) r)
  (define (conc hs) (hash-union* hs #:combine (lambda (k x y) (append x y))))
  (record-parser rf (p/map1 conc (iterate rp))))

(define (r/some r) (r/many r #:by p/some))


;;; ---------- Some convenient builtin parsers ----------
;;; naming convention: parsers begin with ":"

(define :ws  (p/satisfy char-whitespace?))
(define :ws* (p/many (p/satisfy char-whitespace?)))
(define :ws+ (p/some (p/satisfy char-whitespace?)))

(define (p/token p) (p/between :ws* :ws* p))

(define :ident-start (p/satisfy char-alphabetic?))
(define :ident-mid
  (p/satisfy (or/c char-alphabetic? char-numeric? (curry char=? #\_))))
(define :ident
  (p/map (compose string->symbol list->string cons)
    :ident-start (p/many :ident-mid)))

(define :digit (p/satisfy char-numeric?))
(define :number (p/map (compose string->number list->string) (p/some :digit)))


;;; ---------- A simple calculator parser/evaluator ----------
(module+ calc
  (provide (all-defined-out))

  (define :expr (p/delay (:expr-at 0)))
  (define :atom (p/token (p/alt :number (p/parens :expr))))
  (define (:expr-at prec) ((p/ops :atom op-table) prec))

  ;; op-parse: parser (int, Expr -> parser Expr)
  (define (infix-op func assoc parse)
    (define (p-rhs prec lhs)
      (p/map (curry list (object-name func) lhs) (:expr-at prec)))
    (op assoc (p/replace p-rhs parse)))

  (define op-table
    (hash
      6 (set
          (infix-op + 'l (p/string "+"))
          (infix-op - 'l (p/string "-")))
      7 (set
          (infix-op * 'l (p/string "*"))
          (infix-op / 'l (p/string "/"))))))


;;; ---------- Concrete syntax ----------

;;; ===== Patterns =====
;;; TODO: more patterns
(define :underscore (p/replace #'_ (p/string "_")))
(define :pat (p/alt :underscore :ident))

;;; ===== Expressions =====

;;; ===== Record parsers =====
;;; parser (list symbol, code (parser hash))
(define :record
  (p/error "record parsing unimplemented"))

;;; ===== Parsers =====
;; (define :parser
;;   (p/alt
;;     (p/braces :record)
;;     (p/let (list r-vars r-code) :record
;;       (p/let e (p/brackets :expr)
;;         #`(p/map
;;             (lambda (h)
;;               )
;;             (p/record ,r))
;;         ))))
