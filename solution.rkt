#lang racket
(require data/heap)
(provide sim? wire?
         (contract-out
          [make-sim        (-> sim?)]
          [sim-wait!       (-> sim? positive? void?)]
          [sim-time        (-> sim? real?)]
          [sim-add-action! (-> sim? positive? (-> any/c) void?)]

          [make-wire       (-> sim? wire?)]
          [wire-on-change! (-> wire? (-> any/c) void?)]
          [wire-value      (-> wire? boolean?)]
          [wire-set!       (-> wire? boolean? void?)]

          [bus-value (-> (listof wire?) natural?)]
          [bus-set!  (-> (listof wire?) natural? void?)]

          [gate-not  (-> wire? wire? void?)]
          [gate-and  (-> wire? wire? wire? void?)]
          [gate-nand (-> wire? wire? wire? void?)]
          [gate-or   (-> wire? wire? wire? void?)]
          [gate-nor  (-> wire? wire? wire? void?)]
          [gate-xor  (-> wire? wire? wire? void?)]

          [wire-not  (-> wire? wire?)]
          [wire-and  (-> wire? wire? wire?)]
          [wire-nand (-> wire? wire? wire?)]
          [wire-or   (-> wire? wire? wire?)]
          [wire-nor  (-> wire? wire? wire?)]
          [wire-xor  (-> wire? wire? wire?)]

          [flip-flop (-> wire? wire? wire? void?)]))

;--------------------------------------------------------------------------
; struktura symulacji

(struct sim ([time #:mutable] [queue #:mutable]) #:transparent)

; car pary w heap mowi w jakim czasie wykonac funkcje z cdr pary 
(define (make-sim)
  (sim 0 (make-heap (lambda (x y) (<= (car x) (car y))))))

;--------------------------------------------------------------------------

(define (sim-wair-help s)
  (if (eq? 0 (heap-count (sim-queue s)))
      (void)
      (if (not (>= (sim-time s) (car (heap-min (sim-queue s)))))
          (void)
          (begin
            ((cdr (heap-min (sim-queue s))))
            (heap-remove-min! (sim-queue s))
            (sim-wair-help s)))))

(define (sim-wait! s t)
  (if (<= t 0)
      (void)
      (begin
        (set-sim-time! s (+ t (sim-time s)))
        (sim-wair-help s))))


(define (sim-add-action! s d act)
  (heap-add! (sim-queue s) (cons (+ (sim-time s) d) act)))

;-------------------------------------------------------------------------
; struktura wire (kabla) i jej obsluga

(struct wire (sim [value #:mutable] [actions #:mutable]) #:transparent)

(define (make-wire s)
  (wire s #f null))

(define (wire-on-change! w f)
  (begin
    (f)
    (set-wire-actions! w (cons f (wire-actions w)))))

(define (wire-set! w v)
  (if (eq? v (wire-value w))
      (void)
      (begin
        (set-wire-value! w v)
        (call-actions (wire-actions w)))))

(define (call-actions xs)
  (if (null? xs)
      (void)
      (begin
        ((car xs))
        (call-actions (cdr xs)))))

;--------------------------------------------------------------------------
; funckje reprezentujace bramk logicze 

(define (gate-and c a b) 
  (define delay 1)
  (define curr_t (sim-time (wire-sim a)))
  (define (and-action)
    (wire-set! c (and (wire-value a) (wire-value b))))
  (set-wire-actions! a (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) and-action)) (wire-actions a)))
  (set-wire-actions! b (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) and-action)) (wire-actions b)))
  (and-action))



(define (gate-nand c a b) 
  (define delay 1)
  (define curr_t (sim-time (wire-sim a)))
  (define (nand-action)
    (wire-set! c (not (and (wire-value a) (wire-value b)))))
  (set-wire-actions! a (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) nand-action)) (wire-actions a)))
  (set-wire-actions! b (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) nand-action)) (wire-actions b)))
  (nand-action))


(define (gate-not b a)
  (define delay 1)
  (define curr_t (sim-time (wire-sim a)))
  (define (not-action)
    (wire-set! b (not (wire-value a))))
  (set-wire-actions! a (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) not-action)) (wire-actions a)))
  (not-action))

(define (gate-or c a b) 
  (define delay 1)
  (define curr_t (sim-time (wire-sim a)))
  (define (or-action)
    (wire-set! c (or (wire-value a) (wire-value b))))
  (set-wire-actions! a (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) or-action)) (wire-actions a)))
  (set-wire-actions! b (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) or-action)) (wire-actions b)))
  (or-action))



(define (gate-nor c a b) 
  (define delay 1)
  (define curr_t (sim-time (wire-sim a)))
  (define (nor-action)
    (wire-set! c (not (or (wire-value a) (wire-value b)))))
  (set-wire-actions! a (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) nor-action)) (wire-actions a)))
  (set-wire-actions! b (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) nor-action)) (wire-actions b)))
  (nor-action))

(define (gate-xor c a b) 
  (define delay 2)
  (define curr_t (sim-time (wire-sim a)))
  (define (xor-action)
    (wire-set! c (xor (wire-value a) (wire-value b))))
  (set-wire-actions! a (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) xor-action)) (wire-actions a)))
  (set-wire-actions! b (cons (lambda () (sim-add-action!
                             (wire-sim a)
                             (+ curr_t delay) xor-action)) (wire-actions b)))
  (xor-action))

;--------------------------------------------------------------------------
; funkcje laczace funkcjonalosci gate-ow i wire-ow

(define (wire-not a)
  (let ([output (make-wire (wire-sim a))])
  (gate-not output a)
  output))

(define (wire-and a b)
    (let ([output (make-wire (wire-sim a))])
    (gate-and output a b)
    output))

(define (wire-nand a b)
  (let ([output (make-wire (wire-sim a))])
    (gate-nand output a b)
    output))

(define (wire-or a b)
  (let ([output (make-wire (wire-sim a))])
    (gate-or output a b)
    output))

(define (wire-nor a b)
  (let ([output (make-wire (wire-sim a))])
    (gate-nor output a b)
    output))

(define (wire-xor a b)
  (let ([output (make-wire (wire-sim a))])
    (gate-xor output a b)
    output))


;--------------------------------------------------------------------------


(define (probe name w)
  (wire-on-change! w (lambda ()
                   (display name)
                   (display " = ")
                   (display (wire-value w))
                   (display "\n"))))


;--------------------------------------------------------------------------



(define (bus-set! wires value)
  (match wires
    ['() (void)]
    [(cons w wires)
     (begin
       (wire-set! w (= (modulo value 2) 1))
       (bus-set! wires (quotient value 2)))]))

(define (bus-value ws)
  (foldr (lambda (w value) (+ (if (wire-value w) 1 0) (* 2 value)))
         0
         ws))

(define (flip-flop out clk data)
  (define sim (wire-sim data))
  (define w1  (make-wire sim))
  (define w2  (make-wire sim))
  (define w3  (wire-nand (wire-and w1 clk) w2))
  (gate-nand w1 clk (wire-nand w2 w1))
  (gate-nand w2 w3 data)
  (gate-nand out w1 (wire-nand out w3)))
