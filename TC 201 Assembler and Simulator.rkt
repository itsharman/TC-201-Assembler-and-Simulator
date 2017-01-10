#lang racket

;**********************************************************
; Name: Harmanpreet Singh
; Email address: harmanpreet.singh@yale.edu
; Topics: TC-201 assembler and simulator,
; assembly language programs for remainder and reverse.
;**********************************************************

(provide hours
         entry entry? entry-key entry-value
         ram-read ram-write diff-rams
         extract bits->int int->bits int->bits-width
         conf conf? conf-cpu conf-ram
         diff-configs incr-pc do-load do-store
         do-add do-sub
         do-input do-output
         do-jump do-skipzero do-skippos do-skiperr
         do-loadi do-storei
         next-config
         init-config symbol-table assemble
         simulate remainder-prog
         reverse-prog)

(define hours 15)

;************************************************************

; A table is a list of entries, where each entry has two fields: key and value.
; The constructor for entries is entry, the type predicate is entry?, and the
; two selectors are entry-key and entry-value.

(struct entry (key value) #:transparent)

; Random access memory (RAM)

; We represent the contents of a memory register as
; a list of 16 bits, each either 0 or 1.
; The contents of the RAM is represented as a list giving
; the contents of memory register 0, memory register 1,
; and so on, up to some address n, where n is at most 4095.
; Those memory registers whose contents are not explicitly
; listed are assumed to contain 16 zeroes.

; Examples of RAMs.

(define ram-ex1
  '((0 0 0 1  0 0 0 0  0 0 0 0  0 0 1 1) ;16 bits, memory register 1
    (0 0 1 0  0 0 0 0  0 0 0 0  0 1 0 0) ;memory register 2, etc...
    (0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0)
    (0 0 0 0  0 0 0 0  0 0 0 0  1 0 1 0)
    (0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0)))
 
(define ram-ex2
  '((0 0 0 1  0 0 0 0  0 0 0 0  0 0 1 1)
    (0 0 1 0  0 0 0 0  0 0 0 0  0 1 0 1)
    (0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0)
    (0 0 0 0  0 0 0 0  0 0 1 0  0 1 0 0)))

; (ram-read address ram)
; takes a memory address and a ram
; and returns a list of 16 bits giving the contents
; of the memory register in ram with the given address.

(define (ram-read-aux ram address)
  (if (< address (length ram))
      (list-ref ram address)
      '(0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0)))

(define (ram-read address ram)
  (ram-read-aux ram address))

; (ram-write address contents ram)
; takes a memory address (address), a list of 16 bits (contents) and a ram,
; and returns a ram representing the result of copying the contents 
; into the memory register of ram specified by the memory address.

(define (ram-write address contents ram)
  ; appends list of 16 0 bits to a given ram
  (define (myappend ram n)
    (if (= n 0)
        (append ram (list contents))
        (myappend (append ram '((0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0))) (- n 1))))
  
  ; goes through given ram & replaces the entry at index address
  (define (ram-write-aux input output)
    (cond
      [(empty? input) (myappend output (- address (length output)))]
      [(equal? (length output) address) (append output (list contents) (cdr input))]
      [else (ram-write-aux (cdr input) (append output (list (car input))))]))

  (ram-write-aux ram '()))

; (diff-rams ram1 ram2)
; takes two RAMs and returns a list indicating the memory registers 
; which have different contents in the two RAMs.
; The format of the list is a list of triples giving
; a memory address, the contents of that memory register
; in ram1, and the contents of that memory register
; in ram2.  The addresses should be in increasing order.

(define (diff-rams-aux ram1 ram2 counter)
  (cond
    [(and (> counter (length ram1)) (> counter (length ram2))) '()]
    [(equal? (ram-read counter ram1) (ram-read counter ram2)) (diff-rams-aux ram1 ram2 (+ counter 1))]
    [else (append (list (list counter (ram-read counter ram1) (ram-read counter ram2))) (diff-rams-aux ram1 ram2 (+ counter 1)))]))

(define (diff-rams ram1 ram2)
  (diff-rams-aux ram1 ram2 0))

; (extract i j lst) 
; takes nonnegative integers i and j and a list lst
; and returns the list of elements of lst indexed i through j.
; You may assume i and j are at least 0 and less than the
; length of the list, and i is less than or equal to j.
; As in list-ref, list elements are indexed starting with 0.

(define (extract i j lst)
  (if (empty? lst)
      '()
      (if (equal? i (length lst))
          (list (list-ref lst (- i 1)))
          (if (equal? i j)
              (list (list-ref lst i))
              (append (list (list-ref lst i)) (extract i (- j 1) (rest lst)))))))

; (bits->int lst) takes a list of bits lst
; and returns the value of the nonnegative number 
; represented in binary by those digits.

(define (bits->int lst)
  (if (empty? lst)
      0
      (+ (* (car lst) (expt 2 (- (length lst) 1)))
         (bits->int (cdr lst)))))

; (int->bits n) takes a nonnegative integer n
; and returns the list of bits representing n in 
; unsigned binary.
; Note that for 0 the answer is (0) but for
; all other numbers the answer starts with 1.

; if n = 0, return 0, else return log base2 of n
(define (logn n)
  (if (= n 0)
      0
      (/ (log n) (log 2))))

; aux fxn that does most of the heavy lifting for int-bits, but passed in a truncated log based 2 of n as a paramater
(define (make-bin n length)
  (cond
    [(< length 0) '()]
    [(>= (- n (expt 2 length)) 0) (append '(1) (make-bin (- n (expt 2 length)) (- length 1)))]
    [else (append '(0) (make-bin n (- length 1)))]))

(define (int->bits n) 
  (make-bin n (truncate (logn n))))

; (int->bits-width n w) takes a nonnegative integer n
; and returns a list of w bits representing n in 
; unsigned binary.
; If n cannot be correctly represented in binary using
; w bits, the string "field too small" should be returned.

(define (int->bits-width n width)
  (cond
    [(>= width (logn n)) (make-bin n (- width 1))]
    [else "field too small"]))

;************************************************************
; Next I develop a simulator for the TC-201

; For the TC-201 Central Processing Unit (CPU), the contents of the registers 
; are represented by a table with entries giving the contents of the CPU 
; registers ** in this order **.

; the accumulator (acc)
; the program counter (pc)
; the run flag (rf)
; the arithmetic error bit (aeb)

; Each entry is a list containing 
; a symbol (one of 'acc, 'pc, 'rf, 'aeb)
; a list of bits of the correct length,
; namely, 16 bits for the acc, 12 bit for
; the pc, and 1 bit each for rf and aeb.

; Examples

(define cpu-ex1 
  (list
   (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1)) ;16 bit
   (entry 'pc '(0 0 0 0 0 0 0 0 0 1 1 1)) ;12 bit
   (entry 'rf '(1)) ;1 bit
   (entry 'aeb '(0)))) ;1 bit

;help fxn -- should define (lookup symbol table) function that goes through list of entries and matches symbol with value and returns it
(define (lookup symbol table)
  (cond
    [(empty? table) #f]
    [(equal? (entry-key (car table)) symbol) (entry-value (car table))]
    [else (lookup symbol (cdr table))]))

(define cpu-ex2 
  (list
   (entry 'acc '(1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1))
   (entry 'pc '(0 0 0 0 0 0 0 0 0 1 1 1))
   (entry 'rf '(1))
   (entry 'aeb '(1))))

; A configuration of the TC-201 is a struct with two fields:
; (1) the contents of the CPU registers, in the above format,
; (2) the contents of the RAM, in the format of problem 1.

(struct conf (cpu ram) #:transparent)

; Note that the constructor is conf, the type-predicate
; is conf?, and the selectors are conf-cpu, conf-ram.

; Examples

(define config-ex1 (conf cpu-ex1 ram-ex1))
(define config-ex2 (conf cpu-ex2 ram-ex2))

; (diff-configs config1 config2)
; takes two configurations and returns a list showing where they differ, 
; as a list of triples, giving the name (or address) of the
; register, the contents in config1 and the contents in config2.  
; The order should be CPU registers first (in order: acc, pc, rf, aeb) 
; and then memory registers in increasing order of addresses.

; aux fxn that determines the differences in the 2 cpus in the configs
(define (diff-cpus cpu1 cpu2)
  (cond
    [(empty? cpu1) '()]
    [(equal? (car cpu1) (car cpu2)) (diff-cpus (cdr cpu1) (cdr cpu2))]
    [else (append (list (list (entry-key (car cpu1)) (entry-value (car cpu1)) (entry-value (car cpu2))))
                  (diff-cpus (cdr cpu1) (cdr cpu2)))]))

(define (diff-configs config1 config2)
  (append (diff-cpus (conf-cpu config1) (conf-cpu config2))
          (diff-rams (conf-ram config1) (conf-ram config2))))

; (incr-pc n config)
; takes a nonnegative integer n and a TC-201 configuration config
; and returns the TC-201 configuration that is obtained by adding n 
; to the value of pc.  Note that the sum should be taken modulo 4096.  
; (Racket has a modulo procedure.)

(define (incr-pc n config)
  (conf
   (list
    (list-ref (conf-cpu config) 0)
    (entry 'pc (int->bits-width (modulo (+ n (bits->int (entry-value (list-ref (conf-cpu config) 1)))) 4096) 12))
    (list-ref (conf-cpu config) 2)
    (list-ref (conf-cpu config) 3))
    (conf-ram config)))

; (do-load address config)
; takes a memory address and a TC-201 configuration, and returns the TC-201 
; configuration that is obtained by copying the contents
; of the given memory address into the accumulator.
; The values of all other registers (including the pc) are unchanged.

(define (do-load address config)
  (conf
   (list
    (entry 'acc (ram-read address (conf-ram config)))
    (list-ref (conf-cpu config) 1)
    (list-ref (conf-cpu config) 2)
    (list-ref (conf-cpu config) 3))
    (conf-ram config)))

; (do-store address config)
; takes a memory address and a TC-201 configuration, and returns the TC-201 
; configuration that is obtained by copying the contents of the accumulator 
; into the given memory address.
; The values of other all registers (including the pc) are unchanged.

(define (do-store address config)
  (conf
   (list
    (list-ref (conf-cpu config) 0)
    (list-ref (conf-cpu config) 1)
    (list-ref (conf-cpu config) 2)
    (list-ref (conf-cpu config) 3))
    (ram-write address (entry-value (list-ref (conf-cpu config) 0)) (conf-ram config))))
	   
; (do-add address config)
; takes a memory address and a TC-201 configuration
; and returns a TC-201 configuration in which
; the contents of the memory register addressed has
; been added to the contents of the accumulator.

; converts 16 bits to a sin-integer
(define (bits->sin-int lst)
  (*
   (if (equal? 0 (car lst))
       1
       -1)
   (bits->int (extract 1 15 lst))))

; converts a sin-integer to 16-bits
(define (sin-int->bits val)
  (append
   (list
    (if (< val 0)
        1
        0))
   (int->bits-width (abs val) 15)))

(define (do-add address config)
  (if (< (abs (+ (bits->sin-int (ram-read address (conf-ram config))) (bits->sin-int (entry-value (list-ref (conf-cpu config) 0))))) 32768)
      (conf
       (list
        (entry 'acc (sin-int->bits (+ (bits->sin-int (entry-value (list-ref (conf-cpu config) 0))) (bits->sin-int (ram-read address (conf-ram config))))))
        (list-ref (conf-cpu config) 1)
        (list-ref (conf-cpu config) 2)
        (entry 'aeb '(0)))
        (conf-ram config))
      (conf
       (list
        (entry 'acc '(0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0))
        (list-ref (conf-cpu config) 1)
        (list-ref (conf-cpu config) 2)
        (entry 'aeb '(1)))
        (conf-ram config))))

; (do-sub address config) is similar, except that the
; contents of the memory register addressed has
; been subtracted from the contents of the accumulator.

; Note that if the result is zero, the answer should
; be +0, not -0.

; If the result can be correctly represented in 16-bit sign/magnitude
; then the arithmetic error bit (aeb) should also be set to 0.

; If the result cannot be correctly represented in 16-bit sign/magnitude
; then the arithmetic error bit (aeb) should also be set to 1.
; In this case, the result in the accumulator should be 
; 16 zeroes, representing +0.

; The contents of registers other than the accumulator and the
; arithmetic error bit should be unchanged.

(define (do-sub address config)
  (if (< (abs (- (bits->sin-int (entry-value (list-ref (conf-cpu config) 0))) (bits->sin-int (ram-read address (conf-ram config))))) 32768)
      (conf
       (list
        (entry 'acc (sin-int->bits (- (bits->sin-int (entry-value (list-ref (conf-cpu config) 0))) (bits->sin-int (ram-read address (conf-ram config))))))
        (list-ref (conf-cpu config) 1)
        (list-ref (conf-cpu config) 2)
        (entry 'aeb '(0)))
        (conf-ram config))
      (conf
       (list
        (entry 'acc '(0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0))
        (list-ref (conf-cpu config) 1)
        (list-ref (conf-cpu config) 2)
        (entry 'aeb '(1)))
        (conf-ram config))))

; Each takes a TC-201 configuration and performs the appropriate action 
; (reading a number from the user or writing a number out to the user)
; and *returns* the resulting TC-201 configuration.

(define (do-input config)
  (let ((value (begin (display "input = ") (read))))
   (conf
    (list
     (entry 'acc (sin-int->bits (modulo value 32768)))
     (list-ref (conf-cpu config) 1)
     (list-ref (conf-cpu config) 2)
     (list-ref (conf-cpu config) 3))
     (conf-ram config))))

(define (do-output config)
  (display "output = ")
  (display (bits->sin-int (entry-value (car (conf-cpu config)))))
  (newline)
  config)

; (do-jump address config)
; takes a memory address and a TC-201 configuration, and
; returns a TC-201 configuration in which the program counter
; (pc) is set to the given address.  All other registers are
; unaffected.

(define (do-jump address config)
  (conf
   (list
    (list-ref (conf-cpu config) 0)
    (entry 'pc (int->bits-width address 12))
    (list-ref (conf-cpu config) 2)
    (list-ref (conf-cpu config) 3))
    (conf-ram config)))

; (do-skipzero config)
; takes a TC-201 configuration config and returns
; a TC-201 configuration in which the program counter (pc)
; is increased by 2 if the accumulator contains +0 or -0,
; and is increased by 1 otherwise.  All registers other than
; the pc are unaffected.

(define (do-skipzero config)
   (incr-pc
    (if (equal? 0 (bits->sin-int (entry-value (list-ref (conf-cpu config) 0))))
        2
        1)
    config))

; (do-skippos config)
; takes a TC-201 configuration config and returns
; a TC-201 configuration in which the program counter (pc)
; is increased by 2 if the accumulator contains a nonzero
; positive number, and is increased by 1 otherwise.  
; All registers other than the pc are unaffected.

(define (do-skippos config)
   (incr-pc
    (if (> (bits->sin-int (entry-value (list-ref (conf-cpu config) 0))) 0)
        2
        1)
    config))

; (do-skiperr config)
; takes a TC-201 configuration config and returns
; a TC-201 configuration in which the program counter (pc)
; is increased by 2 if the arithmetic error bit contains 1
; and is increased by 1 if the arithmetic error bit contains 0.
; In either case, in the new configuration, the arithmetic
; error bit is set to 0.
; All registers other than the pc and the aeb are unaffected.

(define (do-skiperr config)
  (incr-pc
   (if (member 1 (entry-value (list-ref (conf-cpu config) 3)))
       2
       1)
   (conf
    (list
     (list-ref (conf-cpu config) 0)
     (list-ref (conf-cpu config) 1)
     (list-ref (conf-cpu config) 2)
     (entry 'aeb '(0)))
     (conf-ram config))))
           
; (loadi address config)
; takes a memory address and a TC-201 configuration and returns a TC-201 
; configuration that reflects the result of doing a "load indirect" from the
; given memory address to the accumulator.
; That is, the low-order 12 bits of the contents of the memory register 
; addressed by address are extracted and used as the memory address
; from which the contents are loaded into the accumulator.
; All other registers are unaffected.

(define (do-loadi address config)
  (do-load (bits->int (extract 4 15 (ram-read address (conf-ram config)))) config))

; (storei address config)
; takes a memory address and a TC-201 configuration and returns a TC-201 
; configuration that reflects the result of doing a "store indirect" to the
; given memory address from the accumulator.
; That is, the low-order 12 bits of the contents of the memory register 
; addressed by address are extracted and used as the memory address
; to which the contents of the accumulator are copied.
; All other registers are unaffected.

(define (do-storei address config)  
  (do-store (bits->int (extract 4 15 (ram-read address (conf-ram config)))) config))

; (next-config config)
; takes a TC-201 configuration and returns the next TC-201 configuration,
; after one iteration of the fetch/execute cycle.

; halts the computer by setting the run flag to 0
(define (do-halt config)
  (conf
   (list
    (list-ref (conf-cpu config) 0)
    (list-ref (conf-cpu config) 1)
    (entry 'rf '(0))
    (list-ref (conf-cpu config) 3))
    (conf-ram config)))

; increment the program counter by 1
(define (do-next config)
   (incr-pc 1 config))

(define (next-config config)
  (if (equal? '(1) (entry-value (list-ref (conf-cpu config) 2)))
      (case (bits->int (extract 0 3 (ram-read (bits->int (entry-value (list-ref (conf-cpu config) 1))) (conf-ram config))))
        [(1) (do-next (do-load (bits->int (extract 4 15 (ram-read (bits->int (entry-value (list-ref (conf-cpu config) 1))) (conf-ram config)))) config))]
        [(2) (do-next (do-store (bits->int (extract 4 15 (ram-read (bits->int (entry-value (list-ref (conf-cpu config) 1))) (conf-ram config)))) config))]
        [(3) (do-next (do-add (bits->int (extract 4 15 (ram-read (bits->int (entry-value (list-ref (conf-cpu config) 1))) (conf-ram config)))) config))]
        [(4) (do-next (do-sub (bits->int (extract 4 15 (ram-read (bits->int (entry-value (list-ref (conf-cpu config) 1))) (conf-ram config)))) config))]
        [(5) (do-next (do-input config))]
        [(6) (do-next (do-output config))]
        [(7) (do-jump (bits->int (extract 4 15 (ram-read (bits->int (entry-value (list-ref (conf-cpu config) 1))) (conf-ram config)))) config)]
        [(8) (do-skipzero config)]
        [(9) (do-skippos config)]
        [(10) (do-next (do-skiperr config))]
        [(11) (do-next (do-loadi (bits->int (extract 4 15 (ram-read (bits->int (entry-value (list-ref (conf-cpu config) 1))) (conf-ram config)))) config))]
        [(12) (do-next (do-storei (bits->int (extract 4 15 (ram-read (bits->int (entry-value (list-ref (conf-cpu config) 1))) (conf-ram config)))) config))]
        [else (do-halt config)])
      config))

; The symbolic opcodes are:
; halt, load, store, add, sub, input, output
; jump, skipzero, skippos, skiperr, loadi, storei.

; There is also a data statement.

; An assembly language program is a list of "lines", where
; each line is a list of two or three elements representing
; an instruction or a data statment.  If the line has
; three elements, the first one is a symbolic label that
; should appear in the symbol table for the program.
; The remaining two elements (or the only two elements,
; if the line has just two elements) are either a symbol
; representing an opcode and an address, or the symbol 'data
; and a data value.  The address field of an instruction may
; be a number in the range 0 to 4095 inclusive, or a symbolic
; label, in which case the address is the numeric value of the
; label in the symbol table.  The value field of a data statement
; may be a number in the range -32767 to 32767 inclusive, or
; a symbolic label, in which case the value used is the numeric
; value of the label in the symbol table.

; Assume that numeric addresses and data values will be in the correct ranges.

; Note that even instructions like halt, input, and skipzero, which
; ignore their address fields, must have an address specified.
; (A typical choice is 0 for the address fields of such instructions.)

; Example TC-201 assembly language programs

; a program with only instructions, numeric addresses, and no labels

(define prog1
  '((load 3)
    (store 4)
    (halt 0)))

; a program with only data statements, three labels, and both numeric
; and symbolic data values

(define prog2
  '((x data 1)
    (y data -2)
    (z data y)))

; a version of the program we wrote in lecture to sum up
; a zero-terminated sequence of numbers, output the sum, and halt.

(define prog3
  '((start  load constant-zero)
   (        store sum)
   (next    input 0)
   (        skipzero 0)
   (        jump add-num)
   (        load sum)
   (        output 0)
   (        halt 0)
   (add-num add sum)
   (        store sum)
   (        jump next)
   (sum     data 0)
   (constant-zero data 0)))

; (init-config lst)
; takes a list lst 16 bit patterns, and returns a TC-201 configuration 
; in which those patterns are loaded into RAM starting with address 0, 
; and the CPU registers are initialized so that the accumulator has
; value +0, the program counter has address 0, the run flag has 
; value 1, and the arithmetic error bit has value 0.

(define (init-config lst)
  (conf
   (list
    (entry 'acc '(0 0 0 0  0 0 0 0  0 0 0 0  0 0 0 0))
    (entry 'pc '(0 0 0 0  0 0 0 0  0 0 0 0))
    (entry 'rf '(1))
    (entry 'aeb '(0)))
   lst))

; (symbol-table prog)
; takes a TC-201 assembly language program prog (in the format specified below) 
; and returns a table of entries in which the key is a symbol that is a label 
; in prog and the value is the corresponding memory address for that
; instruction or data value (when the program is loaded into memory starting 
; at address 0). The addresses in the table should be in increasing order.

(define (make-table prog n)
    (cond
      [(empty? prog) '()]
      [(equal? 3 (length (car prog))) (append (list (entry (car (car prog)) n)) (make-table (cdr prog) (+ n 1)))]
      [else (make-table (cdr prog) (+ n 1))]))

(define (symbol-table prog)
  (make-table prog 0))

; (assemble prog)
; translates a TC-201 assembly language program prog 
; into a list of 16-bit patterns to be loaded into the TC-201 memory.

;recursively assemble program's each line with reference to table
  (define (recursively-assemble prog table)
    (cond
      [(empty? prog) '()]
      [(equal? (list-ref (car prog) (- (length (car prog)) 2)) 'data)
       (append (list (sin-int->bits
                      (if (number? (list-ref (car prog) (- (length (car prog)) 1)))
                          (list-ref (car prog) (- (length (car prog)) 1))
                          (lookup (list-ref (car prog) (- (length (car prog)) 1)) table))))
               (recursively-assemble (cdr prog) table))]
      [else (append (list (append (int->bits-width
      (case (list-ref (car prog) (- (length (car prog)) 2))
        [(halt) 0]
        [(load) 1]
        [(store) 2]
        [(add) 3]
        [(sub) 4]
        [(input) 5]
        [(output) 6]
        [(jump) 7]
        [(skipzero) 8]
        [(skippos) 9]
        [(skiperr) 10]
        [(loadi) 11]
        [(storei) 12]) 4)
                                  (int->bits-width
                                   (if (number? (list-ref (car prog) (- (length (car prog)) 1)))
                                       (list-ref (car prog) (- (length (car prog)) 1))
                                       (lookup (list-ref (car prog) (- (length (car prog)) 1)) table))
                                   12)))
                    (recursively-assemble (cdr prog) table))]))

(define (assemble prog)
  (recursively-assemble prog (symbol-table prog)))

; (simulate n config)
; simulates the TC-201 computer from the configuration config until
; either it halts (the run flag is 0) or n iterations of the fetch/execute
; cycle have been performed, whichever is first.
; The result returned should be a list of the successive configurations 
; of the TC-201 starting with the config.

(define (simulate n config)
  (if (or (= n 0) (equal? (list-ref (conf-cpu config) 3) '(0)))
      (list config)
      (append (list config) (simulate (- n 1) (next-config config)))))

; remainder-prog
; reads in two positive integers from the user, prints out the remainder 
; when the first is divided by the second, and then halts.

(define remainder-prog
  '((start  input 0)
   (        store 30)
   (        input 0)
   (        store 31)
   (        load 30)
   (loop    sub 31)
   (        skippos 0)
   (        jump out)
   (        jump loop)
   (out     skipzero 0)
   (        add 31)
   (        output 0)
   (        halt 0)))

; reverse-prog
; reads in a zero-terminated sequence of numbers from
; the user, prints them out in reverse, and halts.
; The terminating 0 is not printed out.

(define reverse-prog
  '((loop     input 0)
    (         skipzero 0)
    (         jump newval)
    (         jump out)
    (newval   storei pointer)
    (         load pointer)
    (         add c1)
    (         store pointer)
    (         jump loop)
    (out      load pointer)
    (         sub c1)
    (         store pointer)
    (         sub term)
    (         skippos 0)
    (         halt 0)
    (         loadi pointer)
    (         output 0)
    (         jump out)
    (c1       data 1)
    (term     data 49)
    (pointer  data 50)))

; ********************************************************
; ********  testing, testing. 1, 2, 3 ....
; ********************************************************

(define *testing-flag* #f)
(define error display)

(define (test name got expected)
  (cond (*testing-flag*
	 (let* ((expected (if (procedure? expected)
			      (and (expected got) 'OK-TEST)
			      expected))
		(prefix (if (equal? got expected)
			    '***OK***
			    '====X====)))
	   (list 'testing name prefix 'got: got 'expected: expected)))))
	
(test 'hours hours (lambda (x) (> x 0)))

(test 'ram-read (ram-read 0 ram-ex1) '(0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1))

(test 'ram-read (ram-read 6 ram-ex2) '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))

(test 'diff-rams (diff-rams ram-ex1 ram-ex2) '((1 (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0) (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 1)) (3 (0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0) (0 0 0 0 0 0 0 0 0 0 1 0 0 1 0 0))))

(test 'diff-rams (diff-rams '() '((0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))) '())

(test 'diff-rams (diff-rams ram-ex1 (ram-write 2 '(0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1) ram-ex1)) '((2 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1))))

(test 'diff-rams (diff-rams ram-ex2 (ram-write 5 '(1 1 0 0 1 1 0 0 1 1 0 0 1 1 0 0) ram-ex2)) '((5 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (1 1 0 0 1 1 0 0 1 1 0 0 1 1 0 0))))

(test 'diff-rams (diff-rams ram-ex1 (ram-write 1 '(0 1 1 1 0 0 0 0 0 0 0 0 0 0 1 1) ram-ex1)) '((1 (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0) (0 1 1 1 0 0 0 0 0 0 0 0 0 0 1 1))))


(test 'extract (extract 1 3 '(a b c d e)) '(b c d))

(test 'extract (extract 4 4 '(a b c d e)) '(e))

(test 'bits->int (bits->int '(0)) 0)

(test 'bits->int (bits->int '(0 0 0 1 1 0)) 6)

(test 'int->bits (int->bits 0) '(0))

(test 'int->bits (int->bits 6) '(1 1 0))

(test 'int->bits (int->bits-width 14 8) '(0 0 0 0 1 1 1 0))

(test 'int->bits (int->bits-width 14 3) "field too small")

(test 'diff-configs (diff-configs config-ex1 config-ex2) '((acc (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1) (1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1))
  (aeb (0) (1))
  (1 (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0) (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 1))
  (3 (0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0) (0 0 0 0 0 0 0 0 0 0 1 0 0 1 0 0))))

(test 'incr-pc (incr-pc 1 config-ex1)
(conf
 (list
  (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1))
  (entry 'pc '(0 0 0 0 0 0 0 0 1 0 0 0))
  (entry 'rf '(1))
  (entry 'aeb '(0)))
 '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
   (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
   (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
   (0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0)
   (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))))

(test 'diff-configs (diff-configs config-ex2 (incr-pc 4090 config-ex2))
'((pc (0 0 0 0 0 0 0 0 0 1 1 1) (0 0 0 0 0 0 0 0 0 0 0 1))))

(test 'load-store (diff-configs config-ex1 (do-load 1 config-ex1))
'((acc (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1) (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0))))

(test 'load-store (diff-configs config-ex2 (do-load 12 config-ex2))
'((acc (1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1) (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))))

(test 'load-store (diff-configs config-ex1 (do-store 5 config-ex1))
'((5 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1))))

(test 'load-store  (diff-configs config-ex2 (do-store 0 config-ex2))
'((0 (0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1) (1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1))))


(test 'add-sub (diff-configs config-ex1 (do-add 3 config-ex1))
'((acc (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1) (0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 1))))

(test 'add-sub (diff-configs config-ex2 (do-add 3 config-ex2))
'((acc (1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1) (0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 1))
  (aeb (1) (0))))

(test 'add-sub (diff-configs config-ex1 (do-sub 3 config-ex1))
'((acc (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1) (0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1))))

(test 'add-sub (diff-configs config-ex2 (do-sub 3 config-ex2))
'((acc (1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1) (1 0 0 0 0 0 0 0 0 0 1 0 0 1 1 1))
  (aeb (1) (0))))

(test 'add-sub  (let ((config (conf cpu-ex1 '((0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1))))) (diff-configs config (do-add 0 config)))
'((acc (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1) (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
  (aeb (0) (1))))


(test 'skip-jump (diff-configs config-ex1 (do-jump 5 config-ex1))
'((pc (0 0 0 0 0 0 0 0 0 1 1 1) (0 0 0 0 0 0 0 0 0 1 0 1))))

(test 'skip-jump (diff-configs config-ex2 (do-skipzero config-ex2))
'((pc (0 0 0 0 0 0 0 0 0 1 1 1) (0 0 0 0 0 0 0 0 1 0 0 0))))

(test 'skip-jump (diff-configs config-ex1 (do-skippos config-ex1))
'((pc (0 0 0 0 0 0 0 0 0 1 1 1) (0 0 0 0 0 0 0 0 1 0 0 1))))

(test 'skip-jump (diff-configs config-ex2 (do-skiperr config-ex2))
'((pc (0 0 0 0 0 0 0 0 0 1 1 1) (0 0 0 0 0 0 0 0 1 0 0 1)) (aeb (1) (0))))


(test 'loadi-storei (diff-configs config-ex3 (do-loadi 1 config-ex3))
'((acc (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1) (0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1))))

(test 'loadi-storei (diff-configs config-ex3 (do-loadi 2 config-ex3))
'((acc (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1) (0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1))))

(test 'loadi-storei (diff-configs config-ex3 (do-storei 1 config-ex3))
'((5 (0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1) (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1))))

(test 'loadi-storei (diff-configs config-ex3 (do-storei 2 config-ex3))
'((4 (0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1) (0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1))))


(test 'next-config (next-config config-ex4)
 (conf
  (list
   (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1))
   (entry 'pc '(0 0 0 0 0 0 0 0 0 0 0 1))
   (entry 'rf '(1))
   (entry 'aeb '(0)))
  '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
    (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
    (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)
    (1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0))))

(test 'next-config (next-config (next-config config-ex4))
 (conf
  (list
   (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1))
   (entry 'pc '(0 0 0 0 0 0 0 0 0 0 1 0))
   (entry 'rf '(1))
   (entry 'aeb '(0)))
  '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
    (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
    (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)
    (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1))))

(test 'next-config (next-config (next-config (next-config config-ex4)))
 (conf
  (list
   (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1))
   (entry 'pc '(0 0 0 0 0 0 0 0 0 0 1 0))
   (entry 'rf '(0))
   (entry 'aeb '(0)))
  '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
    (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
    (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)
    (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1))))



(test 'init-config (init-config ram-ex2)
 (conf
  (list (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) 
        (entry 'pc '(0 0 0 0 0 0 0 0 0 0 0 0)) 
        (entry 'rf '(1)) 
        (entry 'aeb '(0)))
  '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
    (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 1)
    (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (0 0 0 0 0 0 0 0 0 0 1 0 0 1 0 0))))

(test 'symbol-table (symbol-table prog1)
 '())

(test 'symbol-table (symbol-table prog2)
 (list (entry 'x 0) (entry 'y 1) (entry 'z 2)))

(test 'symbol-table (symbol-table prog3)
 (list
  (entry 'start 0)
  (entry 'next 2)
  (entry 'add-num 8)
  (entry 'sum 11)
  (entry 'constant-zero 12)))

(test 'assemble (assemble prog1)
 '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
   (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
   (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))

(test 'assemble (assemble prog2)
 '((0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)
   (1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0)
   (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)))

(test 'assemble (assemble prog3)
 '((0 0 0 1 0 0 0 0 0 0 0 0 1 1 0 0)
   (0 0 1 0 0 0 0 0 0 0 0 0 1 0 1 1)
   (0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0)
   (1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
   (0 1 1 1 0 0 0 0 0 0 0 0 1 0 0 0)
   (0 0 0 1 0 0 0 0 0 0 0 0 1 0 1 1)
   (0 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0)
   (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
   (0 0 1 1 0 0 0 0 0 0 0 0 1 0 1 1)
   (0 0 1 0 0 0 0 0 0 0 0 0 1 0 1 1)
   (0 1 1 1 0 0 0 0 0 0 0 0 0 0 1 0)
   (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
   (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))

(test 'simulate (simulate 5 config-ex4)
 (list
  (conf
   (list
    (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
    (entry 'pc '(0 0 0 0 0 0 0 0 0 0 0 0))
    (entry 'rf '(1))
    (entry 'aeb '(0)))
   '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
     (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
     (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
     (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)
     (1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0)))
  (conf
   (list
    (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1))
    (entry 'pc '(0 0 0 0 0 0 0 0 0 0 0 1))
    (entry 'rf '(1))
    (entry 'aeb '(0)))
   '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
     (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
     (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
     (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)
     (1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0)))
  (conf
   (list
    (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1))
    (entry 'pc '(0 0 0 0 0 0 0 0 0 0 1 0))
    (entry 'rf '(1))
    (entry 'aeb '(0)))
   '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
     (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
     (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
     (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)
     (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)))
  (conf
   (list
    (entry 'acc '(0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1))
    (entry 'pc '(0 0 0 0 0 0 0 0 0 0 1 0))
    (entry 'rf '(0))
    (entry 'aeb '(0)))
   '((0 0 0 1 0 0 0 0 0 0 0 0 0 0 1 1)
     (0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0)
     (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
     (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)
     (0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1)))))