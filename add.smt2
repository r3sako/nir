(set-logic ALL)
(set-option :produce-models true)

; Определяем константы
(define-fun p () Int 2013265921) ;  BabyBear
(define-fun two16 () Int 65536) ; 2^16 (для high)
(define-fun two32 () Int 4294967296) ; 2^32 (для переноса в нормализации)
(define-fun max16 () Int 65535) ; 2^16 - 1 (максимальное значение 16 битных)
(define-fun max17 () Int 131072) ; 2^17 (максимум для денормализованных)

; Переменные для первого экземпляра (a1 + b1 = c1)
(declare-fun a1_low () Int)
(declare-fun a1_high () Int)
(declare-fun b1_low () Int)
(declare-fun b1_high () Int)
(declare-fun c1_low () Int)
(declare-fun c1_high () Int)
(declare-fun tmp_low1 () Int) ; денормализованная сумма младших
(declare-fun tmp_high1 () Int) ; денормализованная сумма старших
(declare-fun low16_1 () Int) ; нормализованная сумма младших
(declare-fun high16_1 () Int)
(declare-fun lowCarry1 () Int) ; перенос из младших
(declare-fun highCarry1 () Int)

; Переменные для второго экземпляра
(declare-fun a2_low () Int)
(declare-fun a2_high () Int)
(declare-fun b2_low () Int)
(declare-fun b2_high () Int)
(declare-fun c2_low () Int)
(declare-fun c2_high () Int)
(declare-fun tmp_low2 () Int)
(declare-fun tmp_high2 () Int)
(declare-fun low16_2 () Int)
(declare-fun high16_2 () Int)
(declare-fun lowCarry2 () Int)
(declare-fun highCarry2 () Int)

; Ограничения на диапазоны
(assert (and (>= a1_low 0) (<= a1_low max16)))
(assert (and (>= a1_high 0) (<= a1_high max16)))
(assert (and (>= b1_low 0) (<= b1_low max16)))
(assert (and (>= b1_high 0) (<= b1_high max16)))
(assert (and (>= c1_low 0) (<= c1_low max16)))
(assert (and (>= c1_high 0) (<= c1_high max16)))
(assert (and (>= tmp_low1 0) (<= tmp_low1 max17))) ; tmp_low1 до 2^17 (денормализованная сумма)
(assert (and (>= tmp_high1 0) (<= tmp_high1 max17)))
(assert (and (>= low16_1 0) (<= low16_1 max16))) 
(assert (and (>= high16_1 0) (<= high16_1 max16)))
(assert (or (= lowCarry1 0) (= lowCarry1 1)))
(assert (or (= highCarry1 0) (= highCarry1 1)))

(assert (and (>= a2_low 0) (<= a2_low max16)))
(assert (and (>= a2_high 0) (<= a2_high max16)))
(assert (and (>= b2_low 0) (<= b2_low max16)))
(assert (and (>= b2_high 0) (<= b2_high max16)))
(assert (and (>= c2_low 0) (<= c2_low max16)))
(assert (and (>= c2_high 0) (<= c2_high max16)))
(assert (and (>= tmp_low2 0) (<= tmp_low2 max17)))
(assert (and (>= tmp_high2 0) (<= tmp_high2 max17)))
(assert (and (>= low16_2 0) (<= low16_2 max16)))
(assert (and (>= high16_2 0) (<= high16_2 max16)))
(assert (or (= lowCarry2 0) (= lowCarry2 1)))
(assert (or (= highCarry2 0) (= highCarry2 1)))

; Одинаковые входные данные
(assert (= a1_low a2_low))
(assert (= a1_high a2_high))
(assert (= b1_low b2_low))
(assert (= b1_high b2_high))

; Ограничения для первого экземпляра (AddU32 + NormalizeU32)
; tmp_low1 = a1_low + b1_low mod p
(assert (= (mod tmp_low1 p) (mod (+ a1_low b1_low) p)))
; tmp_high1 = a1_high + b1_high mod p
(assert (= (mod tmp_high1 p) (mod (+ a1_high b1_high) p)))
; tmp_low1 = low16_1 + lowCarry1 * 2^16 mod p
(assert (= (mod tmp_low1 p) (mod (+ low16_1 (* lowCarry1 two16)) p)))
; tmp_high1 + lowCarry1 = high16_1 + highCarry1 * 2^16 mod p
(assert (= (mod (+ tmp_high1 lowCarry1) p) (mod (+ high16_1 (* highCarry1 two16)) p)))
; c1_low = low16_1
(assert (= c1_low low16_1))
; c1_high = high16_1
(assert (= c1_high high16_1))

; Основное ограничение: a1 + b1 = c1 + highCarry1 * 2^32 mod p
(assert (= (mod (+ (* a1_low 1) (* a1_high two16) (* b1_low 1) (* b1_high two16)) p)
           (mod (+ (* c1_low 1) (* c1_high two16) (* highCarry1 two32)) p)))

; Ограничения для второго
; tmp_low2 = a2_low + b2_low mod p
(assert (= (mod tmp_low2 p) (mod (+ a2_low b2_low) p)))
; tmp_high2 = a2_high + b2_high mod p
(assert (= (mod tmp_high2 p) (mod (+ a2_high b2_high) p)))
; tmp_low2 = low16_2 + lowCarry2 * 2^16 mod p
(assert (= (mod tmp_low2 p) (mod (+ low16_2 (* lowCarry2 two16)) p)))
; tmp_high2 + lowCarry2 = high16_2 + highCarry2 * 2^16 mod p
(assert (= (mod (+ tmp_high2 lowCarry2) p) (mod (+ high16_2 (* highCarry2 two16)) p)))
; c2_low = low16_2
(assert (= c2_low low16_2))
; c2_high = high16_2
(assert (= c2_high high16_2))

(assert (= (mod (+ (* a2_low 1) (* a2_high two16) (* b2_low 1) (* b2_high two16)) p)
           (mod (+ (* c2_low 1) (* c2_high two16) (* highCarry2 two32)) p)))

; Утверждение: результаты отличаются (то есть ищем разный результат при одинаковых входных)
(assert (or (not (= c1_low c2_low)) (not (= c1_high c2_high))))

(check-sat)
(get-model)
