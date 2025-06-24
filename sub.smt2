(set-logic ALL)
(set-option :produce-models true)

; Определяем константы
(define-fun p () Int 2013265921) ; Модуль поля BabyBear (p = 15 * 2^27 + 1)
(define-fun two16 () Int 65536) ; 2^16 (для представления high части U32)
(define-fun two32 () Int 4294967296) ; 2^32 (для переноса в нормализации)
(define-fun max16 () Int 65535) ; 2^16 - 1 (максимальное значение для 16-битных слов)
(define-fun max17 () Int 131072) ; 2^17 (максимальное значение для денормализованных слов)

; Переменные для первого экземпляра вычитания (a1 - b1 = c1)
; a1 и b1 - входные 32-битные числа, c1 - результат вычитания
; Каждая переменная типа ValU32 состоит из low и high (16-битные слова)
; Все вычисления в поле Z/pZ, где p = 2013265921
(declare-fun a1_low () Int) ; Младшие 16 бит первого входного числа a1 (a1.low в u32.zir, 0 <= a1_low <= 2^16-1)
(declare-fun a1_high () Int) ; Старшие 16 бит первого входного числа a1 (a1.high в u32.zir, 0 <= a1_high <= 2^16-1)
(declare-fun b1_low () Int) ; Младшие 16 бит второго входного числа b1 (b1.low в u32.zir, 0 <= b1_low <= 2^16-1)
(declare-fun b1_high () Int) ; Старшие 16 бит второго входного числа b1 (b1.high в u32.zir, 0 <= b1_high <= 2^16-1)
(declare-fun c1_low () Int) ; Младшие 16 бит результата вычитания c1 (c1.low в u32.zir, 0 <= c1_low <= 2^16-1)
(declare-fun c1_high () Int) ; Старшие 16 бит результата вычитания c1 (c1.high в u32.zir, 0 <= c1_high <= 2^16-1)
(declare-fun tmp_low1 () Int) ; Денормализованная разность младших 16 бит (2^16 + a1.low - b1.low, до 2^17, из SubU32)
(declare-fun tmp_high1 () Int) ; Денормализованная разность старших 16 бит ((2^16-1) + a1.high - b1.high, до 2^17, из SubU32)
(declare-fun low16_1 () Int) ; Нормализованные младшие 16 бит разности (low16 в NormalizeU32, 0 <= low16_1 <= 2^16-1)
(declare-fun high16_1 () Int) ; Нормализованные старшие 16 бит разности (high16 в NormalizeU32, 0 <= high16_1 <= 2^16-1)
(declare-fun lowCarry1 () Int) ; Перенос из младших 16 бит (lowCarry в NormalizeU32, 0 или 1)
(declare-fun highCarry1 () Int) ; Перенос из старших 16 бит (highCarry в NormalizeU32, 0 или 1)

; Переменные для второго экземпляра (аналогичны первому)
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

; Ограничения на диапазоны для первого экземпляра
(assert (and (>= a1_low 0) (<= a1_low max16))) ; a1_low в [0, 2^16-1]
(assert (and (>= a1_high 0) (<= a1_high max16))) ; a1_high в [0, 2^16-1]
(assert (and (>= b1_low 0) (<= b1_low max16))) ; b1_low в [0, 2^16-1]
(assert (and (>= b1_high 0) (<= b1_high max16))) ; b1_high в [0, 2^16-1]
(assert (and (>= c1_low 0) (<= c1_low max16))) ; c1_low в [0, 2^16-1]
(assert (and (>= c1_high 0) (<= c1_high max16))) ; c1_high в [0, 2^16-1]
(assert (and (>= tmp_low1 0) (<= tmp_low1 max17))) ; tmp_low1 до 2^17 (денормализованная разность)
(assert (and (>= tmp_high1 0) (<= tmp_high1 max17))) ; tmp_high1 до 2^17 (денормализованная разность)
(assert (and (>= low16_1 0) (<= low16_1 max16))) ; low16_1 в [0, 2^16-1]
(assert (and (>= high16_1 0) (<= high16_1 max16))) ; high16_1 в [0, 2^16-1]
(assert (or (= lowCarry1 0) (= lowCarry1 1))) ; lowCarry1 - бит переноса (0 или 1)
(assert (or (= highCarry1 0) (= highCarry1 1))) ; highCarry1 - бит переноса (0 или 1)

; Ограничения на диапазоны для второго экземпляра
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

; Одинаковые входные данные для обоих экземпляров
(assert (= a1_low a2_low)) ; a1 и a2 имеют одинаковые младшие 16 бит
(assert (= a1_high a2_high)) ; a1 и a2 имеют одинаковые старшие 16 бит
(assert (= b1_low b2_low)) ; b1 и b2 имеют одинаковые младшие 16 бит
(assert (= b1_high b2_high)) ; b1 и b2 имеют одинаковые старшие 16 бит

; Ограничения для первого экземпляра (SubU32 + NormalizeU32)
; tmp_low1 = 2^16 + a1_low - b1_low mod p (денормализованная разность младших слов)
(assert (= (mod tmp_low1 p) (mod (+ two16 (- a1_low b1_low)) p)))
; tmp_high1 = (2^16 - 1) + a1_high - b1_high mod p (денормализованная разность старших слов)
(assert (= (mod tmp_high1 p) (mod (+ (- two16 1) (- a1_high b1_high)) p)))
; tmp_low1 = low16_1 + lowCarry1 * 2^16 mod p (нормализация младших слов)
(assert (= (mod tmp_low1 p) (mod (+ low16_1 (* lowCarry1 two16)) p)))
; tmp_high1 + lowCarry1 = high16_1 + highCarry1 * 2^16 mod p (нормализация старших слов с учетом переноса)
(assert (= (mod (+ tmp_high1 lowCarry1) p) (mod (+ high16_1 (* highCarry1 two16)) p)))
; c1_low = low16_1 (младшие 16 бит результата)
(assert (= c1_low low16_1))
; c1_high = high16_1 (старшие 16 бит результата)
(assert (= c1_high high16_1))

; Основное ограничение для первого экземпляра: a1 - b1 = c1 + highCarry1 * 2^32 mod p
(assert (= (mod (- (+ a1_low (* a1_high two16)) (+ b1_low (* b1_high two16))) p)
           (mod (+ c1_low (* c1_high two16) (* highCarry1 two32)) p)))

; Ограничения для второго экземпляра (SubU32 + NormalizeU32)
; tmp_low2 = 2^16 + a2_low - b2_low mod p
(assert (= (mod tmp_low2 p) (mod (+ two16 (- a2_low b2_low)) p)))
; tmp_high2 = (2^16 - 1) + a2_high - b2_high mod p
(assert (= (mod tmp_high2 p) (mod (+ (- two16 1) (- a2_high b2_high)) p)))
; tmp_low2 = low16_2 + lowCarry2 * 2^16 mod p
(assert (= (mod tmp_low2 p) (mod (+ low16_2 (* lowCarry2 two16)) p)))
; tmp_high2 + lowCarry2 = high16_2 + highCarry2 * 2^16 mod p
(assert (= (mod (+ tmp_high2 lowCarry2) p) (mod (+ high16_2 (* highCarry2 two16)) p)))
; c2_low = low16_2
(assert (= c2_low low16_2))
; c2_high = high16_2
(assert (= c2_high high16_2))

; Основное ограничение для второго экземпляра: a2 - b2 = c2 + highCarry2 * 2^32 mod p
(assert (= (mod (- (+ a2_low (* a2_high two16)) (+ b2_low (* b2_high two16))) p)
           (mod (+ c2_low (* c2_high two16) (* highCarry2 two32)) p)))

; Утверждение: результаты вычитания различаются (c1 != c2)
(assert (or (not (= c1_low c2_low)) (not (= c1_high c2_high))))

; Проверяем
(check-sat)
