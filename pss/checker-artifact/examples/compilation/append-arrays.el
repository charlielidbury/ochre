;; Length-indexed array append: correct vs deliberately-wrong.
;;
;; This file showcases the headline test that motivated the iota encoding
;; for Och: the type-checker should distinguish between
;;
;;   appendArrays    : ... -> Array (plus n1 n2) T
;;   appendArrays_wrong : ... -> Array (plus n1 n1) T
;;
;; The wrong version replaces the result-length annotation -- the body is
;; the same, so the checker must rely on the dependent index alone to
;; distinguish them.

;; --- Correct (top-level definition) ---
(<=-compile *append-arrays*)

;; --- Wrong (n1 + n1 instead of n1 + n2) ---
(<=-compile *append-arrays-wrong*)

;; --- Use-site: ascribe the function at its declared (correct) type and check ---
;; Body of append-arrays is fully spelled out so its body POs are emitted in
;; an ascribed context.
(<=-compile (FUN T top
              (FUN n1 *int*
                   (FUN n2 *int*
                        (FUN a1 ((*array* 'n1) 'T)
                             (FUN a2 ((*array* 'n2) 'T)
                                  (((((*append-arrays* 'T) 'n1) 'n2) 'a1) 'a2)))))))

;; --- Use-site for the wrong version ---
(<=-compile (FUN T top
              (FUN n1 *int*
                   (FUN n2 *int*
                        (FUN a1 ((*array* 'n1) 'T)
                             (FUN a2 ((*array* 'n2) 'T)
                                  (((((*append-arrays-wrong* 'T) 'n1) 'n2) 'a1) 'a2)))))))
