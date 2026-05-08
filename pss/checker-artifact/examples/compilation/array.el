;; Length-indexed array compilation example
;;
;; Identity function on a length-2 array of T:
;; given a payload type T and an a : *array* 2 T, return a.
(<=-compile (FUN T top (FUN a ((*array* *2*) 'T) 'a)))
