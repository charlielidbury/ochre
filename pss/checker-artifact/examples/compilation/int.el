;; Some integer related examples

;; None
(<=-compile *0*)

;; *0* <= top
(<=-compile (*0* *0*))

;; (<=p 'm (FUN t XXX top))
;; (<=p 'm XXX)
(<=-compile ('m 'm))
