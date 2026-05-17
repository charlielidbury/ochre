;; Terms for booleans - Scott encoding

(define-term
 '*true*
 '(FUN true-case top
       (FUN false-case top
            'true-case)))

(define-term
 '*false*
 '(FUN true-case top
       (FUN false-case top
            'false-case)))

(define-term
 '*bool*
 '(OR *true* *false*))

(define-term
 '*and*
 '(FUN a *bool*
       (FUN b *bool*
            (('a 'b) *false*))))

(define-term
 '*not*
 '(FUN b *bool*
       (('b *false*) *true*
        ('b *true*) *false*)))
