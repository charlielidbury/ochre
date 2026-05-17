;; Example of division by factorial

;; 1/fact
(<=-compile (FUN p *int* (FUN n *int* ((*safe-div* 'p) ((*factorial* (FUN t *int* (*succ* *int*))) 'n)))))
