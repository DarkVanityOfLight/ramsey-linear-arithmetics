(define-fun R ((invalid Int) (unowned Int) (nonexclusive Int) (exclusive Int) (invalid_p Int) (unowned_p Int) (nonexclusive_p Int) (exclusive_p Int) (state Int)) Bool (and (and (>= invalid 0) (>= unowned 0) (>= nonexclusive 0) (>= exclusive 0) (>= invalid_p 0) (>= unowned_p 0) (>= nonexclusive_p 0) (>= exclusive_p 0) (>= state 0)) (and (= state 0) true)))

(assert
(ramsey
((invalid Int) (unowned Int) (nonexclusive Int) (exclusive Int))
((invalid_p Int) (unowned_p Int) (nonexclusive_p Int) (exclusive_p Int))
(R
invalid unowned nonexclusive exclusive
invalid_p unowned_p nonexclusive_p exclusive_p 
0)
)
)

(check-sat)
