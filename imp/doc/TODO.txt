
1.  Presently type variables are not substituted during evaluation, leading to incorrect type annotations after evaluation.
    Example:
      $> ./BINT testing/Fun.txt testing/Sum.txt
      Brandon's Interpreter> Sum.liftl (Fun.id) (Left 0 : (Nat|Bool))
      
      Real Output:
        Left 0 : forall b. (forall c. ((b|c)))
      
      Correct Output:
        Left 0 : (Nat|Bool)
