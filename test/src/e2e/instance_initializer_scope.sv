// §23.9 stops the upward search for a variable at a module boundary, so the P
// that `int q = P;` reads is the parameter of the instance the declaration sits
// in. The top declares an int P of its own, holding a value neither override
// supplies, so an initializer resolved against the top prints "3 3" and one
// that resolved against nothing prints "0 0"; only the per-instance answer
// prints "7 9".
// The instantiating module is written last, because a run that names no top
// module elaborates the last module of the source (src/main.cpp:464).
module scoped_child #(parameter int P = 0);
  int q = P;
endmodule

module instance_initializer_scope;
  int P = 3;

  scoped_child #(.P(7)) u1();
  scoped_child #(.P(9)) u2();

  initial begin
    $display("%0d %0d", u1.q, u2.q);
  end
endmodule
