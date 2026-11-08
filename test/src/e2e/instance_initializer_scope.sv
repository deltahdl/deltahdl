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
