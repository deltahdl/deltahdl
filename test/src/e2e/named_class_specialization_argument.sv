class Buf #(type T1 = int, type T2 = bit);
  typedef T2 elem_t;
endclass

module named_class_specialization_argument;
  Buf#(.T2(byte))::elem_t v;

  initial begin
    $display("%0d", $bits(v));
    v = 200;
    $display("%0d", v);
  end
endmodule
