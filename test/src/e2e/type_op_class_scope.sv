module type_op_class_scope;
  class Frame;
    typedef byte payload_t;
  endclass

  localparam type P = type(Frame::payload_t);

  P v;

  initial begin
    $display("%0d", $bits(v));
    v = -1;
    $display("%0d", v);
  end
endmodule
