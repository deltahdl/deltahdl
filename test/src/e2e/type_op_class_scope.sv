module type_op_class_scope;
  class Frame;
    typedef byte payload_t;
  endclass

  // §8.23 lists the type operator among the contexts in which a class scope
  // resolution may prefix a type name, so P binds to the payload_t of Frame
  // rather than to a payload_t of this module.
  localparam type P = type(Frame::payload_t);

  P v;

  initial begin
    // byte is 8 bits and signed, so a P that lost the Frame prefix prints
    // neither 8 nor -1.
    $display("%0d", $bits(v));
    v = -1;
    $display("%0d", v);
  end
endmodule
