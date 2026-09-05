module net_class_scope;
  class Frame;
    typedef logic [7:0] beat_t;
  endclass

  // §8.23 puts no condition on where the class itself stands, and a net takes
  // its declared type by a path of its own: decl_class_scope.sv declares a
  // variable through the same prefix, and this file is the net beside it. The
  // typedef is 4-state because §6.7.1 requires that of a net's data type.
  wire Frame::beat_t w;

  initial begin
    // A prefix that resolved to nothing would size the net at zero bits.
    $display("%0d", $bits(w));
  end
endmodule
