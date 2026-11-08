module decl_class_scope;
  class Frame;
    typedef byte payload_t;
  endclass

  Frame::payload_t v;

  initial begin
    $display("%0d", $bits(v));
    v = -1;
    $display("%0d", v);
  end
endmodule
