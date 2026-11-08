module net_class_scope;
  class Frame;
    typedef logic [7:0] beat_t;
  endclass

  wire Frame::beat_t w;

  initial begin
    $display("%0d", $bits(w));
  end
endmodule
