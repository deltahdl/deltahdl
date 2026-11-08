module payload_sink #(parameter type T = int)();
  T data;

  initial begin
    $display("%0d", $bits(data));
    data = 200;
    $display("%0d", data);
  end
endmodule

module type_param_override_class_scope;
  class Frame;
    typedef byte payload_t;
  endclass

  payload_sink #(.T(Frame::payload_t)) u0();
endmodule
