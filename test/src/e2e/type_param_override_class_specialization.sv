class Buf #(type T = int);
  typedef T elem_t;
endclass

module payload_sink #(parameter type P = longint)();
  P data;

  initial begin
    $display("%0d", $bits(data));
    data = 200;
    $display("%0d", data);
  end
endmodule

module type_param_override_class_specialization;
  payload_sink #(.P(Buf#(byte)::elem_t)) u0();
endmodule
