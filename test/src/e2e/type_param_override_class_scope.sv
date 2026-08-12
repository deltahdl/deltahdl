// The module that instantiates is written last, because a run that names no
// top module elaborates the last module of the source (src/main.cpp:464).
module payload_sink #(parameter type T = int)();
  T data;

  initial begin
    // byte is 8 bits, so an override that never reached this instance prints
    // 32 here, the width of the int default.
    $display("%0d", $bits(data));
    // 200 does not fit a signed byte and truncates to -56. It does fit the int
    // default, which prints 200.
    data = 200;
    $display("%0d", data);
  end
endmodule

module type_param_override_class_scope;
  class Frame;
    typedef byte payload_t;
  endclass

  // §23.10.2 defines the instance parameter value assignment and §6.20.3 gives
  // its type-parameter form. §8.23 names a type parameter assignment among the
  // contexts in which a class scope resolution may prefix a type name, so
  // Frame::payload_t is a legal override value here and binds T to the byte
  // that the payload_t of Frame names.
  payload_sink #(.T(Frame::payload_t)) u0();
endmodule
