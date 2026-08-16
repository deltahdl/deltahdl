// The module that instantiates is written last, because a run that names no
// top module elaborates the last module of the source (src/main.cpp:464).
class Buf #(type T = int);
  typedef T elem_t;
endclass

module payload_sink #(parameter type P = longint)();
  P data;

  initial begin
    // byte is 8 bits, so an override that dropped the #(byte) and took the
    // class's own default of int prints 32 here, and one that never reached
    // this instance prints 64, the width of the longint default.
    $display("%0d", $bits(data));
    // 200 does not fit a signed byte and truncates to -56. It fits both int
    // and longint, either of which prints 200.
    data = 200;
    $display("%0d", data);
  end
endmodule

module type_param_override_class_specialization;
  // §8.25 says a generic class is not a type and only a concrete specialization
  // represents one, so Buf#(byte) and Buf#(shortint) are different types and
  // the elem_t of the first is a byte. §6.20.3 names a type parameter
  // assignment among the contexts a class scope resolution may prefix a type
  // name in, so this is a legal override value.
  payload_sink #(.P(Buf#(byte)::elem_t)) u0();
endmodule
