// The module is written last, because a run that names no top module
// elaborates the last module of the source (src/main.cpp:464).
class Buf #(type T1 = int, type T2 = bit);
  typedef T2 elem_t;
endclass

module named_class_specialization_argument;
  // §8.25 says a parameterized class is instantiated using the same parameter
  // override rules as a module instance (see 23.10), and §23.10.2.2 says an
  // assignment by name explicitly links the parameter name to its new value and
  // leaves every parameter it does not name at its default. The named argument
  // here therefore binds byte to T2 and leaves T1 at int, so elem_t is a byte.
  // §8.25.1 requires the explicit specialization form outside the class, which
  // is what prefixes the scope resolution operator below.
  Buf#(.T2(byte))::elem_t v;

  initial begin
    // byte is 8 bits, so this prints 8. A binding that took the argument
    // positionally would give byte to T1 and leave T2 at its bit default, and
    // one that dropped the argument would leave T2 at bit as well; either
    // prints 1. A binding that named T1 instead prints 32, the width of int.
    $display("%0d", $bits(v));
    // 200 does not fit a signed byte and truncates to -56. A bit elem_t would
    // keep only the low bit of 200 and print 0, and an int elem_t would print
    // 200, so the value tells the three types apart as well as the width does.
    v = 200;
    $display("%0d", v);
  end
endmodule
