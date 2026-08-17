// IEEE 1800-2023 §29.4: in a combinational UDP "the output state is determined
// solely as a function of the current input states". Every combination this
// design drives has a row below, because §29.3.4 rules that "All combinations
// of input values that are not explicitly specified result in a default output
// state of x".
primitive udp_and2 (y, a, b);
  output y;
  input a, b;
  table
    // a b   y
       0 0 : 0 ;
       0 1 : 0 ;
       1 0 : 0 ;
       1 1 : 1 ;
  endtable
endprimitive

module udp_array;
  logic [3:0] a;
  logic [3:0] b;
  logic enable;
  wire [3:0] y;
  wire [3:0] z;

  // §29.8: "An optional range may be specified for an array of UDP instances",
  // so each of these is four instances of udp_and2 rather than one. §29.8 also
  // rules that "The terminal connection rules remain the same as outlined in
  // 28.3.6", which connects element p to bit p of a terminal as wide as the
  // array and broadcasts a single-bit terminal to every element. So y is the
  // bitwise AND of a and b, and z is a gated by the one bit enable.
  udp_and2 ga [3:0] (y, a, b);
  udp_and2 gb [3:0] (z, a, enable);

  initial begin
    a = 4'b1100;
    b = 4'b1010;
    enable = 1;
    #1;
    $display("a=1100 b=1010 y=%b", y);
    $display("a=1100 enable=1 z=%b", z);

    b = 4'b0101;
    enable = 0;
    #1;
    $display("a=1100 b=0101 y=%b", y);
    $display("a=1100 enable=0 z=%b", z);
  end
endmodule
