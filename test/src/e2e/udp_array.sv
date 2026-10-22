// IEEE 1800-2023 §29.4: a combinational UDP's output state depends on nothing
// but the input states of the moment. Every combination this design drives has
// a row below, because §29.3.4 gives every input combination the table leaves
// out the default output state x.
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

  // §29.8 lets an array of UDP instances carry a range, so each of these is
  // four instances of udp_and2 rather than one. §29.8 also keeps §28.3.6's
  // terminal connection rules, which connect element p to bit p of a terminal
  // as wide as the array and broadcast a single-bit terminal to every element.
  // So y is the bitwise AND of a and b, and z is a gated by the one bit enable.
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
