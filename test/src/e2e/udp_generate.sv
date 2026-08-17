// IEEE 1800-2023 §29.4: in a combinational UDP "the output state is determined
// solely as a function of the current input states". Every combination this
// design drives has a row below, because §29.3.4 rules that "All combinations
// of input values that are not explicitly specified result in a default output
// state of x".
primitive udp_inv (y, a);
  output y;
  input a;
  table
    // a   y
       0 : 1 ;
       1 : 0 ;
  endtable
endprimitive

module udp_generate;
  logic [2:1] d;
  wire [2:1] y;

  genvar bit_pos;

  // §27.4: "Within the generate block of a loop generate construct, there is
  // an implicit localparam declaration", whose "value within each instance of
  // the generate block is the value of the loop index at the time the instance
  // was elaborated", and which "can be used anywhere within the generate block
  // that a normal parameter with an integer value can be used". A terminal
  // written y[bit_pos] is such a use, so each of the two instances drives its
  // own bit and y is the bitwise inverse of d. Two instances that resolved
  // bit_pos to one value would drive one bit twice and leave the other at x.
  //
  // The genvar runs 1 to 2 rather than 0 to 1 so that its value is never the
  // ordinal of the instance the iteration creates, which are 0 and 1. An
  // instance connected by its ordinal reaches y[0], which is not a bit of this
  // net at all.
  generate
    for (bit_pos = 1; bit_pos < 3; bit_pos = bit_pos + 1) begin : inv_bit
      udp_inv g (y[bit_pos], d[bit_pos]);
    end
  endgenerate

  initial begin
    d = 2'b10;
    #1;
    $display("d=10 y=%b", y);

    d = 2'b01;
    #1;
    $display("d=01 y=%b", y);
  end
endmodule
