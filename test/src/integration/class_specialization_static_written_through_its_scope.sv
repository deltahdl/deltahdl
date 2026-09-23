/*
:subclause: 8.25
:stage: simulation
*/
class S #(type T = int);
  static int n = 0;
endclass

module top;
  initial begin
    S#(byte)::n = 5;
    S#(shortint)::n += 3;
    $display(":assert: (%0d == 5)", S#(byte)::n);
    $display(":assert: (%0d == 3)", S#(shortint)::n);
    $display(":assert: (%0d == 0)", S#(int)::n);
  end
endmodule
