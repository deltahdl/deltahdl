`timescale 1ns/1ns
module top;
  logic a = 0;
  wire y;
  assign #(3, 4) y = a;
  always @(y) $display("y=%0d at %0t", y, $time);
  initial begin
    #1 $probe;
    #9 a = 1;
    #10 a = 0;
    #10;
  end
endmodule
