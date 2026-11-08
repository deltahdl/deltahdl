`timescale 1ns/1ns
module top;
  int x;
  initial #3 $display("sv x=%0d at %0t", x, $time);
endmodule
