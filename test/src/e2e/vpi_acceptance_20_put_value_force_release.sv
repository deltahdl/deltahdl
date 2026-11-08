`timescale 1ns/1ns
module top;
  logic d = 1;
  wire w = d;
  always @(w) $display("w=%0d at %0t", w, $time);
  initial begin
    #1 $probe;
    #1 $display("sv sees %0d at %0t", w, $time);
    #1 $probe;
    #1;
  end
endmodule
