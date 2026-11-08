`timescale 1ns/1ns
module top;
  int v;
  always @(v) $display("v=%0d at %0t", v, $time);
  initial begin
    #1 $probe;
    #9 $display("end v=%0d at %0t", v, $time);
  end
endmodule
