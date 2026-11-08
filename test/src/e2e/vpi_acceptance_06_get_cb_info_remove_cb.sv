`timescale 1ns/1ns
module top;
  int x;
  initial begin
    #1 x = 5;
    #1 x = 6;
    #1 $probe;
    #1 x = 7;
  end
endmodule
