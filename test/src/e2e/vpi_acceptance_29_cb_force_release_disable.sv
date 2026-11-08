`timescale 1ns/1ns
module top;
  int x;
  logic [3:0] v;
  initial begin
    #1 force x = 5;
    #1 release x;
  end
  initial begin : blk
    #10 $display("blk ran on");
  end
  initial #3 disable blk;
endmodule
