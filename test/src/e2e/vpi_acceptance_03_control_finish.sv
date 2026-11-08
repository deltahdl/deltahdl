`timescale 1ns/1ns
module top;
  initial begin
    $display("before");
    #5 $probe;
    #5 $display("after must not print");
  end
endmodule
