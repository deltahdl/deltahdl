`timescale 1ns/1ns
module top;
  int q;
  initial begin
    #5;
    $display("active at %0t q=%0d", $time, q);
    q <= 1;
    #5;
  end
endmodule
