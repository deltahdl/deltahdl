`timescale 1ns/1ns
module top;
  int x;
  int arr[4];
  initial begin
    #1 x = 5;
    #1 arr[2] = 8;
    #1 x = 5;
    #1 x = 6;
    #1 arr[1] = 9;
  end
endmodule
