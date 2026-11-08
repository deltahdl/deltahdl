`timescale 1ns/1ps
module sub; timeunit 1ps; timeprecision 1ps; endmodule
module top;
  sub s();
  initial #7 $probe;
endmodule
