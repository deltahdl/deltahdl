package pkg;
  parameter int VAL = 77;
endpackage

module child;
  import pkg::VAL;

  initial $display("VAL=%0d", VAL);
endmodule

module top;
  child u1();
endmodule
