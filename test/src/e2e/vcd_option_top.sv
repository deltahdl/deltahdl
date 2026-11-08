module vcd_option_top;
  logic a = 0;
  initial begin
    #1 a = 1;
    #1 $finish;
  end
endmodule

module vcd_option_other;
  logic b = 1;
endmodule
