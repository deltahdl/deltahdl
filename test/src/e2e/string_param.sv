module string_param;
  parameter string NAME = "John Smith";
  initial $display("%s", NAME);
endmodule
