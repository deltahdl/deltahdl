module child #(parameter string NAME = "x") ();
  initial $display("%s", NAME);
endmodule

module string_param_override;
  child #(.NAME("John Smith")) u();
endmodule
