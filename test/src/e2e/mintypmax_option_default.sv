module mintypmax_option;
  parameter int DELAY = (11:22:33);

  initial begin
    $display("%0d", DELAY);
    #(95:100:105);
    $finish;
  end
endmodule
