module timing_check_violation_location(output logic d, output logic clk);

  specify
$setup(d, posedge clk, 10);
  endspecify

  initial begin
    d = 1'b0;
    clk = 1'b0;
    #5 d = 1'b1;
    #5 clk = 1'b1;
  end
endmodule
