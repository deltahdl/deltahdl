module vcd_dump;
  logic clk;

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, vcd_dump);
    clk = 1'b0;
    #1 clk = 1'b1;
    #1 $display("done");
  end
endmodule
