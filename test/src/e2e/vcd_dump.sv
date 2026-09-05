// §21.7: a VCD file holds value changes "stored by VCD system tasks", so what
// this design is right or wrong by is the file it writes rather than the line
// it prints. The e2e tier compared a run's two streams and nothing else until
// the .artifact file beside this one existed, which left §21.7's whole subject
// outside it.
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
