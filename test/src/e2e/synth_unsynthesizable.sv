module synth_unsynthesizable(input logic clk, output logic y);
  always @(posedge clk) begin
    #1 y = 1;
  end
endmodule
