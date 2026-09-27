// A delay control inside an always procedure has no hardware to lower to, so
// the lowering reports it and the run exits 1 with no synthesis summary.
module synth_unsynthesizable(input logic clk, output logic y);
  always @(posedge clk) begin
    #1 y = 1;
  end
endmodule
