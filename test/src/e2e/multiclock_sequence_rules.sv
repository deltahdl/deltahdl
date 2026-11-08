module multiclock_sequence_rules;
  logic clk0, clk1, clk2, sig0, sig1, s1, s2;

  assert property (@(posedge clk0) sig0 ##1 @(posedge clk1) sig1[*0:1]);
  assert property (@(posedge clk1) s1 ##2 @(posedge clk2) s2);
  assert property (@(posedge clk1) s1 intersect @(posedge clk2) s2);

  assert property (@(posedge clk0) sig0 ##1 @(posedge clk1) sig1);
  assert property (@(posedge clk0) sig0 ##0 @(posedge clk1) sig1);
  assert property (@(posedge clk1) s1 ##2 @(posedge clk1) s2);
endmodule
