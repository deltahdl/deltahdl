module nondegenerate_sequences;
  logic clk, a, b;

  sequence never;
    1'b1 intersect (1'b1 ##1 1'b1);
  endsequence

  assert property (@(posedge clk) 1'b1 intersect (1'b1 ##1 1'b1));
  assert property (@(posedge clk) 1'b1[*0]);
  assert property (@(posedge clk) a[*0:2]);
  assert property (@(posedge clk) 1'b1[*0] |-> b);
  assert property (@(posedge clk) a ##1 never |=> b);

  assert property (@(posedge clk) a[*0:2] |-> b);
  assert property (@(posedge clk) 1'b1[*0] |=> b);
  assert property (@(posedge clk) a and a[*2]);
endmodule
