module examples_with_default(input logic a, b, clk);
  property q1;
    a |=> !b;
  endproperty
  default clocking posedge_clk @(posedge clk);
    property q3;
      a |=> !b;
    endproperty
  endclocking
  property q5;
    @(negedge clk) a |=> !b;
  endproperty
  sequence s2;
    a ##1 b;
  endsequence

  d1: assert property (q1) else $display("d1 failed at %0d", $time);
  d2: assert property (a |=> !b) else $display("d2 failed at %0d", $time);
  d3: assert property (@(negedge clk) a |=> !b)
    else $display("d3 failed at %0d", $time);
  d4: assert property (posedge_clk.q3)
    else $display("d4 failed at %0d", $time);
  d5: assert property (q5) else $display("d5 failed at %0d", $time);

  always @(negedge clk) begin
    p1: assert property (q1) else $display("p1 failed at %0d", $time);
    p2: assert property (posedge_clk.q3)
      else $display("p2 failed at %0d", $time);
  end

  c1: cover property (s2) $display("c1 covered at %0d", $time);
  c2: cover property (@(negedge clk) s2)
    $display("c2 covered at %0d", $time);
endmodule

module examples_without_default(input logic a, b, clk);
  property q5;
    @(negedge clk) a |=> !b;
  endproperty
  sequence s2;
    a ##1 b;
  endsequence
  sequence s3;
    @(negedge clk) s2;
  endsequence

  e1: assert property (q5) else $display("e1 failed at %0d", $time);
  e2: cover property (@(negedge clk) s2)
    $display("e2 covered at %0d", $time);
  e3: cover property (s3) $display("e3 covered at %0d", $time);
endmodule

module clock_resolution;
  logic clk = 0;
  logic a = 0, b = 0;
  always #5 clk = ~clk;

  examples_with_default u1(a, b, clk);
  examples_without_default u2(a, b, clk);

  initial begin
    #12 a = 1;
    #10 a = 0; b = 1;
    #12 b = 0;
    #6 $finish;
  end
endmodule
