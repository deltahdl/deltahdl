module procedural_assertion_arguments;
  logic clk = 0;
  logic [10:0] foo = 11'b10101010101, bar = 11'b00000011111;
  logic w = 0, act = 0, en = 0;
  int i, n, cyc = 0;
  int a1_pass = 0, a1_fail = 0, a2_pass = 0, a2_fail = 0;
  int a3_pass = 0, a3_fail = 0, a4_pass = 0, a4_fail = 0;
  int a5_pass = 0, a5_fail = 0, a6_pass = 0, a6_fail = 0;
  int a7_pass = 0, a7_fail = 0, a7_first = 0, a7_last = 0;
  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc++;
    en = (cyc == 2);
    if (en) begin
      a9: assert property (1) $display("a9 evaluated at %0d", $time);
    end
    if ($sampled(en)) begin
      a10: assert property (1) $display("a10 evaluated at %0d", $time);
    end
  end

  always @(posedge clk) begin
    for (i = 0; i < 10; i++) begin
      a1: assert property (foo[i] && bar[i]) a1_pass++; else a1_fail++;
      a2: assert property (foo[const'(i)] && bar[i]) a2_pass++;
      else a2_fail++;
      a3: assert property (foo[const'(i)] && bar[const'(i)]) a3_pass++;
      else a3_fail++;
    end
  end

  always @(posedge clk) begin
    for (int j = 0; j < 10; j++) begin
      a4: assert property (foo[j] && bar[j]) a4_pass++; else a4_fail++;
      a5: assert property (foo[const'(j)] && bar[j]) a5_pass++;
      else a5_fail++;
      a6: assert property (foo[const'(j)] && bar[const'(j)]) a6_pass++;
      else a6_fail++;
    end
  end

  always @(posedge clk) begin : procedural_block_1
    if (act == 1) begin
      for (int k = 0; k < 2; k++) begin
        a7: assume property (foo[k] |=> bar[k] ##1 (w == 1'b1)) begin
          a7_pass++;
          if (a7_pass == 1) a7_first = $time;
          else a7_last = $time;
        end else a7_fail++;
      end
    end
  end

  always @(posedge clk) begin
    for (n = 0; n < 4; n++) begin
      a8: assert property (foo[const'(n)] && bar[n]) else
        $display("a8 failed for const n=%0d and n=%0d", const'(n),
                 $sampled(n));
    end
  end

  initial begin
    #12 act = 1;
    #6 act = 0;
    #12 w = 1;
    #10 $display("a1 passes %0d fails %0d", a1_pass, a1_fail);
    $display("a2 passes %0d fails %0d", a2_pass, a2_fail);
    $display("a3 passes %0d fails %0d", a3_pass, a3_fail);
    $display("a4 passes %0d fails %0d", a4_pass, a4_fail);
    $display("a5 passes %0d fails %0d", a5_pass, a5_fail);
    $display("a6 passes %0d fails %0d", a6_pass, a6_fail);
    $display("a7 passes %0d fails %0d, at %0d and %0d", a7_pass, a7_fail,
             a7_first, a7_last);
    $finish;
  end
endmodule
