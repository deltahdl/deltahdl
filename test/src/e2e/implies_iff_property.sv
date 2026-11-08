module implies_iff_property;
  logic clk = 0;
  int tick = 1;
  logic a, b, c;
  int implies_pass = 0, implies_fail = 0;
  int iff_pass = 0, iff_fail = 0;
  int first_pass = 0, first_fail = 0;
  int seq_pass = 0, seq_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 3};
  assign b = tick inside {2, 3};
  assign c = tick inside {2, 3};

  implies_bool: assert property (@(posedge clk) a implies b)
    implies_pass++; else implies_fail++;

  iff_bool: assert property (@(posedge clk) a iff b)
    iff_pass++; else iff_fail++;

  iff_first: assert property (@(posedge clk) a iff b implies c)
    first_pass++; else first_fail++;

  implies_seq: assert property (@(posedge clk) (a ##1 b) implies c)
    seq_pass++; else seq_fail++;

  initial begin
    #40;
    $display("a implies b passes %0d fails %0d", implies_pass, implies_fail);
    $display("a iff b passes %0d fails %0d", iff_pass, iff_fail);
    $display("a iff b implies c passes %0d fails %0d", first_pass, first_fail);
    $display("(a ##1 b) implies c passes %0d fails %0d", seq_pass, seq_fail);
    $finish;
  end
endmodule
