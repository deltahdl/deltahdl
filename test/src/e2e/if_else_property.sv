module if_else_property;
  logic clk = 0;
  int tick = 1;
  logic req, gnt, done, idle;
  int one_pass = 0, one_fail = 0;
  int two_pass = 0, two_fail = 0;
  int seq_pass = 0, seq_fail = 0;
  int loose_pass = 0, loose_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign req = tick inside {1, 2, 4};
  assign gnt = tick inside {1, 4};
  assign done = tick inside {2};
  assign idle = tick inside {1};

  one_branch: assert property (@(posedge clk) if (req) gnt)
    one_pass++; else one_fail++;

  two_branch: assert property (@(posedge clk) if (req) gnt else idle)
    two_pass++; else two_fail++;

  seq_branch: assert property (@(posedge clk) if (req) gnt ##1 done else idle)
    begin
      seq_pass++;
      if ($time == 40)
        $display("if (req) gnt ##1 done else idle passes at the end of the run");
    end else seq_fail++;

  loosest: assert property (@(posedge clk) if (req) gnt and idle)
    loose_pass++; else loose_fail++;

  initial begin
    #40;
    $display("if (req) gnt passes %0d fails %0d", one_pass, one_fail);
    $display("if (req) gnt else idle passes %0d fails %0d", two_pass,
             two_fail);
    $display("if (req) gnt ##1 done else idle passes %0d fails %0d at ticks",
             seq_pass, seq_fail);
    $display("if (req) gnt and idle passes %0d fails %0d", loose_pass,
             loose_fail);
    $finish;
  end
endmodule
