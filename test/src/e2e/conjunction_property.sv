module conjunction_property;
  logic clk = 0;
  int tick = 1;
  logic a, b, c, d;
  int bool_pass = 0, bool_fail = 0;
  int weak_pass = 0, weak_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int mixed_pass = 0, mixed_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 4};
  assign b = tick inside {1, 2};
  assign c = tick inside {2, 3};
  assign d = tick inside {1, 4};

  bool_and: assert property (@(posedge clk) a and b)
    bool_pass++; else bool_fail++;

  weak_and: assert property (@(posedge clk) (a ##1 c) and d)
    begin
      weak_pass++;
      if ($time == 40) $display("(a ##1 c) and d passes at the end of the run");
    end else weak_fail++;

  strong_and: assert property (@(posedge clk) strong(a ##1 c) and d)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40)
        $display("strong(a ##1 c) and d fails at the end of the run");
    end

  or_and: assert property (@(posedge clk) a or b and c)
    mixed_pass++; else mixed_fail++;

  initial begin
    #40;
    $display("a and b passes %0d fails %0d", bool_pass, bool_fail);
    $display("(a ##1 c) and d passes %0d fails %0d at ticks", weak_pass,
             weak_fail);
    $display("strong(a ##1 c) and d passes %0d fails %0d at ticks",
             strong_pass, strong_fail);
    $display("a or b and c passes %0d fails %0d", mixed_pass, mixed_fail);
    $finish;
  end
endmodule
