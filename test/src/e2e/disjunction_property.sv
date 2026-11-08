module disjunction_property;
  logic clk = 0;
  int tick = 1;
  logic a, b, c;
  int bool_pass = 0, bool_fail = 0;
  int weak_pass = 0, weak_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int not_pass = 0, not_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 4};
  assign b = tick inside {2};
  assign c = tick inside {3};

  bool_or: assert property (@(posedge clk) a or b)
    bool_pass++; else bool_fail++;

  weak_or: assert property (@(posedge clk) (a ##1 b) or c)
    begin
      weak_pass++;
      if ($time == 40) $display("(a ##1 b) or c passes at the end of the run");
    end else weak_fail++;

  strong_or: assert property (@(posedge clk) strong(a ##1 b) or c)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40)
        $display("strong(a ##1 b) or c fails at the end of the run");
    end

  not_or: assert property (@(posedge clk) not a or b)
    not_pass++; else not_fail++;

  initial begin
    #40;
    $display("a or b passes %0d fails %0d", bool_pass, bool_fail);
    $display("(a ##1 b) or c passes %0d fails %0d at ticks", weak_pass,
             weak_fail);
    $display("strong(a ##1 b) or c passes %0d fails %0d at ticks",
             strong_pass, strong_fail);
    $display("not a or b passes %0d fails %0d", not_pass, not_fail);
    $finish;
  end
endmodule
