// §16.12.10 Nexttime property: `nexttime property_expr` is true if and only
// if the property is true beginning at the next tick or there is no
// further tick, and `s_nexttime property_expr` if and only if there is a
// next tick and the property is true beginning there; the indexed forms
// `nexttime [n]` and `s_nexttime [n]` count n ticks instead of one, the
// weak form holding where fewer follow and the strong failing. The
// assertions below run over four ticks, clk rising at 5, 15, 25 and 35 so
// that tick n is at 10n - 5, the tick counter counting through: a is high
// at ticks 2 and 3, and the run ends at 40, tick 4 the last.
//
// weak_next, the clause's p1, is true at 2 and 3 for the attempts from 1
// and 2, false at 4 for the attempt from 3, and true when the run ends for
// the attempt from 4, no tick following, its pass action run in the final
// blocks after $finish; strong_next, p2, fails then instead. weak_two, p7,
// is true at 3 for the attempt from 1, false at 4 for the attempt from 2,
// and true when the run ends for the attempts from 3 and 4, fewer than two
// ticks following; strong_two, p8, fails then twice.
module nexttime_property;
  logic clk = 0;
  int tick = 1;
  logic a;
  int weak_pass = 0, weak_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int two_pass = 0, two_fail = 0;
  int stwo_pass = 0, stwo_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {2, 3};

  weak_next: assert property (@(posedge clk) nexttime a)
    begin
      weak_pass++;
      if ($time == 40) $display("nexttime a passes at the end of the run");
    end else weak_fail++;

  strong_next: assert property (@(posedge clk) s_nexttime a)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("s_nexttime a fails at the end of the run");
    end

  weak_two: assert property (@(posedge clk) nexttime [2] a)
    begin
      two_pass++;
      if ($time == 40) $display("nexttime [2] a passes at the end of the run");
    end else two_fail++;

  strong_two: assert property (@(posedge clk) s_nexttime [2] a)
    stwo_pass++; else begin
      stwo_fail++;
      if ($time == 40)
        $display("s_nexttime [2] a fails at the end of the run");
    end

  initial begin
    #40;
    $display("nexttime a passes %0d fails %0d at ticks", weak_pass, weak_fail);
    $display("s_nexttime a passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("nexttime [2] a passes %0d fails %0d at ticks", two_pass,
             two_fail);
    $display("s_nexttime [2] a passes %0d fails %0d at ticks", stwo_pass,
             stwo_fail);
    $finish;
  end
endmodule
