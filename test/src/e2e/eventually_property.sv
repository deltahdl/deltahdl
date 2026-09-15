// §16.12.13 Eventually property: `s_eventually property_expr` is true if
// and only if the property holds at some current or future tick;
// `eventually [min:max] property_expr` if and only if it holds at some tick
// of the range or not every tick of the range exists; and `s_eventually
// [min:max] property_expr`, the range unbounded with `$` allowed, if and
// only if it holds at some tick of the range. The assertions below run over
// four ticks, clk rising at 5, 15, 25 and 35 so that tick n is at 10n - 5,
// the tick counter counting through: a is high at tick 3 alone, and the run
// ends at 40.
//
// strong, the clause's p1, is true at 3 for the attempts from 1 to 3 and
// fails when the run ends for the attempt from 4, a never true again, its
// fail action run in the final blocks after $finish. ranged, `eventually
// [0:1] a`, is false at 2 for the attempt from 1, true at 3 for those from 2
// and 3, and true at the end for the attempt from 4, its second tick never
// reached; strong_ranged, `s_eventually [0:1] a`, fails then instead.
// unbounded, the clause's p7, `s_eventually [2:$] a`, is true at 3 for the
// attempt from 1 and fails at the end for the three after, a never true two
// or more ticks after them.
module eventually_property;
  logic clk = 0;
  int tick = 1;
  logic a;
  int strong_pass = 0, strong_fail = 0;
  int ranged_pass = 0, ranged_fail = 0;
  int sranged_pass = 0, sranged_fail = 0;
  int unbounded_pass = 0, unbounded_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {3};

  strong_ev: assert property (@(posedge clk) s_eventually a)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("s_eventually a fails at the end of the run");
    end

  ranged: assert property (@(posedge clk) eventually [0:1] a)
    begin
      ranged_pass++;
      if ($time == 40)
        $display("eventually [0:1] a passes at the end of the run");
    end else ranged_fail++;

  strong_ranged: assert property (@(posedge clk) s_eventually [0:1] a)
    sranged_pass++; else begin
      sranged_fail++;
      if ($time == 40)
        $display("s_eventually [0:1] a fails at the end of the run");
    end

  unbounded: assert property (@(posedge clk) s_eventually [2:$] a)
    unbounded_pass++; else begin
      unbounded_fail++;
      if ($time == 40)
        $display("s_eventually [2:$] a fails at the end of the run");
    end

  initial begin
    #40;
    $display("s_eventually a passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("eventually [0:1] a passes %0d fails %0d at ticks", ranged_pass,
             ranged_fail);
    $display("s_eventually [0:1] a passes %0d fails %0d at ticks",
             sranged_pass, sranged_fail);
    $display("s_eventually [2:$] a passes %0d fails %0d at ticks",
             unbounded_pass, unbounded_fail);
    $finish;
  end
endmodule
