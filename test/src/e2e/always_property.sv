// §16.12.11 Always property: `always property_expr` is true if and only if
// the property holds at every current or future tick; `always [min:max]
// property_expr` at every tick of the range that exists; and `s_always
// [min:max] property_expr` needs every tick of the range to exist and the
// property to hold at each. The assertions below run over four ticks, clk
// rising at 5, 15, 25 and 35 so that tick n is at 10n - 5, the tick counter
// counting through: a is high at ticks 1 to 3 and b at every tick, and the
// run ends at 40.
//
// weak_a, `always a`, fails at 4 for every attempt, a low there. weak_b,
// `always b`, is decided by no tick and holds for every attempt when the
// run ends, its pass action run four times in the final blocks after
// $finish. ranged, `always [0:1] b`, is true at 2, 3 and 4 for the attempts
// from 1 to 3 and, its second tick never reached, true at the end of the
// run for the attempt from 4; strong_ranged, `s_always [0:1] b`, fails then
// instead, the range needing that tick.
module always_property;
  logic clk = 0;
  int tick = 1;
  logic a, b;
  int weak_a_pass = 0, weak_a_fail = 0;
  int weak_b_pass = 0, weak_b_fail = 0;
  int ranged_pass = 0, ranged_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 2, 3};
  assign b = tick inside {1, 2, 3, 4};

  weak_a: assert property (@(posedge clk) always a)
    weak_a_pass++; else weak_a_fail++;

  weak_b: assert property (@(posedge clk) always b)
    begin
      weak_b_pass++;
      if ($time == 40) $display("always b passes at the end of the run");
    end else weak_b_fail++;

  ranged: assert property (@(posedge clk) always [0:1] b)
    begin
      ranged_pass++;
      if ($time == 40) $display("always [0:1] b passes at the end of the run");
    end else ranged_fail++;

  strong_ranged: assert property (@(posedge clk) s_always [0:1] b)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("s_always [0:1] b fails at the end of the run");
    end

  initial begin
    #40;
    $display("always a passes %0d fails %0d", weak_a_pass, weak_a_fail);
    $display("always b passes %0d fails %0d at ticks", weak_b_pass,
             weak_b_fail);
    $display("always [0:1] b passes %0d fails %0d at ticks", ranged_pass,
             ranged_fail);
    $display("s_always [0:1] b passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $finish;
  end
endmodule
