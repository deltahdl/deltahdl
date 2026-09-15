// §16.12.12 Until property: `property_expr1 until property_expr2` is true
// where property_expr1 holds at every tick from the attempt's until, not
// including, a tick property_expr2 holds at; `until_with` needs
// property_expr1 at that tick as well; and the strong forms, `s_until` and
// `s_until_with`, need a tick property_expr2 holds at to exist, where the
// weak forms hold with property_expr1 true at every tick though
// property_expr2 never holds. The assertions below run over four ticks, clk
// rising at 5, 15, 25 and 35 so that tick n is at 10n - 5, the tick counter
// counting through: a is high at ticks 1, 2 and 4, b at 3 and c at every
// tick, and the run ends at 40.
//
// weak_until, `a until b`, is true at 3 for the attempts from 1 to 3, a not
// needed there, and true when the run ends for the attempt from 4, a high
// with b never true again, its pass action run in the final blocks after
// $finish; strong_until, `a s_until b`, fails then instead. with_a, `a until_with
// b`, needs a at 3 as well and fails there for the attempts from 1 to 3,
// holding at the end for the attempt from 4; with_c, `c until_with b`, is
// true at 3 for those attempts and at the end for the last, where
// strong_with, `c s_until_with b`, fails.
module until_property;
  logic clk = 0;
  int tick = 1;
  logic a, b, c;
  int weak_pass = 0, weak_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int with_a_pass = 0, with_a_fail = 0;
  int with_c_pass = 0, with_c_fail = 0;
  int swith_pass = 0, swith_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 2, 4};
  assign b = tick inside {3};
  assign c = tick inside {1, 2, 3, 4};

  weak_until: assert property (@(posedge clk) a until b)
    begin
      weak_pass++;
      if ($time == 40) $display("a until b passes at the end of the run");
    end else weak_fail++;

  strong_until: assert property (@(posedge clk) a s_until b)
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("a s_until b fails at the end of the run");
    end

  with_a: assert property (@(posedge clk) a until_with b)
    begin
      with_a_pass++;
      if ($time == 40) $display("a until_with b passes at the end of the run");
    end else with_a_fail++;

  with_c: assert property (@(posedge clk) c until_with b)
    begin
      with_c_pass++;
      if ($time == 40) $display("c until_with b passes at the end of the run");
    end else with_c_fail++;

  strong_with: assert property (@(posedge clk) c s_until_with b)
    swith_pass++; else begin
      swith_fail++;
      if ($time == 40)
        $display("c s_until_with b fails at the end of the run");
    end

  initial begin
    #40;
    $display("a until b passes %0d fails %0d at ticks", weak_pass, weak_fail);
    $display("a s_until b passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("a until_with b passes %0d fails %0d at ticks", with_a_pass,
             with_a_fail);
    $display("c until_with b passes %0d fails %0d at ticks", with_c_pass,
             with_c_fail);
    $display("c s_until_with b passes %0d fails %0d at ticks", swith_pass,
             swith_fail);
    $finish;
  end
endmodule
