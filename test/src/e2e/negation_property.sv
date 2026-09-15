// §16.12.3 Negation property: `not property_expr` evaluates, at each
// attempt, to the opposite of the underlying property, and switches the
// strength of a sequence: the clause's a1, `not a ##1 b`, negates a weak
// sequence, which holds beginning at the last tick of a clock that stops
// ticking while a is true, so a1 fails there, where a2, `not strong(a ##1
// b)`, holds. The assertions below run over four ticks, clk rising at 5,
// 15, 25 and 35 so that tick n is at 10n - 5, the tick counter counting
// through: a is high at ticks 1, 2 and 4 and b at 2, so a ##1 b matches
// from 1 at 2, the attempts from 2 and 3 can no longer match at 3, and the
// attempt from 4 is unfinished when the run ends at 40; busy is high at 3.
//
// a1 fails at 2, passes at 3 twice and fails again when the run ends, its
// fail action run in the final blocks, after $finish; a2 fails at 2 and
// passes at 3 twice, and the run's end adds nothing; a3, `not busy`, passes
// three times and fails at 3, as a4 does through p_idle, whose body is the
// negation.
module negation_property;
  logic clk = 0;
  int tick = 1;
  logic a, b, busy;
  int a1_pass = 0, a1_fail = 0;
  int a2_pass = 0, a2_fail = 0;
  int a3_pass = 0, a3_fail = 0;
  int a4_pass = 0, a4_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 2, 4};
  assign b = tick inside {2};
  assign busy = tick inside {3};

  a1: assert property (@(posedge clk) not a ##1 b)
    a1_pass++; else begin
      a1_fail++;
      if ($time == 40) $display("not a ##1 b fails at the end of the run");
    end

  a2: assert property (@(posedge clk) not strong(a ##1 b))
    a2_pass++; else begin
      a2_fail++;
      if ($time == 40)
        $display("not strong(a ##1 b) fails at the end of the run");
    end

  a3: assert property (@(posedge clk) not busy) a3_pass++; else a3_fail++;

  property p_idle;
    @(posedge clk) not busy;
  endproperty

  a4: assert property (p_idle) a4_pass++; else a4_fail++;

  initial begin
    #40;
    $display("not a ##1 b passes %0d fails %0d at ticks", a1_pass, a1_fail);
    $display("not strong(a ##1 b) passes %0d fails %0d at ticks", a2_pass,
             a2_fail);
    $display("not busy passes %0d fails %0d", a3_pass, a3_fail);
    $display("p_idle passes %0d fails %0d", a4_pass, a4_fail);
    $finish;
  end
endmodule
