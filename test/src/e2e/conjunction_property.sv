// §16.12.5 Conjunction property: `property_expr1 and property_expr2`
// evaluates to true if and only if both operands do. The assertions below
// run over four ticks, clk rising at 5, 15, 25 and 35 so that tick n is at
// 10n - 5, the tick counter counting through: a is high at ticks 1 and 4, b
// at 1 and 2, c at 2 and 3 and d at 1 and 4, so a ##1 c matches from 1 at
// 2, cannot match from 2 or 3, and is unfinished from 4 when the run ends at
// 40.
//
// bool_and, `a and b`, holds at 1 alone. weak_and, `(a ##1 c) and d`, is
// decided false as soon as either operand is and true once both are: true
// at 2 for the attempt from 1, whose sequence matches there, false at 2 and
// 3 for the attempts from 2 and 3, whose sequence cannot match, and, d true
// and its weak sequence unfinished at the end of the run, true then for the
// attempt from 4, its pass action run in the final blocks after $finish.
// strong_and, `strong(a ##1 c) and d`, reads that unfinished sequence as
// false and fails then instead. or_and, `a or b and c`, is a or (b and c)
// as Table 16-3 has `and` bind tighter, true at 1, 2 and 4 and false at 3.
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
