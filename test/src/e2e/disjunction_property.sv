// §16.12.4 Disjunction property: `property_expr1 or property_expr2`
// evaluates to true if and only if at least one of its operands does. The
// assertions below run over four ticks, clk rising at 5, 15, 25 and 35 so
// that tick n is at 10n - 5, the tick counter counting through: a is high
// at ticks 1 and 4, b at 2 and c at 3, so a ##1 b matches from 1 at 2,
// cannot match from 2 or 3, and is unfinished from 4 when the run ends at
// 40.
//
// bool_or, `a or b`, holds at 1, 2 and 4 and fails at 3. weak_or, `(a ##1
// b) or c`, is decided where either operand is: true at 2 for the attempt
// from 1, whose sequence matches there, false at 2 for the attempt from 2,
// both operands false, true at 3 through c for the attempt from 3, and, its
// weak sequence unfinished at the end of the run, true then for the attempt
// from 4, its pass action run in the final blocks after $finish. strong_or,
// `strong(a ##1 b) or c`, reads that unfinished sequence as false and fails
// then instead. not_or, `not a or b`, is (not a) or b as Table 16-3 has
// `not` bind tighter, false at 1 and 4 and true at 2 and 3.
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
