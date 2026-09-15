// §16.12.8 Implies and iff properties: `property_expr1 implies
// property_expr2` evaluates to true if and only if property_expr1 is false
// or property_expr2 true, and `property_expr1 iff property_expr2` if and
// only if both are false or both true. The assertions below run over four
// ticks, clk rising at 5, 15, 25 and 35 so that tick n is at 10n - 5, the
// tick counter counting through: a is high at ticks 1 and 3, b at 2 and 3
// and c at 2 and 3, so a ##1 b matches from 1 at 2, cannot match from 2 or
// 4, and cannot match from 3 at 4.
//
// implies_bool, `a implies b`, fails at 1 alone, a high with b low.
// iff_bool, `a iff b`, holds at 3 and 4, where both are high and both low,
// and fails at 1 and 2. iff_first, `a iff b implies c`, is (a iff b)
// implies c as Table 16-3 has iff bind tighter, and fails at 4 alone, where
// a iff b holds with c low. implies_seq, `(a ##1 b) implies c`, is false at
// 2 for the attempt from 1, whose sequence matches there with c low at 1,
// true at 2 for the attempt from 2, whose sequence cannot match, true at 3
// for the attempt from 3 through c, and true at 4 for the attempt from 4.
module implies_iff_property;
  logic clk = 0;
  int tick = 1;
  logic a, b, c;
  int implies_pass = 0, implies_fail = 0;
  int iff_pass = 0, iff_fail = 0;
  int first_pass = 0, first_fail = 0;
  int seq_pass = 0, seq_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 3};
  assign b = tick inside {2, 3};
  assign c = tick inside {2, 3};

  implies_bool: assert property (@(posedge clk) a implies b)
    implies_pass++; else implies_fail++;

  iff_bool: assert property (@(posedge clk) a iff b)
    iff_pass++; else iff_fail++;

  iff_first: assert property (@(posedge clk) a iff b implies c)
    first_pass++; else first_fail++;

  implies_seq: assert property (@(posedge clk) (a ##1 b) implies c)
    seq_pass++; else seq_fail++;

  initial begin
    #40;
    $display("a implies b passes %0d fails %0d", implies_pass, implies_fail);
    $display("a iff b passes %0d fails %0d", iff_pass, iff_fail);
    $display("a iff b implies c passes %0d fails %0d", first_pass, first_fail);
    $display("(a ##1 b) implies c passes %0d fails %0d", seq_pass, seq_fail);
    $finish;
  end
endmodule
