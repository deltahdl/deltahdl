// §16.12.6 If-else property: `if (expression_or_dist) property_expr` is
// true if and only if the expression is false or the property true, and
// `if (expression_or_dist) property_expr1 else property_expr2` if and only
// if the expression is true and property_expr1 true or the expression false
// and property_expr2 true. The assertions below run over four ticks, clk
// rising at 5, 15, 25 and 35 so that tick n is at 10n - 5, the tick counter
// counting through: req is high at ticks 1, 2 and 4, gnt at 1 and 4, done
// at 2 and idle at 1, so gnt ##1 done matches from 1 at 2, cannot match from
// 2, and is unfinished from 4 when the run ends at 40.
//
// one_branch, `if (req) gnt`, fails at 2 alone, req high with gnt low, and
// holds at 3 with req low. two_branch, `if (req) gnt else idle`, fails at 2
// and at 3, where req is low and idle with it. seq_branch, `if (req) gnt
// ##1 done else idle`, is true at 2 for the attempt from 1, whose sequence
// matches there, false at 2 for the attempt from 2, false at 3 through
// idle, and, its weak sequence unfinished at the end of the run, true then
// for the attempt from 4, its pass action run in the final blocks after
// $finish. loosest, `if (req) gnt and idle`, is if (req) (gnt and idle) as
// Table 16-3 puts if-else below every other operator, true at 1 and 3 and
// false at 2 and 4.
module if_else_property;
  logic clk = 0;
  int tick = 1;
  logic req, gnt, done, idle;
  int one_pass = 0, one_fail = 0;
  int two_pass = 0, two_fail = 0;
  int seq_pass = 0, seq_fail = 0;
  int loose_pass = 0, loose_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign req = tick inside {1, 2, 4};
  assign gnt = tick inside {1, 4};
  assign done = tick inside {2};
  assign idle = tick inside {1};

  one_branch: assert property (@(posedge clk) if (req) gnt)
    one_pass++; else one_fail++;

  two_branch: assert property (@(posedge clk) if (req) gnt else idle)
    two_pass++; else two_fail++;

  seq_branch: assert property (@(posedge clk) if (req) gnt ##1 done else idle)
    begin
      seq_pass++;
      if ($time == 40)
        $display("if (req) gnt ##1 done else idle passes at the end of the run");
    end else seq_fail++;

  loosest: assert property (@(posedge clk) if (req) gnt and idle)
    loose_pass++; else loose_fail++;

  initial begin
    #40;
    $display("if (req) gnt passes %0d fails %0d", one_pass, one_fail);
    $display("if (req) gnt else idle passes %0d fails %0d", two_pass,
             two_fail);
    $display("if (req) gnt ##1 done else idle passes %0d fails %0d at ticks",
             seq_pass, seq_fail);
    $display("if (req) gnt and idle passes %0d fails %0d", loose_pass,
             loose_fail);
    $finish;
  end
endmodule
