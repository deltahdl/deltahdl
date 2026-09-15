// §16.12.7 Implication: `sequence_expr |-> property_expr` evaluates the
// consequent separately from the end point of each match of the antecedent
// from the attempt's start point, and is true if and only if every such
// evaluation is, so an antecedent with no match makes the implication true;
// `|=>` begins each consequent at the tick after the match's end point. The
// assertions below run over four ticks, clk rising at 5, 15, 25 and 35 so
// that tick n is at 10n - 5, the tick counter counting through: req is high
// at ticks 1, 2 and 4, gnt at 1 and 4, ack at 2 and 3, done at 2 and 3 and
// late at 2, so req ##[1:2] ack matches from 1 at 2 and at 3, from 2 at 3,
// not at all from 3, and is unfinished from 4 when the run ends at 40.
//
// overlapped, `req |-> gnt`, reads gnt at the tick of each req and is true
// where req is low, so it fails at 2 alone. nonoverlapped, `req |=> gnt`,
// reads gnt the tick after: the attempts from 1 and 2 fail at 2 and 3, the
// attempt from 3 is true, and the attempt from 4, its consequent beginning
// at a tick the run never reaches, is true when the run ends, its pass
// action run in the final blocks after $finish. every_match, `(req ##[1:2]
// ack) |-> done`, evaluates done at both end points of the attempt from 1
// and is true at 3, where its antecedent can match no more, true at 4 for
// the attempt from 2, true at 3 for the attempt from 3, whose antecedent
// has no match, and true at the end of the run for the attempt from 4;
// one_fails, the same over late, low at 3, fails at 3 for the attempts from
// 1 and 2.
module implication_property;
  logic clk = 0;
  int tick = 1;
  logic req, gnt, ack, done, late;
  int over_pass = 0, over_fail = 0;
  int non_pass = 0, non_fail = 0;
  int every_pass = 0, every_fail = 0;
  int one_pass = 0, one_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign req = tick inside {1, 2, 4};
  assign gnt = tick inside {1, 4};
  assign ack = tick inside {2, 3};
  assign done = tick inside {2, 3};
  assign late = tick inside {2};

  overlapped: assert property (@(posedge clk) req |-> gnt)
    over_pass++; else over_fail++;

  nonoverlapped: assert property (@(posedge clk) req |=> gnt)
    begin
      non_pass++;
      if ($time == 40) $display("req |=> gnt passes at the end of the run");
    end else non_fail++;

  every_match: assert property (@(posedge clk) (req ##[1:2] ack) |-> done)
    begin
      every_pass++;
      if ($time == 40)
        $display("(req ##[1:2] ack) |-> done passes at the end of the run");
    end else every_fail++;

  one_fails: assert property (@(posedge clk) (req ##[1:2] ack) |-> late)
    begin
      one_pass++;
      if ($time == 40)
        $display("(req ##[1:2] ack) |-> late passes at the end of the run");
    end else one_fail++;

  initial begin
    #40;
    $display("req |-> gnt passes %0d fails %0d", over_pass, over_fail);
    $display("req |=> gnt passes %0d fails %0d at ticks", non_pass, non_fail);
    $display("(req ##[1:2] ack) |-> done passes %0d fails %0d at ticks",
             every_pass, every_fail);
    $display("(req ##[1:2] ack) |-> late passes %0d fails %0d at ticks",
             one_pass, one_fail);
    $finish;
  end
endmodule
