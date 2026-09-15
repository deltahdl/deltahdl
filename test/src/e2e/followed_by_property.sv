// §16.12.9 Followed-by property: `sequence_expr #-# property_expr` is true
// from a start point if and only if the antecedent has a match beginning
// there and the consequent is true from that match's end point, and `#=#`
// from the tick after it; the followed-bys are the duals of the
// implications, `s #-# p` being `not (s |-> not p)`, so an antecedent with
// no match makes them false where it makes an implication true. The
// assertions below run over four ticks, clk rising at 5, 15, 25 and 35 so
// that tick n is at 10n - 5, the tick counter counting through: req is
// high at ticks 1, 2 and 4, gnt at 1 and 4, done at 3 and rst at 2, the run
// ending at 40.
//
// overlapped, `req #-# gnt`, holds at 1 and 4, where req matches with gnt,
// and fails at 2, gnt low, and at 3, req having no match. nonoverlapped,
// `req #=# gnt`, reads gnt the tick after: the attempts from 1 and 2 fail
// at 2 and 3, the attempt from 3 fails at 3 with no match, and the attempt
// from 4, its consequent beginning at a tick the run never reaches, fails
// when the run ends, its fail action run in the final blocks after $finish.
// windowed, the clause's p1 with !rst as the consequent, `##[0:5] done #-#
// !rst`, is true at 3 for the attempts from 1, 2 and 3, done holding there
// with rst low, and fails at the end of the run for the attempt from 4,
// whose window is unfinished with no match. dual, `not (req |-> not gnt)`,
// counts as overlapped does.
module followed_by_property;
  logic clk = 0;
  int tick = 1;
  logic req, gnt, done, rst;
  int over_pass = 0, over_fail = 0;
  int non_pass = 0, non_fail = 0;
  int win_pass = 0, win_fail = 0;
  int dual_pass = 0, dual_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign req = tick inside {1, 2, 4};
  assign gnt = tick inside {1, 4};
  assign done = tick inside {3};
  assign rst = tick inside {2};

  overlapped: assert property (@(posedge clk) req #-# gnt)
    over_pass++; else over_fail++;

  nonoverlapped: assert property (@(posedge clk) req #=# gnt)
    non_pass++; else begin
      non_fail++;
      if ($time == 40) $display("req #=# gnt fails at the end of the run");
    end

  windowed: assert property (@(posedge clk) ##[0:5] done #-# !rst)
    win_pass++; else begin
      win_fail++;
      if ($time == 40)
        $display("##[0:5] done #-# !rst fails at the end of the run");
    end

  dual: assert property (@(posedge clk) not (req |-> not gnt))
    dual_pass++; else dual_fail++;

  initial begin
    #40;
    $display("req #-# gnt passes %0d fails %0d", over_pass, over_fail);
    $display("req #=# gnt passes %0d fails %0d at ticks", non_pass, non_fail);
    $display("##[0:5] done #-# !rst passes %0d fails %0d at ticks", win_pass,
             win_fail);
    $display("not (req |-> not gnt) passes %0d fails %0d", dual_pass,
             dual_fail);
    $finish;
  end
endmodule
