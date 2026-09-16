// §16.14.3 Cover statement: a cover property monitors property coverage,
// its count rising at most once per evaluation attempt, and a cover
// sequence monitors sequence coverage, every match of an attempt counted;
// the pass statement of the first runs once for each successful attempt
// and the pass statement of the second once for each match, both in the
// Reactive region of the time step the attempt succeeds or the match
// completes in; the results a tool reports at the end of simulation are,
// for a property, the attempts, the successes and the successes because of
// vacuity, the attempts counting the disabled evaluations and the other two
// not, and, for a sequence, the attempts and the matches, a match that
// completes after the disable condition occurred counting nothing. clk
// rises at 5, 15, ..., 85, so each statement attempts nine times; req is
// high at 15, 45 and 75, ack at 25, 35, 55 and 65, and rst across 65.
// implied covers req |=> ack disabled while rst: the attempts of 15 and 45
// succeed at 25 and 55, the attempts of 5, 25, 35, 55 and 85 succeed
// vacuously, req being low, the attempt of 65 is disabled and the attempt
// of 75 fails at 85, so its pass statement runs seven times. acked covers
// ack, succeeding at the four ticks ack is high, its pass statement
// reading the tick's time where marker, written in the Active region,
// already holds it. requested covers req with the null statement and runs
// nothing. matched covers the sequence req ##[1:2] ack disabled while
// rst: the attempt of 15 matches at 25 and again at 35, the attempt of 45
// matches at 55 and would match at 65, where rst is high, and the attempt
// of 75 is still in flight at the end, so its pass statement runs three
// times.
module cover_statement;
  logic clk = 0;
  logic req = 0, ack = 0, rst = 0;
  int implied_hits = 0, acked_hits = 0, reactive_hits = 0;
  int matched_hits = 0, marker = 0;
  always #5 clk = ~clk;
  always @(posedge clk) marker = $time;

  implied: cover property (@(posedge clk) disable iff (rst) req |=> ack)
    implied_hits++;
  acked: cover property (@(posedge clk) ack) begin
    acked_hits++;
    if (marker == $time) reactive_hits++;
  end
  requested: cover property (@(posedge clk) req);
  matched: cover sequence (@(posedge clk) disable iff (rst) req ##[1:2] ack)
    matched_hits++;

  initial begin
    #10 req = 1;
    #10 req = 0; ack = 1;
    #20 ack = 0; req = 1;
    #10 req = 0; ack = 1;
    #12 rst = 1;
    #6 rst = 0;
    #2 ack = 0; req = 1;
    #10 req = 0;
    #10 $display("implied: pass statement ran %0d times", implied_hits);
    $display("acked: pass statement ran %0d times, %0d in the Reactive region",
             acked_hits, reactive_hits);
    $display("matched: pass statement ran %0d times", matched_hits);
    $finish;
  end
endmodule
