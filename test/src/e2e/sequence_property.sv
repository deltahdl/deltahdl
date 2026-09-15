// §16.12.2 Sequence property: a sequence_expr is a property in three forms,
// bare, weak(sequence_expr) and strong(sequence_expr); strong holds if and
// only if the sequence has a nonempty match, and weak holds unless a finite
// prefix witnesses that the sequence cannot match, so an attempt still in
// flight when the run ends fails a strong property and not a weak one. A
// bare sequence_expr is weak in an assert or assume and strong otherwise, in
// a cover among them. The assertions below evaluate the clause's p3, b ##1
// c, over four ticks, clk rising at 5, 15, 25 and 35 so that tick n is at
// 10n - 5, the tick counter counting through: b is high at ticks 2 to 4 and
// c at 3, so the attempt from 2 matches at 3, the attempt from 1 has no
// match from its first tick and fails at 1, the one from 3 fails at 4 where
// c is low, and the one from 4 is unfinished when the run ends at 40.
//
// weak_seq and weak_wrapped pass once and fail twice; strong_seq passes
// once and fails twice at ticks and once more when the run ends, its fail action run then, after $finish;
// and cov, whose sequence is strong, matches once.
module sequence_property;
  logic clk = 0;
  int tick = 1;
  logic b, c;
  int weak_pass = 0, weak_fail = 0;
  int wrapped_pass = 0, wrapped_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int cov_match = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign b = tick inside {2, 3, 4};
  assign c = tick inside {3};

  weak_seq: assert property (@(posedge clk) b ##1 c)
    weak_pass++; else weak_fail++;

  weak_wrapped: assert property (@(posedge clk) weak(b ##1 c))
    wrapped_pass++; else wrapped_fail++;

  strong_seq: assert property (@(posedge clk) strong(b ##1 c))
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("strong(b ##1 c) fails at the end of the run");
    end

  cov: cover property (@(posedge clk) b ##1 c) cov_match++;

  initial begin
    #40;
    $display("b ##1 c passes %0d fails %0d", weak_pass, weak_fail);
    $display("weak(b ##1 c) passes %0d fails %0d", wrapped_pass, wrapped_fail);
    $display("strong(b ##1 c) passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("cover b ##1 c matches %0d", cov_match);
    $finish;
  end
endmodule
