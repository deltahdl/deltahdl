// §16.9.3 Sampled value functions: $sampled returns the sampled value of its
// argument, which in an action block, run in the Reactive region, differs
// from the current value where the variable was written in the tick's own
// time step; $rose, $fell, $stable and $changed compare the sampled value with
// the one at the previous tick of the clock, Figure 16-3 drawing e1 as
// $rose(req) and e2 as $fell(ack); $past returns the value sampled a stated
// number of ticks back, one by default, over the ticks its gating expression
// admits, and may read an automatic loop variable; and each serves in
// procedural code under the clock of the procedure, as the clause's `reg1 <=
// a & $rose(b)` does. clk rises at 5, 15, 25, ...
module sampled_value_functions;
  logic clk = 0;
  logic a = 1;
  logic b = 1;
  logic req = 0;
  logic ack = 1;
  logic [3:0] v = 4'b0101;
  logic [3:0] r = 0;
  logic enable = 1;
  int q = 0;
  logic en_p = 1;
  logic b_p = 0;
  logic reg1 = 0;
  always #5 clk = ~clk;

  // The clause's a1_bad and a2_ok in one assertion: at the tick at 25 the
  // sampled a is 0 and the sampled b is 1, so the property fails; the
  // always_ff clears b at that tick, so the action block reads b as 0 unless
  // it asks for $sampled(b).
  always_ff @(posedge clk) if ($time == 25) b <= 0;
  initial #20 a = 0;
  a_bad_and_ok: assert property (@(posedge clk) a == b)
  else
    $display("at %0d: current a = %b, b = %b; sampled a = %b, b = %b", $time,
             a, b, $sampled(a), $sampled(b));

  // Figure 16-3: req rises between the ticks at 15 and 25, ack falls between
  // the ticks at 45 and 55.
  initial begin
    #22 req = 1;
    #30 ack = 0;
  end
  always @(posedge clk) begin
    if ($rose(req)) $display("e1 = $rose(req) at %0d", $time);
    if ($fell(ack)) $display("e2 = $fell(ack) at %0d", $time);
    if ($changed(req) || $changed(ack))
      $display("$changed at %0d, $stable(req) is %0d", $time, $stable(req));
  end

  // $past with its arguments: q takes the time of each tick, enable is low at
  // the tick at 55, and v changes between the ticks at 35 and 45.
  always @(posedge clk) begin
    if ($time == 45) enable <= 0;
    if ($time == 55) enable <= 1;
    q <= $time;
  end
  always @(posedge clk) if ($time == 35) v <= 4'b1010;
  always @(posedge clk) begin
    for (int i = 0; i < 4; i++) r[i] = $past(v[i]);
    if ($time == 45)
      $display("at 45: v is %b and $past(v[i]) over i is %b", v, r);
    if ($time == 65)
      $display("at 65: $past(q) is %0d, $past(q, 2) is %0d, $past(q, 2, enable) is %0d",
               $past(q), $past(q, 2), $past(q, 2, enable));
  end

  // The clause's procedural example: b_p rises between the ticks at 55 and
  // 65, so reg1 is set at 65 and read as 1 at 75.
  initial #62 b_p = 1;
  always @(posedge clk) reg1 <= en_p & $rose(b_p);
  always @(posedge clk) if (reg1) $display("reg1 set by $rose(b_p) at %0d", $time);

  initial begin
    #80;
    $finish;
  end
endmodule
