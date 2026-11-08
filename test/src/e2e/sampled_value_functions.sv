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

  always_ff @(posedge clk) if ($time == 25) b <= 0;
  initial #20 a = 0;
  a_bad_and_ok: assert property (@(posedge clk) a == b)
  else
    $display("at %0d: current a = %b, b = %b; sampled a = %b, b = %b", $time,
             a, b, $sampled(a), $sampled(b));

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

  initial #62 b_p = 1;
  always @(posedge clk) reg1 <= en_p & $rose(b_p);
  always @(posedge clk) if (reg1) $display("reg1 set by $rose(b_p) at %0d", $time);

  initial begin
    #80;
    $finish;
  end
endmodule
