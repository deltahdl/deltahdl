module sampled_values;
  int v = 5;
  logic y;
  logic tick0 = 0;
  t0_v: assert property (@(posedge tick0) v == 5)
    $display("t0_v: at time 0 v samples its declared 5 while v is now %0d", v);
  else
    $display("t0_v: failed");
  t0_y: assert property (@(posedge tick0) y === 1'bx)
    $display("t0_y: at time 0 y samples x while y is now %0d", y);
  else
    $display("t0_y: failed");

  initial begin
    v = 9;
    y = 1;
    tick0 = 1;
  end

  logic clk = 0;
  logic a = 0;
  event e;
  always #5 clk = ~clk;

  function int twice(input int n);
    return 2 * n;
  endfunction

  pre: assert property (@(posedge clk) twice(a) == 0)
    $display("pre: sampled a is 0 at %0d, a is now %0d", $time, a);
  else
    $display("pre: sampled a is 1 at %0d, a is now %0d", $time, a);

  cc: assert property (@(posedge clk) const'(a) == a)
    $display("cc: const'(a) equals sampled a at %0d", $time);
  else
    $display("cc: const'(a) is %0d while sampled a differs at %0d", a, $time);

  ev: cover property (@(posedge clk) e.triggered)
    $display("ev: e.triggered is current at %0d", $time);

  initial begin
    #15 a = 1;
    #10 -> e;
    #7 a = 0;
    #12 $finish;
  end
endmodule
