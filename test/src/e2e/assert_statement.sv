// §16.14.1 Assert statement: the assert statement enforces a property;
// the pass statements of its action block run where the property is true,
// the fail statements where it is false, and neither where the evaluation
// is disabled; a null statement stands where no action is needed; with no
// else clause the tool calls $error on a failure; the action block may not
// hold a concurrent assertion but may hold an immediate one; and the pass
// and fail statements run in the Reactive region. clk rises at 5, 15, ...,
// 75. The clause's env_prop asserts abc(rst, in1, in2), not (b ##1 c)
// disabled while a is 2, on the clock the body opens with after its
// disable condition: in1 is high at 15 and in2 at 25, so the attempt of 15
// fails at 25; in1 is high at 35 and in2 at 45, but rst is 2 across 45, so
// that attempt is disabled and runs no statement; the other attempts pass,
// five in all. no_else has no else clause and x is low at 65, so the tool
// reports the failure itself; null_fail has a null fail statement and y is
// low at 55, so its else clause is not omitted and the tool reports
// nothing; nested holds an immediate assertion in its fail statement,
// which reads z's value in the Reactive region, 0, at 75.
// reactive counts the ticks at which its pass statement saw the write an
// always procedure made in the tick's Active region.
module assert_statement;
  logic clk = 0;
  int rst = 0;
  logic in1 = 0, in2 = 0;
  logic x = 1, y = 1, z = 1;
  int passes = 0, fails = 0, y_passes = 0;
  int marker = 0, reactive_ok = 0, ticks = 0;
  always #5 clk = ~clk;

  property abc(a, b, c);
    disable iff (a==2) @(posedge clk) not (b ##1 c);
  endproperty
  env_prop: assert property (abc(rst, in1, in2))
    passes++;
  else begin
    fails++;
    $display("env_prop failed at %0d", $time);
  end

  no_else: assert property (@(posedge clk) x);

  null_fail: assert property (@(posedge clk) y)
    y_passes++;
  else ;

  nested: assert property (@(posedge clk) z)
    else begin
      assert (z == 0)
        $display("nested: immediate assertion in the fail statement passed at %0d",
                 $time);
    end

  always @(posedge clk) begin
    marker = $time;
    ticks++;
  end
  reactive: assert property (@(posedge clk) 1)
    if (marker == $time) reactive_ok++;

  initial begin
    #10 in1 = 1;
    #10 in1 = 0; in2 = 1;
    #10 in2 = 0; in1 = 1;
    #8 rst = 2;
    #2 in1 = 0; in2 = 1;
    #8 rst = 0;
    #2 in2 = 0;
    #10 y = 0;
    #10 y = 1; x = 0;
    #10 x = 1; z = 0;
    #10 z = 1;
    $display("env_prop passes %0d fails %0d", passes, fails);
    $display("null_fail passes %0d of %0d ticks", y_passes, ticks);
    $display("reactive: pass statements saw the tick's Active write at %0d of %0d ticks",
             reactive_ok, ticks);
    $finish;
  end
endmodule
