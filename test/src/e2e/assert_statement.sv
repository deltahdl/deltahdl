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
    #2 in2 = 0; y = 0;
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
