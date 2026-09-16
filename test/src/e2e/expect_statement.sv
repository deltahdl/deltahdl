// §16.17 Expect statement: a procedural blocking statement that waits on a
// property evaluation, its syntax an assert property's, which blocks the
// executing process until the property succeeds or fails and schedules
// the statement following it after the Observed region in which the
// property completes; it starts a single thread of evaluation on the
// subsequent clocking event, the first evaluation at the next tick, and
// no further evaluation begins until it is executed again; on failure the
// else clause runs, or $error reports where there is none, and on success
// the pass statement runs; it can appear wherever a wait statement can,
// and being blocking its property may refer to automatic variables. clk
// rises at 5, 15, 25 and so on, and data counts the rising edges, so its
// sampled value at the posedge of 10n - 5 is n - 1.
//
// The first expect, the clause's a ##1 b ##1 c, is reached at 20 and
// evaluated from the posedge of 25, where a is 1, b at 35 and c at 45: the
// sequence matches at 45, the pass statement prints there and the
// statement following it runs at 45 as well. The second, reached at 45, is
// evaluated from 55, where a is 0: the sequence cannot match, so its else
// clause prints at 55. The third has no action block and its c is 0 at
// 65, so the tool reports the failure through $error. wait_for is the
// clause's task, its expect reading the automatic argument value: called
// for 9 at 65, it is evaluated from 75 and data is 9 at 95, the second of
// the 1 to 10 ticks, so ok is 1 at 95; called for 30 at 95, none of the
// ten ticks from 115 to 205 reads 30, so ok is 0 at 205.
module expect_statement;
  logic clk = 0;
  logic a = 0, b = 0, c = 0;
  int data = 0;
  always #5 clk = ~clk;
  always @(posedge clk) data <= data + 1;

  task automatic wait_for(integer value, output bit success);
    expect (@(posedge clk) ##[1:10] data == value) success = 1;
      else success = 0;
  endtask

  initial begin
    bit ok;
    #20;
    expect (@(posedge clk) a ##1 b ##1 c)
      $display("a ##1 b ##1 c matched at %0d", $time);
      else $display("a ##1 b ##1 c failed at %0d", $time);
    $display("ABC at %0d", $time);
    expect (@(posedge clk) a ##1 b ##1 c)
      $display("a ##1 b ##1 c matched at %0d", $time);
      else $display("a ##1 b ##1 c failed at %0d", $time);
    expect (@(posedge clk) c);
    wait_for(9, ok);
    $display("wait_for 9: ok=%0d at %0d", ok, $time);
    wait_for(30, ok);
    $display("wait_for 30: ok=%0d at %0d", ok, $time);
    $finish;
  end

  initial begin
    #22 a = 1;
    #10 b = 1;
    #10 c = 1;
    #5 a = 0;
    #10 c = 0;
  end
endmodule
