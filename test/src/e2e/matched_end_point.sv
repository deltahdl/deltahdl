// §16.13.5 Detecting and using the end point of a sequence in multiclock
// context: where the clock of the source sequence differs from the
// destination sequence's, its end point is detected with the method
// matched, which, unlike triggered, synchronizes between the two clocks by
// storing the result of the source match until the first tick of the
// destination clock after it; the result does not depend on the source's
// starting point, and the method applies to an instance with arguments.
// The clause's e1 and e2 are run here: e1 on clk, rising at 5, 15, ..., and
// e2 on sysclk, rising at 8, 24, 40, ..., the two never together. Each
// process records the times its sequence reaches an end point at.
//
// e1(ready, proc1, proc2) matches at 35, ready having risen for the tick at
// 15 and proc1 and proc2 holding at 25 and 35, and again at 95. e2 reads
// reset at 8 and inst at 24, and e1's end point through matched at 40, the
// first tick of sysclk after 35, and branch_back at 56, where it ends; the
// second round has reset at 72, inst at 88, the match of 95 read at 104,
// and branch_back at 120. e2_triggered reads the end point through
// triggered, which is true at the time step of the match alone, 35, no
// tick of sysclk, so it never ends. twice reads matched on e1_inst, the
// instance named, at consecutive ticks of sysclk: the first read consumes
// the stored match, so the second reads false and the sequence never ends.
module matched_end_point;
  logic clk = 0;
  logic sysclk = 0;
  logic ready = 0, proc1 = 0, proc2 = 0;
  logic reset = 0, inst = 0, branch_back = 0;
  string e2_ends = "", triggered_ends = "", twice_ends = "";
  always #5 clk = ~clk;
  always #8 sysclk = ~sysclk;

  sequence e1(a, b, c);
    @(posedge clk) $rose(a) ##1 b ##1 c;
  endsequence

  sequence e2;
    @(posedge sysclk) reset ##1 inst ##1 e1(ready, proc1, proc2).matched [->1]
      ##1 branch_back;
  endsequence

  sequence e2_triggered;
    @(posedge sysclk) reset ##1 inst ##1 e1(ready, proc1, proc2).triggered [->1]
      ##1 branch_back;
  endsequence

  sequence e1_inst;
    e1(ready, proc1, proc2);
  endsequence

  sequence twice;
    @(posedge sysclk) e1_inst.matched ##1 e1_inst.matched;
  endsequence

  initial forever begin
    wait (e2.triggered);
    e2_ends = $sformatf("%s %0d", e2_ends, $time);
    @(posedge sysclk);
  end
  initial forever begin
    wait (e2_triggered.triggered);
    triggered_ends = $sformatf("%s %0d", triggered_ends, $time);
    @(posedge sysclk);
  end
  initial forever begin
    wait (twice.triggered);
    twice_ends = $sformatf("%s %0d", twice_ends, $time);
    @(posedge sysclk);
  end

  initial begin
    #5 reset = 1;
    #5 reset = 0; ready = 1;
    #10 inst = 1; proc1 = 1;
    #10 inst = 0; proc1 = 0; proc2 = 1;
    #10 proc2 = 0;
    #10 ready = 0; branch_back = 1;
    #10 branch_back = 0;
    #10 reset = 1; ready = 1;
    #5 reset = 0;
    #5 inst = 1; proc1 = 1;
    #10 inst = 0; proc1 = 0; proc2 = 1;
    #10 proc2 = 0;
    #15 branch_back = 1;
    #10 branch_back = 0;
    #5;
    $display("e2 with e1(ready, proc1, proc2).matched [->1] ends at%s",
             e2_ends);
    $display("e2 with e1(ready, proc1, proc2).triggered [->1] ends at%s",
             triggered_ends);
    $display("e1_inst.matched ##1 e1_inst.matched ends at%s", twice_ends);
    $finish;
  end
endmodule
