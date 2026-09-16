// §16.13.6 Sequence methods: triggered and matched read the end point of
// a named sequence, of an instance with arguments or of a formal of type
// sequence, a single bit that does not depend on where the match began.
// The clause's e1 on sysclk, rising at 8, 24, 40, ..., is run here with a
// rising at 10, b holding at 40 and c at 56, so e1 ends at 56. e2 reads
// reset at 24, inst at 40, e1's end point through triggered at 56, the same
// tick, and branch_back at 72, where it ends. e3 is on clk, rising at 5,
// 15, ..., and reads e1's end point through matched at 65, the first tick
// of clk after 56, between reset1 at 55 and branch_back1 at 75, where it
// ends. e2_with_arg takes the source sequence as a formal of type sequence
// and applies triggered to the formal; e4 instantiates it with e1's body
// as the actual, `@(posedge sysclk) $rose(a) ##1 b ##1 c`, and ends at 72
// as e2 does. The program check, instantiated in the module, waits for
// either of e1 and e2 to end, which e1 does first, and then, from the
// labelled statement, for e2.
module sequence_methods;
  logic clk = 0;
  logic sysclk = 0;
  logic a = 0, b = 0, c = 0;
  logic reset = 0, inst = 0, branch_back = 0;
  logic reset1 = 0, branch_back1 = 0;
  string e3_ends = "", e4_ends = "";
  always #5 clk = ~clk;
  always #8 sysclk = ~sysclk;

  sequence e1;
    @(posedge sysclk) $rose(a) ##1 b ##1 c;
  endsequence

  sequence e2;
    @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 branch_back;
  endsequence

  sequence e3;
    @(posedge clk) reset1 ##1 e1.matched ##1 branch_back1;
  endsequence

  sequence e2_with_arg(sequence subseq);
    @(posedge sysclk) reset ##1 inst ##1 subseq.triggered ##1 branch_back;
  endsequence

  sequence e4;
    e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c);
  endsequence

  check chk();

  initial forever begin
    wait (e3.triggered);
    e3_ends = $sformatf("%s %0d", e3_ends, $time);
    @(posedge clk);
  end
  initial forever begin
    wait (e4.triggered);
    e4_ends = $sformatf("%s %0d", e4_ends, $time);
    @(posedge sysclk);
  end

  initial begin
    #10 a = 1;
    #10 reset = 1;
    #10 reset = 0; b = 1;
    #5 inst = 1;
    #10 inst = 0;
    #5 b = 0; c = 1; reset1 = 1;
    #10 reset1 = 0;
    #5 c = 0; branch_back = 1;
    #5 branch_back1 = 1;
    #5 branch_back = 0;
    #5 branch_back1 = 0;
    #10;
    $display("e3 with e1.matched ends at%s", e3_ends);
    $display("e4 with subseq.triggered ends at%s", e4_ends);
    $finish;
  end
endmodule

program check;
  initial begin
    wait (e1.triggered || e2.triggered);
    if (e1.triggered) $display("e1 passed at %0d", $time);
    L2: wait (e2.triggered);
    if (e2.triggered) $display("e2 passed at %0d", $time);
  end
endprogram
