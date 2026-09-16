// §16.14.5 Using concurrent assertion statements outside procedural code:
// a concurrent assertion statement, an assert, an assume, a cover or a
// restrict, can stand outside a procedural context, within a module, an
// interface or a program, where it has always semantics, a new evaluation
// attempt of its property_spec beginning at every occurrence of its
// leading clock event, so assert property (ps) action_block is equivalent
// to always assert property (ps) action_block; and cover property (ps)
// statement_or_null to always cover property (ps) statement_or_null. The
// assertions below run over eight ticks, clk rising at 5, 15, ..., 75 so
// that tick n is at 10n - 5, the tick counter counting through: a is high
// at ticks 1, 3 and 6, b at 1, 3, 4, 6 and 7 and c at 2, 5 and 7, and the
// run ends at 80.
//
// The clause's a1 asserts the clause's rule3, @(posedge clk) a |-> b ##1
// c, from the beginning to the end of simulation: the attempts from 1 and
// 6 hold at 2 and 7, the attempt from 3 fails at 4, c low there, and the
// five attempts at which a is low hold vacuously, so a1 passes seven times
// and fails once; the always form beside it counts the same. The clause's
// c1 covers the clause's seq3, @(posedge clk) b ##1 c, from the beginning
// to the end: the attempts from 1, 4 and 6 match at 2, 5 and 7, so c1 is
// covered three times, and the always form beside it counts the same. The
// interface bus asserts its own rule3 over its ports, failing at 4 as a1
// does, and the program prog covers its own seq3, covered at 2, 5 and 7 as
// c1 is, and the tool's end-of-simulation results name the three cover
// statements, the always form's under the module alone, it carrying no
// label.
interface bus_if(input logic clk, input logic a, input logic b,
                 input logic c);
  property rule3;
    @(posedge clk) a |-> b ##1 c;
  endproperty
  if_a1: assert property (rule3)
    else $display("%m failed at %0d", $time);
endinterface

module static_concurrent_assertions;
  logic clk = 0;
  int tick = 1;
  logic a, b, c;
  int a1_pass = 0, a1_fail = 0, always_pass = 0, always_fail = 0;
  int c1_covered = 0, always_covered = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {1, 3, 6};
  assign b = tick inside {1, 3, 4, 6, 7};
  assign c = tick inside {2, 5, 7};

  bus_if bus(clk, a, b, c);

  property rule3;
    @(posedge clk) a |-> b ##1 c;
  endproperty
  a1: assert property (rule3) a1_pass++; else a1_fail++;
  always assert property (rule3) always_pass++; else always_fail++;

  sequence seq3;
    @(posedge clk) b ##1 c;
  endsequence
  c1: cover property (seq3) c1_covered++;
  always cover property (seq3) always_covered++;

  program prog;
    sequence seq3;
      @(posedge clk) b ##1 c;
    endsequence
    pr_c1: cover property (seq3) $display("%m covered at %0d", $time);
  endprogram

  initial begin
    #80 $display("a1 passes %0d fails %0d", a1_pass, a1_fail);
    $display("always assert property passes %0d fails %0d", always_pass,
             always_fail);
    $display("c1 covered %0d times", c1_covered);
    $display("always cover property covered %0d times", always_covered);
    $finish;
  end
endmodule
