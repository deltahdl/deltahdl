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
