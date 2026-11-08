module sequence_property;
  logic clk = 0;
  int tick = 1;
  logic b, c;
  int weak_pass = 0, weak_fail = 0;
  int wrapped_pass = 0, wrapped_fail = 0;
  int strong_pass = 0, strong_fail = 0;
  int cov_match = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign b = tick inside {2, 3, 4};
  assign c = tick inside {3};

  weak_seq: assert property (@(posedge clk) b ##1 c)
    weak_pass++; else weak_fail++;

  weak_wrapped: assert property (@(posedge clk) weak(b ##1 c))
    wrapped_pass++; else wrapped_fail++;

  strong_seq: assert property (@(posedge clk) strong(b ##1 c))
    strong_pass++; else begin
      strong_fail++;
      if ($time == 40) $display("strong(b ##1 c) fails at the end of the run");
    end

  cov: cover property (@(posedge clk) b ##1 c) cov_match++;

  initial begin
    #40;
    $display("b ##1 c passes %0d fails %0d", weak_pass, weak_fail);
    $display("weak(b ##1 c) passes %0d fails %0d", wrapped_pass, wrapped_fail);
    $display("strong(b ##1 c) passes %0d fails %0d at ticks", strong_pass,
             strong_fail);
    $display("cover b ##1 c matches %0d", cov_match);
    $finish;
  end
endmodule
