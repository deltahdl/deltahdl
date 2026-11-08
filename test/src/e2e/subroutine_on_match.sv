module subroutine_on_match;
  logic clk = 0;
  int tick = 1;
  int k = 0;
  logic a, b, c, d, e, f, g, h;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;
  always @(posedge clk) k <= k + 1;

  assign a = tick inside {1, 11};
  assign b = tick inside {3, 12};
  assign e = tick inside {1};
  assign f = tick inside {12};
  assign c = tick inside {21};
  assign d = tick inside {22, 23};
  assign g = tick inside {31};
  assign h = tick inside {41};

  function void note(int t);
    $display("note at tick %0d", t);
  endfunction

  function automatic void show(int by_value, ref int by_ref);
    $display("k by value = %0d, by reference = %0d", by_value, by_ref);
  endfunction

  sequence s1;
    logic v, w;
    @(posedge clk) (a, v = e) ##1
      (b[->1], w = f, $display("b after a with v = %h, w = %h", v, w));
  endsequence

  sequence every_end;
    @(posedge clk) (c ##[1:2] d,
                    $display("c ##[1:2] d ends at tick %0d", tick));
  endsequence

  sequence in_order;
    @(posedge clk) (g, $display("first at tick %0d", tick),
                       $display("second at tick %0d", tick), note(tick));
  endsequence

  sequence sampled;
    @(posedge clk) (h, show(k, k));
  endsequence

  cover sequence (s1);
  cover sequence (every_end);
  cover sequence (in_order);
  cover sequence (sampled);

  initial #450 $finish;
endmodule
