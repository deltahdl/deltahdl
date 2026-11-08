module nonvacuous_evaluations;
  logic clk = 0;
  int tick = 1;
  logic a, b, c, en, x;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = tick inside {2, 4, 5};
  assign b = tick inside {2, 5};
  assign c = tick inside {1, 2, 3};
  assign en = tick inside {1, 2, 3};
  assign x = tick inside {4};

  c1: cover property (@(posedge clk) not (a |-> b));
  c2: cover property (@(posedge clk) (a |-> b) or c);
  c3: cover property (@(posedge clk) if (en) a |-> b else c);
  c4: cover property (@(posedge clk) nexttime (a |-> b));
  c5: cover property (@(posedge clk) always [0:1] (a |-> b));
  c6: cover property (@(posedge clk) accept_on (x) (a |=> b));

  initial #60 $finish;
endmodule
