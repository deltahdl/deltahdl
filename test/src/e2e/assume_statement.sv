module assume_statement;
  logic clk = 0;
  logic req = 0, gnt = 0, rst = 0;
  logic ack = 0, reset_n = 0;
  logic x = 1;
  int v = 0;
  int passes = 0, fails = 0;
  int dist_passes = 0, dist_fails = 0;
  int inside_passes = 0, inside_fails = 0;
  int dist_hits = 0, ticks = 0;
  always #5 clk = ~clk;
  always @(posedge clk) ticks++;

  property abc(a, b, c);
    disable iff (c) @(posedge clk) a |=> b;
  endproperty
  env_prop: assume property (abc(req, gnt, rst)) else $error("Assumption failed.");
  counted: assume property (abc(req, gnt, rst))
    passes++;
  else fails++;

  null_stmt: assume property (@(posedge clk) x) ;

  a1: assume property (@(posedge clk) v dist {0:=40, 1:=60});
  dist_assert: assert property (@(posedge clk) v dist {0:=40, 1:=60})
    dist_passes++;
  else dist_fails++;
  inside_assert: assert property (@(posedge clk) v inside {0, 1})
    inside_passes++;
  else inside_fails++;
  dist_cover: cover property (@(posedge clk) v dist {0:=40, 1:=60})
    dist_hits++;

  property pr1;
    @(posedge clk) !reset_n |-> !req;
  endproperty
  property pr2;
    @(posedge clk) ack |=> !req;
  endproperty
  property pr3;
    @(posedge clk) req |-> req[*1:$] ##0 ack;
  endproperty
  property pa1;
    @(posedge clk) !reset_n || !req |-> !ack;
  endproperty
  property pa2;
    @(posedge clk) ack |=> !ack;
  endproperty
  assume_req1: assume property (pr1);
  assume_req2: assume property (pr2);
  assume_req3: assume property (pr3);
  assert_ack1: assert property (pa1) else $error("ack asserted while req is still deasserted");
  assert_ack2: assert property (pa2) else $error("ack is extended over more than one cycle");

  initial begin
    #10 reset_n = 1; req = 1;
    #10 gnt = 1;
    #10 ack = 1; v = 1;
    #10 req = 0; gnt = 0; ack = 0;
    #10 req = 1; ack = 1;
    #10 req = 0; ack = 0; x = 0;
    #2 rst = 1;
    #6 rst = 0;
    #2 x = 1; ack = 1;
    #10 ack = 0; v = 2;
    #10 $display("counted passes %0d fails %0d of %0d ticks", passes, fails, ticks);
    $display("v dist {0:=40, 1:=60} asserted passes %0d fails %0d", dist_passes, dist_fails);
    $display("v inside {0, 1} asserted passes %0d fails %0d", inside_passes, inside_fails);
    $display("v dist {0:=40, 1:=60} covered at %0d of %0d ticks", dist_hits, ticks);
    $finish;
  end
endmodule
