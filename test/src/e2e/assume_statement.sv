// §16.14.2 Assume statement: an assumed property is checked and reported
// in simulation as an asserted one is; the pass statements of its action
// block run where the property is true, the fail statements where it is
// false, and neither where the evaluation is disabled; a null statement
// stands where no action is needed, and with no else clause the tool calls
// $error on a failure; a dist within an assert or cover statement is the
// inside operator with the weights ignored, and the property an assume
// statement assumes holds the same with or without its biasing. clk rises
// at 5, 15, ..., 85. The clause's env_prop assumes abc(req, gnt, rst),
// a |=> b disabled while c, with a fail statement calling $error: req is
// high at 15, 25 and 35 and gnt at 25 and 35, so the attempt of 35 fails at
// 45; req is high at 55 and rst across 65, so the attempts of 55 and 65 are
// disabled and run no statement; counted assumes the same with counting
// statements, passing at the six other ticks. null_stmt writes the null
// statement and no else clause, and x is low at 65, so the tool reports
// the failure itself. The clause's a1 assumes v dist {0:=40, 1:=60}; v is
// 0, then 1 from 30, and 2 at 85, outside the distribution, so a1 fails
// there; dist_assert and inside_assert assert the dist and the inside
// {0, 1} it is equivalent to, and dist_cover covers it, so the three count
// the same eight ticks. The clause's request and acknowledge protocol is
// assumed and asserted over req, ack and reset_n: reset_n is low at 5, req
// is raised at 10 and acknowledged at 35, raised and acknowledged at once
// at 55, and each is dropped the cycle after, so assume_req1 to
// assume_req3 and assert_ack2 hold throughout, while ack is raised at 70
// with req low, so assert_ack1 fails at 75.
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
