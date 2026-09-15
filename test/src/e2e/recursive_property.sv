// §16.12.17 Recursive properties: a named property is recursive where its
// declaration instantiates itself, and several properties may be mutually
// recursive; the instance is evaluated as the property's body with the
// actuals substituted for the formals, and each recursive instance stands
// after a positive advance in time, so the recursion unrolls one instance
// per tick. The abort operators may be used inside a recursive property.
// The assertions below run over eight ticks, clk rising at 5, 15, ..., 75
// so that tick n is at 10n - 5, the tick counter counting through: a and
// hold are high at every tick but 6, done at 5, go at 2 and 7, s1 and ph1
// at 1 and 3, s2 at 2, ph2 never, abt at 3 and acc at 5.
//
// always_a is the clause's prop_always over a: the attempt from each tick
// requires a at that tick and, a tick later, prop_always(a) again, so the
// attempts from 1 to 6 fail at 6, where a is low, and those from 7 and 8,
// in flight when the run ends with a high at every tick they reached, hold.
// weak_until is prop_weak_until over hold and done: the attempts from 1 to
// 5 hold at 5, where done is high, the one from 6 fails at 6 with neither
// hold nor done, and those from 7 and 8 hold at the end. guarded is p1,
// `go |-> prop_always(a)`: the attempt from 2 fails at 6, the one from 7
// holds at the end, and the six with go low hold at their tick. mutual is
// check_phase1 with check_phase2: the attempt from 1 has s1, ph1 at 1 and
// check_phase2 from 2, where s2 holds and ph2 does not, so it fails at 2;
// the one from 3 has ph1 at 3 and check_phase2 from 4, where s2 is low, so
// it holds at 4; the six with s1 low hold at their tick. aborted is p3
// with p4, `accept_on(acc) reject_on(abt) p3(a, acc, abt)` a tick after a:
// the attempts from 1 and 2 are rejected at 3, those from 3 and 4 accepted
// at 5, those from 5 and 6 fail at 6 with a low, and those from 7 and 8
// hold at the end.
module recursive_property;
  logic clk = 0;
  int tick = 1;
  logic a, hold, done, go, s1, s2, ph1, ph2, abt, acc;
  int always_pass = 0, always_fail = 0;
  int until_pass = 0, until_fail = 0;
  int guarded_pass = 0, guarded_fail = 0;
  int mutual_pass = 0, mutual_fail = 0;
  int aborted_pass = 0, aborted_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign a = !(tick inside {6});
  assign hold = !(tick inside {6});
  assign done = tick inside {5};
  assign go = tick inside {2, 7};
  assign s1 = tick inside {1, 3};
  assign s2 = tick inside {2};
  assign ph1 = tick inside {1, 3};
  assign ph2 = 0;
  assign abt = tick inside {3};
  assign acc = tick inside {5};

  property prop_always(p);
    p and (1'b1 |=> prop_always(p));
  endproperty

  property prop_weak_until(p, q);
    q or (p and (1'b1 |=> prop_weak_until(p, q)));
  endproperty

  property p1(s, p);
    s |-> prop_always(p);
  endproperty

  property check_phase1;
    s1 |-> (ph1 and (1'b1 |=> check_phase2));
  endproperty

  property check_phase2;
    s2 |-> (ph2 and (1'b1 |=> check_phase1));
  endproperty

  property p3(p, b, abort);
    (p and (1'b1 |=> p4(p, b, abort)));
  endproperty

  property p4(p, b, abort);
    accept_on(b) reject_on(abort) p3(p, b, abort);
  endproperty

  always_a: assert property (@(posedge clk) prop_always(a))
    begin
      always_pass++;
      if ($time == 80) $display("prop_always(a) passes at the end of the run");
    end else always_fail++;

  weak_until: assert property (@(posedge clk) prop_weak_until(hold, done))
    begin
      until_pass++;
      if ($time == 80)
        $display("prop_weak_until(hold, done) passes at the end of the run");
    end else until_fail++;

  guarded: assert property (@(posedge clk) p1(go, a))
    begin
      guarded_pass++;
      if ($time == 80) $display("p1(go, a) passes at the end of the run");
    end else guarded_fail++;

  mutual: assert property (@(posedge clk) check_phase1)
    mutual_pass++; else mutual_fail++;

  aborted: assert property (@(posedge clk) p3(a, acc, abt))
    begin
      aborted_pass++;
      if ($time == 80)
        $display("p3(a, acc, abt) passes at the end of the run");
    end else aborted_fail++;

  initial begin
    #80;
    $display("prop_always(a) passes %0d fails %0d at ticks", always_pass,
             always_fail);
    $display("prop_weak_until(hold, done) passes %0d fails %0d at ticks",
             until_pass, until_fail);
    $display("p1(go, a) passes %0d fails %0d at ticks", guarded_pass,
             guarded_fail);
    $display("check_phase1 passes %0d fails %0d at ticks", mutual_pass,
             mutual_fail);
    $display("p3(a, acc, abt) passes %0d fails %0d at ticks", aborted_pass,
             aborted_fail);
    $finish;
  end
endmodule
