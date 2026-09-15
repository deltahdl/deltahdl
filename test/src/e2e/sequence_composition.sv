// §16.9.11 Composing sequences from simpler subsequences: a named sequence
// instantiated by name in another must match from the tick the reference is
// reached at, while its end point is detected with the method triggered,
// which is true at a tick the sequence reaches an end point at whatever the
// match's starting point, applied to an instance with or without arguments;
// and a sequence's empty match does not activate triggered. The clause's
// examples run below, sysclk rising at 5, 15, 25, ... so that tick n is at
// 10n - 5, the tick counter counting straight through, and each process
// records the ticks its sequence reaches an end point at.
//
// Ticks 1 to 6 run rule1: trans is high at 1, start_trans at 2, a at 3, b at
// 4, c at 5 and end_trans at 6, so s, `a ##1 b ##1 c`, matches from 3, the
// tick after start_trans, and rule1 ends at 6.
//
// Ticks 11 to 14 run the triggered forms: reset is high at 11, inst at 12,
// ready from 11 to 13, proc1 at 12, proc2 at 13 and branch_back at 14, so e1,
// `$rose(ready) ##1 proc1 ##1 proc2`, matches from 11 to 13 and reaches its
// end point at 13, one tick after inst, where rule_triggered, rule2 and
// rule2a read it, and each ends at 14; rule_instance, which instantiates e1
// where they read its end point, needs e1 to match from 13, where ready does
// not rise, so it does not end. Ticks 21 to 26 run the same with ready rising
// at 23, proc1 at 24, proc2 at 25 and branch_back at 26: e1 matches from 23,
// so rule_instance ends at 26, while no end point of e1 falls at 23 and the
// triggered forms do not end.
//
// Ticks 31 and 32 have req high, so zero_or_one_req, `(req==1'b1)[*0:1]`,
// reaches an end point at each of them and, its empty match not activating
// triggered, at no other tick.
module sequence_composition;
  logic sysclk = 0;
  int tick = 1;
  logic trans, start_trans, a, b, c, end_trans;
  logic reset, inst, ready, proc1, proc2, branch_back, req;
  string rule1_ends = "";
  string triggered_ends = "";
  string instance_ends = "";
  string rule2_ends = "";
  string rule2a_ends = "";
  string req_ends = "";
  always #5 sysclk = ~sysclk;
  always #10 tick = tick + 1;

  assign trans = tick inside {1};
  assign start_trans = tick inside {2};
  assign a = tick inside {3};
  assign b = tick inside {4};
  assign c = tick inside {5};
  assign end_trans = tick inside {6};
  assign reset = tick inside {11, 21};
  assign inst = tick inside {12, 22};
  assign ready = tick inside {11, 12, 13, 23, 24, 25};
  assign proc1 = tick inside {12, 24};
  assign proc2 = tick inside {13, 25};
  assign branch_back = tick inside {14, 26};
  assign req = tick inside {31, 32};

  sequence s;
    a ##1 b ##1 c;
  endsequence

  sequence rule1;
    @(posedge sysclk) trans ##1 start_trans ##1 s ##1 end_trans;
  endsequence

  sequence e1;
    @(posedge sysclk) $rose(ready) ##1 proc1 ##1 proc2;
  endsequence

  sequence rule_triggered;
    @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 branch_back;
  endsequence

  sequence rule_instance;
    @(posedge sysclk) reset ##1 inst ##1 e1 ##1 branch_back;
  endsequence

  sequence e2(a, b, c);
    @(posedge sysclk) $rose(a) ##1 b ##1 c;
  endsequence

  sequence rule2;
    @(posedge sysclk) reset ##1 inst ##1 e2(ready, proc1, proc2).triggered
      ##1 branch_back;
  endsequence

  sequence e2_instantiated;
    e2(ready, proc1, proc2);
  endsequence

  sequence rule2a;
    @(posedge sysclk) reset ##1 inst ##1 e2_instantiated.triggered ##1
      branch_back;
  endsequence

  sequence zero_or_one_req;
    @(posedge sysclk) (req==1'b1)[*0:1];
  endsequence

  initial forever begin
    wait (rule1.triggered);
    rule1_ends = $sformatf("%s %0d", rule1_ends, tick);
    @(posedge sysclk);
  end
  initial forever begin
    wait (rule_triggered.triggered);
    triggered_ends = $sformatf("%s %0d", triggered_ends, tick);
    @(posedge sysclk);
  end
  initial forever begin
    wait (rule_instance.triggered);
    instance_ends = $sformatf("%s %0d", instance_ends, tick);
    @(posedge sysclk);
  end
  initial forever begin
    wait (rule2.triggered);
    rule2_ends = $sformatf("%s %0d", rule2_ends, tick);
    @(posedge sysclk);
  end
  initial forever begin
    wait (rule2a.triggered);
    rule2a_ends = $sformatf("%s %0d", rule2a_ends, tick);
    @(posedge sysclk);
  end
  initial forever begin
    wait (zero_or_one_req.triggered);
    req_ends = $sformatf("%s %0d", req_ends, tick);
    @(posedge sysclk);
  end

  initial begin
    #350;
    $display("trans ##1 start_trans ##1 s ##1 end_trans ends at ticks%s",
             rule1_ends);
    $display("reset ##1 inst ##1 e1.triggered ##1 branch_back ends at ticks%s",
             triggered_ends);
    $display("reset ##1 inst ##1 e1 ##1 branch_back ends at ticks%s",
             instance_ends);
    $display("rule2 with e2(ready, proc1, proc2).triggered ends at ticks%s",
             rule2_ends);
    $display("rule2a with e2_instantiated.triggered ends at ticks%s",
             rule2a_ends);
    $display("(req==1'b1)[*0:1] ends at ticks%s", req_ends);
    $finish;
  end
endmodule
