// §16.14.8 Nonvacuous evaluations: an evaluation attempt of a property is
// vacuous or nonvacuous, an attempt succeeding nonvacuously if and only if
// the property evaluates to true and the attempt is nonvacuous, and
// nonvacuity is defined on the structure of the property: an attempt of a
// sequence, a boolean among them, is always nonvacuous; of not p as p's
// attempt is; of p1 or p2 where either operand's attempt is; of if (e) p1
// else p2 where e held and p1's attempt is or e did not and p2's is, an
// if without else being vacuous where e did not hold; of s |-> p where a
// consequent beginning at an end point of s is; of nexttime p where there
// was a next clock event and the attempt beginning there is; of always
// [range] p where a tick of the range has a nonvacuous attempt and p fails
// at no tick before; and of accept_on (e) p where p's attempt is and e held
// at no time step of the attempt. The covers below run over six ticks, clk
// rising at 5, 15, ..., 55 so that tick n is at 10n - 5, the tick counter
// counting through: a is high at ticks 2, 4 and 5, b at 2 and 5, c and en
// at 1 to 3, and x at 4; the run ends at 60, and the results the tool
// reports at its end count each cover's successes and, among them, the
// vacuous ones.
//
// c1, not (a |-> b), succeeds at 4 alone, where a is high and b low, and
// nonvacuously, the implication's attempt having begun its consequent;
// where a is low the implication holds vacuously and its negation fails.
// c2, (a |-> b) or c, succeeds at every tick but 4 and never vacuously, c's
// attempt being a sequence's, nonvacuous whatever c is. c3, if (en) a |->
// b else c, takes the implication at 1 to 3, succeeding vacuously at 1 and
// 3, where a is low, and nonvacuously at 2, and takes c at 4 to 6, where c
// is low. c4, nexttime (a |-> b), reads the implication at the tick after
// its own: nonvacuously at 1 and 4, vacuously at 2 and 5, failing at 3,
// and the attempt of 6, with no tick after it, holds vacuously at the end
// of the run. c5, always [0:1] (a |-> b), holds nonvacuously from 1, 2 and
// 5, a tick of each range having a high, fails from 3 and 4, where the
// tick of 4 fails, and holds vacuously from 6, its second tick never
// reached. c6, accept_on (x) (a |=> b), holds vacuously at 1, 3 and 6,
// where a is low, and at 4, where x accepts it, and fails from 2 and 5.
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
