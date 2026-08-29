// §11.11: a min:typ:max expression carries "minimum, typical, and maximum
// values -- in that order", and "the three values allow a design to be tested
// with minimum, typical, or maximum delay values". Which member a run takes is
// what --mintypmax names. This case carries no .args file and claims that a run
// given no such option takes the typical member: DELAY prints 22 and $finish
// runs at time 100.
//
// The design puts the choice where it has to reach both consumers. DELAY folds
// at elaboration, in ConstEvalFull (src/elaborator/const_eval_func.cpp), and
// the delay control is evaluated during the run, in EvalMinTypMax
// (src/simulator/evaluation.cpp). A run in which the two disagreed would print
// a number from one triple and a time from the other. $finish prints the time
// it ran at, which is what makes the delay observable at all.
//
// 11:22:33 and 95:100:105 -- §28.16.1's own example numbers -- put no member
// equal to another member, to its position among the three, or to the 0 a fold
// that gave up leaves behind.
//
// The other two cases over this design are mintypmax_option_min and
// mintypmax_option_max, which differ from this one only in a .args file.
module mintypmax_option;
  parameter int DELAY = (11:22:33);

  initial begin
    $display("%0d", DELAY);
    #(95:100:105);
    $finish;
  end
endmodule
