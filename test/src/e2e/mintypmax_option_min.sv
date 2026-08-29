// §11.11: a min:typ:max expression carries "minimum, typical, and maximum
// values -- in that order", and "the three values allow a design to be tested
// with minimum, typical, or maximum delay values". This case claims that
// `--mintypmax min`, which its .args file passes, takes the minimum member in
// both places the choice has to reach: DELAY prints 11 and $finish runs at
// time 95.
//
// The design is the one mintypmax_option_default.sv carries, which states why
// it is written this way and what the two triples are chosen to distinguish.
// The parameter folds at elaboration and the delay control is evaluated during
// the run, so a run that established the mode in one and not the other would
// print a number from one triple and a time from the other.
module mintypmax_option;
  parameter int DELAY = (11:22:33);

  initial begin
    $display("%0d", DELAY);
    #(95:100:105);
    $finish;
  end
endmodule
