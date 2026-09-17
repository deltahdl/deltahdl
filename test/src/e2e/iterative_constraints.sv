// §18.5.7 Iterative constraints: an arrayed variable is constrained through
// loop variables and indexing expressions, or through array reduction
// methods. The Indexed below is the clause's example, a byte array A under
// C1, a foreach holding each element inside {2, 4, 8, 16}, and C2, a foreach
// holding each element above twice its index; the Summed holds three
// elements of B below 10 through a foreach and their sum to 12 through the
// sum() reduction. Over 128 draws of the Indexed every element of every draw
// is in the set and above twice its index, the first element is drawn at 2,
// which only its own index of 0 admits, and the last at 16; over 64 draws
// of the Summed the elements add up to 12, read element by element and
// through sum() on the object, and each is below 10. Each line prints
// whether the count met what the clause determines and never a value the
// generator chose.
class Indexed;
  rand byte A[4];
  constraint C1 { foreach (A[i]) A[i] inside {2, 4, 8, 16}; }
  constraint C2 { foreach (A[j]) A[j] > 2 * j; }
endclass

class Summed;
  rand bit [7:0] B[3];
  constraint each { foreach (B[k]) B[k] < 10; }
  constraint total { B.sum() == 12; }
endclass

module iterative_constraints;
  int in_set = 0, above = 0, first_at_two = 0, last_at_sixteen = 0;
  int totals = 0, bounded = 0;
  initial begin
    Indexed x = new;
    Summed s = new;
    repeat (128) begin
      void'(x.randomize());
      if (x.A[0] inside {2, 4, 8, 16} && x.A[1] inside {2, 4, 8, 16} &&
          x.A[2] inside {2, 4, 8, 16} && x.A[3] inside {2, 4, 8, 16})
        in_set++;
      if (x.A[0] > 0 && x.A[1] > 2 && x.A[2] > 4 && x.A[3] > 6) above++;
      if (x.A[0] == 2) first_at_two++;
      if (x.A[3] == 16) last_at_sixteen++;
    end
    repeat (64) begin
      void'(s.randomize());
      if (s.B.sum() == 12 && s.B[0] + s.B[1] + s.B[2] == 12) totals++;
      if (s.B[0] < 10 && s.B[1] < 10 && s.B[2] < 10) bounded++;
    end
    $display("every element in the set: %0d of 128", in_set);
    $display("every element above twice its index: %0d of 128", above);
    $display("the first element drawn at 2: %0d, the last at 16: %0d",
             first_at_two > 0, last_at_sixteen > 0);
    $display("the elements sum to 12: %0d of 64, each below 10: %0d of 64",
             totals, bounded);
    $finish;
  end
endmodule
