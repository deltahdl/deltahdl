// §18.5.7.1 foreach iterative constraints: a foreach iterates over the
// elements of an array with a loop variable per dimension, the scope of each
// loop variable being the foreach construct, and its constraint_set can hold
// predicates, which behave as guards where they involve only constants,
// state variables, loop variables or the size of the array iterated; an
// index expression can include loop variables, constants and state
// variables; and the size method of a dynamic array is solved with the size
// constraints first and is a state variable within the foreach. The Sorted
// below is the clause's example, a dynamic int array A whose size c1 holds
// inside {[1:10]} and whose c2 holds each element above the one before it
// under the guard that keeps the index in bounds, beside a property k that
// the loop variable of the same name shadows within the foreach; the Fixed
// leaves the size of A unconstrained, so a randomize() keeps the size new[]
// gave it, and holds each element to three times its index; and the Stepped
// holds each element of a four-element B from the state variable off on to
// one more than the element off places before it, through an index
// expression over the loop variable and the state variable. Over 256 draws
// of the Sorted every draw is sized 1 to 10 and ascending, every size from 1
// to 10 is drawn, and k stays 100; the Fixed sized to 5 keeps 5 elements
// holding 0, 3, 6, 9 and 12; over 64 draws of the Stepped every draw holds
// B[2] one above B[0] and B[3] one above B[1]. Each line prints whether the
// count met what the clause determines and never a value the generator
// chose.
class Sorted;
  rand int A[];
  int k = 100;
  constraint c1 { A.size inside {[1:10]}; }
  constraint c2 { foreach (A[k]) (k < A.size - 1) -> A[k + 1] > A[k]; }
endclass

class Fixed;
  rand int A[];
  constraint each { foreach (A[i]) A[i] == i * 3; }
endclass

class Stepped;
  rand int B[4];
  int off = 2;
  constraint range { foreach (B[i]) B[i] inside {[0:99]}; }
  constraint step { foreach (B[i]) (i >= off) -> B[i] == B[i - off] + 1; }
endclass

module foreach_iterative_constraints;
  int sized = 0, ascending = 0, sizes_seen = 0, stepped = 0, ok = 0;
  bit seen[11];
  initial begin
    Sorted s = new;
    Fixed f = new;
    Stepped p = new;
    repeat (256) begin
      void'(s.randomize());
      if (s.A.size() >= 1 && s.A.size() <= 10) begin
        sized++;
        seen[s.A.size()] = 1;
      end
      ok = 1;
      for (int i = 1; i < s.A.size(); i++)
        if (s.A[i] <= s.A[i - 1]) ok = 0;
      if (ok) ascending++;
    end
    for (int n = 1; n <= 10; n++)
      if (seen[n]) sizes_seen++;
    f.A = new[5];
    void'(f.randomize());
    repeat (64) begin
      void'(p.randomize());
      if (p.B[2] == p.B[0] + 1 && p.B[3] == p.B[1] + 1) stepped++;
    end
    $display("sized 1 to 10: %0d of 256, ascending: %0d of 256", sized,
             ascending);
    $display("sizes drawn: %0d of 10, k: %0d", sizes_seen, s.k);
    $display("size kept: %0d, elements: %0d %0d %0d %0d %0d", f.A.size(),
             f.A[0], f.A[1], f.A[2], f.A[3], f.A[4]);
    $display("stepped: %0d of 64", stepped);
    $finish;
  end
endmodule
