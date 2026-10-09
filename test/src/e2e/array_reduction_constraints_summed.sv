// §18.5.7.2 array reduction iterative constraints: in a constraint, an array
// reduction method is an expression iterated over each element of the array,
// joined by the method's operand, and its result is of the element type, or
// of the type of the expression in the with clause where one is given; and
// the size constraints of a dynamic array are solved first and the iterative
// constraints next.
// The Summed is the clause's example, a dynamic byte array A held to five
// elements whose sum through int'(item) is held below a bound, 300 here,
// which the eight-bit result the elements alone would give is always below.
// Over 256 draws every draw has five elements summing below 300 as an int,
// and some draw sums above 100. Each line prints whether the count met what
// the clause determines and never a value the generator chose.
class Summed;
  rand bit [7:0] A[];
  constraint c1 { A.size == 5; }
  constraint c2 { A.sum() with (int'(item)) < 300; }
endclass

module array_reduction_constraints_summed;
  int below = 0, above = 0, total = 0;
  initial begin
    static Summed s = new;
    repeat (256) begin
      void'(s.randomize());
      total = s.A[0] + s.A[1] + s.A[2] + s.A[3] + s.A[4];
      if (s.A.size() == 5 && total < 300) below++;
      if (total > 100) above++;
    end
    $display("five elements summing below 300 as an int: %0d of 256", below);
    $display("a sum above 100: %0d", above > 0);
    $finish;
  end
endmodule
