// §18.5.7.2 array reduction iterative constraints: in a constraint, an array
// reduction method is an expression iterated over each element of the array,
// joined by the method's operand, and its result is of the element type, or
// of the type of the expression in the with clause where one is given; and
// the size constraints of a dynamic array are solved first and the iterative
// constraints next.
// The Wrapped holds three bytes from 100 to 200 whose sum is held to 44,
// which only a sum wrapped to the element type reaches, at 300 or 556. Over
// 64 draws every draw's elements are in range and sum to 44 modulo 256. The
// line prints whether the count met what the clause determines and never a
// value the generator chose.
class Wrapped;
  rand bit [7:0] B[3];
  constraint each { foreach (B[i]) B[i] inside {[100:200]}; }
  constraint total { B.sum() == 44; }
endclass

module array_reduction_constraints_wrapped;
  int wrapped = 0, total = 0;
  initial begin
    static Wrapped w = new;
    repeat (64) begin
      void'(w.randomize());
      total = w.B[0] + w.B[1] + w.B[2];
      if (w.B[0] >= 100 && w.B[0] <= 200 && w.B[1] >= 100 && w.B[1] <= 200 &&
          w.B[2] >= 100 && w.B[2] <= 200 && total % 256 == 44)
        wrapped++;
    end
    $display("three elements in range summing to 44 as a byte: %0d of 64",
             wrapped);
    $finish;
  end
endmodule
