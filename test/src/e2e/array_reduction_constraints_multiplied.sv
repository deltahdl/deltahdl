// §18.5.7.2 array reduction iterative constraints: in a constraint, an array
// reduction method is an expression iterated over each element of the array,
// joined by the method's operand, and its result is of the element type, or
// of the type of the expression in the with clause where one is given; and
// the size constraints of a dynamic array are solved first and the iterative
// constraints next.
// The Multiplied holds three 4-bit elements from 2 to 5 whose product is
// held to 8, which the four-bit result reaches at 8 and at 40. Over 64 draws
// every draw's elements are in range and multiply to 8 modulo 16. The line
// prints whether the count met what the clause determines and never a value
// the generator chose.
class Multiplied;
  rand bit [3:0] D[3];
  constraint each { foreach (D[i]) D[i] inside {[2:5]}; }
  constraint total { D.product() == 8; }
endclass

module array_reduction_constraints_multiplied;
  int multiplied = 0, total = 0;
  initial begin
    static Multiplied m = new;
    repeat (64) begin
      void'(m.randomize());
      total = m.D[0];
      total = total * m.D[1];
      total = total * m.D[2];
      if (m.D[0] >= 2 && m.D[0] <= 5 && m.D[1] >= 2 && m.D[1] <= 5 &&
          m.D[2] >= 2 && m.D[2] <= 5 && total % 16 == 8)
        multiplied++;
    end
    $display("three elements in range multiplying to 8 as a nibble: %0d of 64",
             multiplied);
    $finish;
  end
endmodule
