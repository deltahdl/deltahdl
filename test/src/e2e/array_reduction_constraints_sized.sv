// §18.5.7.2 array reduction iterative constraints: in a constraint, an array
// reduction method is an expression iterated over each element of the array,
// joined by the method's operand, and its result is of the element type, or
// of the type of the expression in the with clause where one is given; and
// the size constraints of a dynamic array are solved first and the iterative
// constraints next.
// The Sized draws two to six elements whose sum through int'(item) is held
// to 100. Over 64 draws every draw's elements sum to 100 over the size
// drawn, and more than one size is drawn. The line prints whether the count
// met what the clause determines and never a value the generator chose.
class Sized;
  rand bit [7:0] C[];
  constraint c1 { C.size inside {[2:6]}; }
  constraint c2 { C.sum() with (int'(item)) == 100; }
endclass

module array_reduction_constraints_sized;
  int sized = 0, smallest = 7, largest = 0, total = 0;
  initial begin
    static Sized z = new;
    repeat (64) begin
      void'(z.randomize());
      total = 0;
      for (int i = 0; i < z.C.size(); i++) total = total + z.C[i];
      if (z.C.size() >= 2 && z.C.size() <= 6 && total == 100) sized++;
      if (z.C.size() < smallest) smallest = z.C.size();
      if (z.C.size() > largest) largest = z.C.size();
    end
    $display("the elements drawn summing to 100: %0d of 64, sizes vary: %0d",
             sized, largest > smallest);
    $finish;
  end
endmodule
