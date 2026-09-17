// §18.5.7.2 array reduction iterative constraints: in a constraint, an array
// reduction method is an expression iterated over each element of the array,
// joined by the method's operand, and its result is of the element type, or
// of the type of the expression in the with clause where one is given; and
// the size constraints of a dynamic array are solved first and the iterative
// constraints next. The Summed below is the clause's example, a dynamic byte
// array A held to five elements whose sum through int'(item) is held below a
// bound, 300 here, which the eight-bit result the elements alone would give
// is always below; the Wrapped holds three bytes from 100 to 200 whose sum
// is held to 44, which only a sum wrapped to the element type reaches, at
// 300 or 556; the Sized draws two to six elements whose sum through
// int'(item) is held to 100; and the Multiplied holds three 4-bit elements
// from 2 to 5 whose product is held to 8, which the four-bit result reaches
// at 8 and at 40. Over 256 draws of the Summed every draw has five elements
// summing below 300 as an int, and some draw sums above 100; over 64 draws
// of the Wrapped every draw's elements are in range and sum to 44 modulo 256;
// over 64 draws of the Sized every draw's elements sum to 100 over the size
// drawn, and more than one size is drawn; over 64 draws of the Multiplied
// every draw's elements are in range and multiply to 8 modulo 16. Each line
// prints whether the count met what the clause determines and never a value
// the generator chose.
class Summed;
  rand bit [7:0] A[];
  constraint c1 { A.size == 5; }
  constraint c2 { A.sum() with (int'(item)) < 300; }
endclass

class Wrapped;
  rand bit [7:0] B[3];
  constraint each { foreach (B[i]) B[i] inside {[100:200]}; }
  constraint total { B.sum() == 44; }
endclass

class Sized;
  rand bit [7:0] C[];
  constraint c1 { C.size inside {[2:6]}; }
  constraint c2 { C.sum() with (int'(item)) == 100; }
endclass

class Multiplied;
  rand bit [3:0] D[3];
  constraint each { foreach (D[i]) D[i] inside {[2:5]}; }
  constraint total { D.product() == 8; }
endclass

module array_reduction_constraints;
  int below = 0, above = 0, wrapped = 0, sized = 0, smallest = 7, largest = 0;
  int multiplied = 0, total = 0;
  initial begin
    Summed s = new;
    Wrapped w = new;
    Sized z = new;
    Multiplied m = new;
    repeat (256) begin
      void'(s.randomize());
      total = s.A[0] + s.A[1] + s.A[2] + s.A[3] + s.A[4];
      if (s.A.size() == 5 && total < 300) below++;
      if (total > 100) above++;
    end
    repeat (64) begin
      void'(w.randomize());
      total = w.B[0] + w.B[1] + w.B[2];
      if (w.B[0] >= 100 && w.B[0] <= 200 && w.B[1] >= 100 && w.B[1] <= 200 &&
          w.B[2] >= 100 && w.B[2] <= 200 && total % 256 == 44)
        wrapped++;
    end
    repeat (64) begin
      void'(z.randomize());
      total = 0;
      for (int i = 0; i < z.C.size(); i++) total = total + z.C[i];
      if (z.C.size() >= 2 && z.C.size() <= 6 && total == 100) sized++;
      if (z.C.size() < smallest) smallest = z.C.size();
      if (z.C.size() > largest) largest = z.C.size();
    end
    repeat (64) begin
      void'(m.randomize());
      total = m.D[0];
      total = total * m.D[1];
      total = total * m.D[2];
      if (m.D[0] >= 2 && m.D[0] <= 5 && m.D[1] >= 2 && m.D[1] <= 5 &&
          m.D[2] >= 2 && m.D[2] <= 5 && total % 16 == 8)
        multiplied++;
    end
    $display("five elements summing below 300 as an int: %0d of 256", below);
    $display("a sum above 100: %0d", above > 0);
    $display("three elements in range summing to 44 as a byte: %0d of 64",
             wrapped);
    $display("the elements drawn summing to 100: %0d of 64, sizes vary: %0d",
             sized, largest > smallest);
    $display("three elements in range multiplying to 8 as a nibble: %0d of 64",
             multiplied);
    $finish;
  end
endmodule
