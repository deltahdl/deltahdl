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
