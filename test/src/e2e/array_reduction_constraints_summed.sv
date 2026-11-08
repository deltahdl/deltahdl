class Summed;
  rand bit [7:0] A[];
  constraint c1 { A.size == 5; }
  constraint c2 { A.sum() with (int'(item)) < 300; }
endclass

module array_reduction_constraints_summed;
  int below = 0, above = 0, total = 0;
  initial begin
    static Summed s = new;
    repeat (64) begin
      void'(s.randomize());
      total = s.A[0] + s.A[1] + s.A[2] + s.A[3] + s.A[4];
      if (s.A.size() == 5 && total < 300) below++;
      if (total > 100) above++;
    end
    $display("five elements summing below 300 as an int: %0d of 64", below);
    $display("a sum above 100: %0d", above > 0);
    $finish;
  end
endmodule
