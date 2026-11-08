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
