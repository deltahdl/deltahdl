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
