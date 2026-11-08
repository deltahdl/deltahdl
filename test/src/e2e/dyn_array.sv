module dyn_array;
  int dyn[];
  initial begin
    dyn = new[3];
    dyn[0] = 10;
    dyn[1] = 20;
    dyn[2] = 30;
    $display("%0d", dyn.size());
    $display("%0d %0d %0d", dyn[0], dyn[1], dyn[2]);

    dyn = new[5](dyn);
    $display("%0d", dyn.size());
    $display("%0d %0d %0d %0d %0d", dyn[0], dyn[1], dyn[2], dyn[3], dyn[4]);

    dyn.delete();
    $display("%0d", dyn.size());
  end
endmodule
