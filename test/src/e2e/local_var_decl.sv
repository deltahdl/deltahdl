module local_var_decl;
  initial begin
    int i;
    static int j = 10;
    i = 42;
    $display("%0d", i);
    $display("%0d", j);
    for (int k = 0; k < 5; k++) begin
      if (k > 3)
        break;
    end
    $display("done");
  end
endmodule
