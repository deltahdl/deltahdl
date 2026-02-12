module local_var_decl;
  initial begin
    int i;
    i = 42;
    $display("%0d", i);
    int j = 10;
    $display("%0d", j);
    for (int k = 0; k < 5; k++) begin
      if (k > 3)
        break;
    end
    $display("done");
  end
endmodule
