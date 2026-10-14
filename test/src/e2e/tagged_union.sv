module tagged_union;
  typedef union tagged {
    int Valid;
    void Invalid;
  } VInt;

  VInt a;
  initial begin
    a = tagged Valid 42;
    $display("%0d", a.Valid);
    a = tagged Invalid;
    $display("%0d", a matches tagged Invalid ? 1 : 0);
  end
endmodule
