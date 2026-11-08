module class_field_event;
  class C;
    int f;
    function void bump();
      f = 1;
    endfunction
  endclass

  C obj = new();
  int b;

  always @(obj.f) b = obj.f;

  initial begin
    #1 obj.bump();
    #1 $display("%0d", b);
  end
endmodule
