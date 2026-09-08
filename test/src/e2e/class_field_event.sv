module class_field_event;
  class C;
    int f;
    function void bump();
      f = 1;
    endfunction
  endclass

  C obj = new();
  int b;

  // §9.4.2: the method's write to f is a change to an object data member, which
  // re-evaluates this whichever syntax the method used to name the property.
  always_comb b = obj.f;

  initial begin
    #1 obj.bump();
    #1 $display("%0d", b);
  end
endmodule
