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
  // re-evaluates this event control whichever syntax the method used to name
  // the property. An always_comb would not do: §9.2.2.2.1 keeps references to
  // class objects out of its sensitivity.
  always @(obj.f) b = obj.f;

  initial begin
    #1 obj.bump();
    #1 $display("%0d", b);
  end
endmodule
