module assoc_event;
  // §7.9.11: the entry exists from the declaration, so arming the event control
  // below reads an element that is there rather than §7.8.6's non-existent one.
  int tab[int] = '{1: 0};

  // §9.4.2: an aggregate element is a lawful operand of an implicit event, and
  // a change to it re-evaluates the expression, so each write below fires this.
  always @(tab[1]) $display("%0d", tab[1]);

  initial begin
    #1 tab[1] = 5;
    #1 tab[1] = 9;
    #1 $finish;
  end
endmodule
