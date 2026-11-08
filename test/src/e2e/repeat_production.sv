module repeat_production;
  int i, count, tail, in_range, two_seen, six_seen, both_seen, zero_none, three, no_tail;

  initial begin
    in_range = 1; two_seen = 0; six_seen = 0;
    for (i = 0; i < 100; i++) begin
      count = 0;
      randsequence()
        PUSH_OPER : repeat($urandom_range(2, 6)) PUSH ;
        PUSH      : { count++; } ;
      endsequence
      if (count < 2 || count > 6) in_range = 0;
      if (count == 2) two_seen = 1;
      if (count == 6) six_seen = 1;
    end
    both_seen = two_seen && six_seen;
    $display("example: 100 runs of repeat($urandom_range(2, 6)) PUSH each generate 2 to 6 pushes: %0d, 2 and 6 both seen: %0d",
             in_range, both_seen);

    count = 0;
    randsequence()
      NONE : repeat(0) PUSH ;
      PUSH : { count++; } ;
    endsequence
    zero_none = count == 0;
    count = 0;
    randsequence()
      SOME : repeat(1 + 2) PUSH ;
      PUSH : { count++; } ;
    endsequence
    three = count == 3;
    $display("zero: repeat(0) generates nothing: %0d, repeat(1 + 2) generates three: %0d", zero_none, three);

    count = 0; tail = 0;
    randsequence()
      main      : PUSH_OPER TAIL ;
      PUSH_OPER : repeat(5) PUSH ;
      PUSH      : { count++; if (count == 3) break; } ;
      TAIL      : { tail = 1; } ;
    endsequence
    no_tail = tail == 0;
    $display("break: a break in the third of five pushes ends the whole block after %0d pushes, the production after the repeat ungenerated: %0d",
             count, no_tail);
    $finish;
  end
endmodule
