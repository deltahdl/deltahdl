// IEEE 1800-2023 §18.17.1: the := operator assigns a weight to a production
// list and the probability that a list is generated is proportional to its
// weight, so the clause's first : add := 3 | dec := (1 + 1) generates add
// near 60% of the time and dec near 40%; a weight is only meaningful between
// alternatives, so a lone production list weighted 0 is still generated; a
// list with no weight uses 1, so a | b := 3 generates a near 25% and b near
// 75%; weight expressions are evaluated when their enclosing production is
// selected, so weights change dynamically: with w = 10 the list x := w
// beside y := (10 - w) is always taken, with w = 0 never, and three picks in
// one statement, x zeroing w, take x then y then y; and the weight may be a
// ps_identifier, a parameter W3 = 3 generating add near 60% as the literal
// did.
module production_weights;
  parameter int W3 = 3;
  int i, x, w, n, adds, decs, as, bs, xs, lone;
  int add_near, dec_near, every, a_near, b_near, always_x, never_x, then_y;
  int picks[3], p;

  initial begin
    adds = 0; decs = 0; every = 1;
    for (i = 0; i < 5000; i++) begin
      x = 0;
      randsequence( main )
        main  : first ;
        first : add := 3
              | dec := (1 + 1)
              ;
        add   : { x = 1; } ;
        dec   : { x = 2; } ;
      endsequence
      if (x == 1) adds++;
      else if (x == 2) decs++;
      else every = 0;
    end
    add_near = adds > 2850 && adds < 3150;
    dec_near = decs > 1850 && decs < 2150;
    $display("example: 5000 runs of add := 3 | dec := (1 + 1) generate add near 60%%: %0d, dec near 40%%: %0d, every run one of them: %0d",
             add_near, dec_near, every);

    as = 0; bs = 0;
    for (i = 0; i < 4000; i++) begin
      randsequence( main )
        main : a | b := 3 ;
        a    : { as++; } ;
        b    : { bs++; } ;
      endsequence
    end
    a_near = as > 900 && as < 1100;
    b_near = bs > 2900 && bs < 3100;
    $display("default: 4000 runs of a | b := 3 generate a near 25%%: %0d, b near 75%%: %0d", a_near, b_near);

    w = 10; xs = 0;
    for (i = 0; i < 100; i++) begin
      randsequence( main )
        main : x_list := w | y_list := (10 - w) ;
        x_list : { xs++; } ;
        y_list : { } ;
      endsequence
    end
    always_x = xs == 100;
    w = 0; xs = 0;
    for (i = 0; i < 100; i++) begin
      randsequence( main )
        main : x_list := w | y_list := (10 - w) ;
        x_list : { xs++; } ;
        y_list : { } ;
      endsequence
    end
    never_x = xs == 0;
    w = 10; p = 0;
    randsequence( main )
      main : pick pick pick ;
      pick : x_list := w | y_list := (10 - w) ;
      x_list : { picks[p] = 1; p++; w = 0; } ;
      y_list : { picks[p] = 2; p++; } ;
    endsequence
    then_y = picks[0] == 1 && picks[1] == 2 && picks[2] == 2;
    $display("dynamic: with w = 10 x := w is taken in all of 100: %0d, with w = 0 in none: %0d, three picks with x zeroing w take x then y then y: %0d",
             always_x, never_x, then_y);

    adds = 0;
    for (i = 0; i < 5000; i++) begin
      randsequence( first )
        first : add := W3 | dec := 2 ;
        add   : { adds++; } ;
        dec   : { } ;
      endsequence
    end
    add_near = adds > 2850 && adds < 3150;
    $display("parameter: 5000 runs with add := W3 generate add near 60%%: %0d", add_near);

    lone = 0;
    randsequence( main )
      main : only := 0 ;
      only : { lone = 1; } ;
    endsequence
    $display("single: a lone production list weighted 0 is still generated: %0d", lone);
    $finish;
  end
endmodule
