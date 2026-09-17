// IEEE 1800-2023 §18.16: randcase introduces a case statement that randomly
// selects one of its branches, an item's weight divided by the sum of all
// weights giving the probability of taking that branch, so the clause's
// weights of 3, 1 and 4 take the branches near 3/8, 1/8 and 1/2 of the time
// and every draw takes one branch; a zero-weighted branch is not taken and
// no branch is taken when all weights are zero; the weights are arbitrary
// expressions, each of self-determined precision and evaluated at most once,
// added as unsigned values, so with a = 1 and b = 1 the clause's 12'h800
// branch takes most draws and the a - b branch none, and with a = 8'hFF and
// b = 1 the a + b branch, whose 8-bit sum is 0, none; and the statement is
// thread stable, its random numbers coming from $urandom_range(), so a
// forked thread seeded alike selects the same branches beside a busier
// thread.
module randcase_statement;
  int x, i, c1, c2, c3, n, calls, taken, none, mostly, never, wrapped;
  byte a, b;
  int first_near, second_near, third_near, every;
  int f1[8], f2[8], busy, stable;

  function int bump();
    calls++;
    return 1;
  endfunction

  function automatic int pick();
    int y = 0;
    randcase
      3 : y = 1;
      1 : y = 2;
      4 : y = 3;
    endcase
    return y;
  endfunction

  initial begin
    c1 = 0; c2 = 0; c3 = 0;
    for (i = 0; i < 8000; i++) begin
      x = 0;
      randcase
        3 : x = 1;
        1 : x = 2;
        4 : x = 3;
      endcase
      if (x == 1) c1++;
      if (x == 2) c2++;
      if (x == 3) c3++;
    end
    first_near = c1 > 2850 && c1 < 3150;
    second_near = c2 > 850 && c2 < 1150;
    third_near = c3 > 3850 && c3 < 4150;
    every = c1 + c2 + c3 == 8000;
    $display("example: 8000 draws of weights 3, 1 and 4 take the first near 3/8: %0d, the second near 1/8: %0d, the third near 1/2: %0d, every draw one branch: %0d",
             first_near, second_near, third_near, every);

    taken = 0;
    for (i = 0; i < 1000; i++) begin
      x = 0;
      randcase
        3 : x = 1;
        0 : x = 2;
        4 : x = 3;
      endcase
      if (x == 2) taken++;
    end
    x = 0;
    randcase
      0 : x = 1;
      0 : x = 2;
    endcase
    none = x == 0;
    $display("zero: a zero-weighted branch is never taken in 1000: %0d, all weights zero takes no branch: %0d",
             taken == 0, none);

    a = 1; b = 1;
    n = 0; never = 0;
    for (i = 0; i < 1000; i++) begin
      x = 0;
      randcase
        a + b : x = 1;
        a - b : x = 2;
        a ^ ~b : x = 3;
        12'h800 : x = 4;
      endcase
      if (x == 4) n++;
      if (x == 2) never++;
    end
    mostly = n > 800;
    a = 8'hFF; b = 1;
    wrapped = 0;
    for (i = 0; i < 1000; i++) begin
      x = 0;
      randcase
        a + b : x = 1;
        a - b : x = 2;
        a ^ ~b : x = 3;
        12'h800 : x = 4;
      endcase
      if (x == 1) wrapped++;
    end
    $display("expressions: with a = 1 and b = 1 the 12'h800 branch takes most of 1000: %0d, the a - b branch none: %0d; with a = 8'hFF and b = 1 the a + b branch, 0 in 8 bits, none: %0d",
             mostly, never == 0, wrapped == 0);

    calls = 0;
    randcase
      bump() : x = 1;
      bump() : x = 2;
    endcase
    $display("once: two weight calls evaluate the function %0d times", calls);

    fork
      begin
        process p = process::self();
        p.srandom(3);
        for (int j = 0; j < 8; j++) f1[j] = pick();
      end
    join
    fork
      begin
        process q = process::self();
        q.srandom(5);
        for (int j = 0; j < 100; j++) busy = pick();
      end
      begin
        process p = process::self();
        p.srandom(3);
        for (int j = 0; j < 8; j++) f2[j] = pick();
      end
    join
    stable = 1;
    for (i = 0; i < 8; i++) if (f1[i] != f2[i]) stable = 0;
    $display("stability: a forked thread seeded 3 selects the same 8 branches beside a thread drawing 100: %0d", stable);
    $finish;
  end
endmodule
