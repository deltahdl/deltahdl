// IEEE 1800-2023 §18.13.2: $urandom_range returns an unsigned integer within
// maxval ... minval. With minval omitted the range is maxval ... 0, and with
// maxval below minval the arguments are reversed so that the first is the
// larger, so the clause's three examples, (7, 0), (7) and (0, 7), each yield
// 0 to 7 inclusive. Both arguments are int unsigned, so a range above the
// largest int is honoured. The function is automatically thread stable
// (§18.14.2): a thread's draws are independent of another thread's.
module urandom_range_function;
  int i, k;
  int unsigned r;
  int in_range, in_range_omitted, in_range_reversed;
  bit [7:0] seen, seen_omitted, seen_reversed;
  int equal_bounds, above_int_max;
  int unsigned first_a[8], first_c[8];
  int unsigned other;
  int stable;

  initial begin
    in_range = 0;
    in_range_omitted = 0;
    in_range_reversed = 0;
    seen = 0;
    seen_omitted = 0;
    seen_reversed = 0;
    for (i = 0; i < 256; i++) begin
      r = $urandom_range(7, 0);
      if (r <= 7) begin in_range++; seen[r] = 1; end
      r = $urandom_range(7);
      if (r <= 7) begin in_range_omitted++; seen_omitted[r] = 1; end
      r = $urandom_range(0, 7);
      if (r <= 7) begin in_range_reversed++; seen_reversed[r] = 1; end
    end
    $display("examples: within 0..7 in %0d of 256 with %0d values seen, minval omitted %0d with %0d seen, reversed %0d with %0d seen",
             in_range, $countones(seen), in_range_omitted, $countones(seen_omitted),
             in_range_reversed, $countones(seen_reversed));

    // Equal bounds leave one value; bounds above the largest int are unsigned.
    equal_bounds = 0;
    above_int_max = 0;
    for (i = 0; i < 32; i++) begin
      if ($urandom_range(5, 5) == 5) equal_bounds++;
      r = $urandom_range(32'hFFFF_FFFF, 32'hFFFF_FFF0);
      if (r >= 32'hFFFF_FFF0) above_int_max++;
    end
    $display("equal bounds return 5 in %0d of 32, a range above the largest int is kept in %0d of 32",
             equal_bounds, above_int_max);

    // Thread stability: a thread seeded the same way draws the same values
    // whether the thread beside it draws eight numbers or a hundred more.
    fork
      begin
        process p = process::self();
        p.srandom(9);
        for (k = 0; k < 8; k++) first_a[k] = $urandom_range(1000);
      end
      begin
        repeat (8) other = $urandom_range(1000);
      end
    join
    fork
      begin
        process q = process::self();
        q.srandom(9);
        for (k = 0; k < 8; k++) first_c[k] = $urandom_range(1000);
      end
      begin
        repeat (108) other = $urandom_range(1000);
      end
    join
    stable = 0;
    for (i = 0; i < 8; i++) if (first_a[i] == first_c[i]) stable++;
    $display("thread stable: the seeded thread replays %0d of 8 beside a busier neighbour", stable);
    $finish;
  end
endmodule
