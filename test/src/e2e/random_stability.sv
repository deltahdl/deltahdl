// IEEE 1800-2023 §18.14: the RNG is localized to threads and objects, and the
// sequence of random values a thread or object returns is independent of the
// RNG in other threads or objects, which is random stability; it applies to
// $urandom and $urandom_range, shuffle(), randcase and randsequence, srandom()
// and randomize(). So a thread seeded and drawn from through every one of
// those returns the same values whether or not objects and other threads draw
// between, and an object seeded and randomized returns the same values whether
// or not its thread and another object draw between; another seed selects
// other values, so the agreement is the stability and not a constant.
module random_stability;
  class Packet;
    rand bit [15:0] payload;
  endclass

  Packet a, b;
  process p;
  int i, k;
  int arr[8];
  int unsigned u, r;
  int f, c, q;
  int unsigned u1, u2, u3, r1, r2, r3, t1[4], t2[4], t3[4], busy[100];
  int f1, f2, f3, c1, c2, c3, q1, q2, q3;
  bit [15:0] s1[4], s2[4], s3[4];
  int untouched_by_objects, changed_by_seed, untouched_by_thread, untouched_by_draws, changed_by_object_seed;

  // The five kinds the clause lists, drawn from the running thread's RNG.
  task automatic draw_five();
    int j;
    u = $urandom;
    r = $urandom_range(1000);
    for (j = 0; j < 8; j++) arr[j] = j + 1;
    arr.shuffle();
    f = arr[0];
    randcase
      1: c = 1;
      1: c = 2;
      1: c = 3;
    endcase
    randsequence(main)
      main : one | two | three;
      one : { q = 1; };
      two : { q = 2; };
      three : { q = 3; };
    endsequence
  endtask

  initial begin
    a = new;
    b = new;
    p = process::self();

    p.srandom(11);
    draw_five();
    u1 = u; r1 = r; f1 = f; c1 = c; q1 = q;
    for (i = 0; i < 4; i++) t1[i] = $urandom;
    p.srandom(11);
    a.srandom(7);
    for (i = 0; i < 4; i++) k = a.randomize();
    for (i = 0; i < 4; i++) k = b.randomize();
    draw_five();
    u2 = u; r2 = r; f2 = f; c2 = c; q2 = q;
    for (i = 0; i < 4; i++) t2[i] = $urandom;
    untouched_by_objects = 0;
    if (u1 == u2) untouched_by_objects++;
    if (r1 == r2) untouched_by_objects++;
    if (f1 == f2) untouched_by_objects++;
    if (c1 == c2) untouched_by_objects++;
    if (q1 == q2) untouched_by_objects++;
    for (i = 0; i < 4; i++) if (t1[i] == t2[i]) untouched_by_objects++;
    p.srandom(12);
    draw_five();
    changed_by_seed = u != u1;
    $display("thread: seeded 11 and drawn from between draws of two objects, $urandom, $urandom_range, shuffle, randcase, randsequence and four more $urandom agree in %0d of 9; seeded 12 the first $urandom differs: %0d",
             untouched_by_objects, changed_by_seed);

    fork
      begin
        process quiet = process::self();
        quiet.srandom(5);
      end
      begin
        process m = process::self();
        m.srandom(3);
        draw_five();
        u1 = u; r1 = r; f1 = f; c1 = c; q1 = q;
        for (int j = 0; j < 4; j++) t1[j] = $urandom;
      end
    join
    fork
      begin
        process noisy = process::self();
        noisy.srandom(5);
        for (int j = 0; j < 100; j++) busy[j] = $urandom;
        draw_five();
      end
      begin
        process m = process::self();
        m.srandom(3);
        draw_five();
        u2 = u; r2 = r; f2 = f; c2 = c; q2 = q;
        for (int j = 0; j < 4; j++) t2[j] = $urandom;
      end
    join
    untouched_by_thread = 0;
    if (u1 == u2) untouched_by_thread++;
    if (r1 == r2) untouched_by_thread++;
    if (f1 == f2) untouched_by_thread++;
    if (c1 == c2) untouched_by_thread++;
    if (q1 == q2) untouched_by_thread++;
    for (i = 0; i < 4; i++) if (t1[i] == t2[i]) untouched_by_thread++;
    $display("thread: a forked thread seeded 3 beside a quiet thread and beside one drawing a hundred agrees in %0d of 9",
             untouched_by_thread);

    a.srandom(7);
    for (i = 0; i < 4; i++) begin k = a.randomize(); s1[i] = a.payload; end
    a.srandom(7);
    for (i = 0; i < 8; i++) k = b.randomize();
    for (i = 0; i < 8; i++) k = $urandom;
    draw_five();
    for (i = 0; i < 4; i++) begin k = a.randomize(); s2[i] = a.payload; end
    untouched_by_draws = 0;
    for (i = 0; i < 4; i++) if (s1[i] == s2[i]) untouched_by_draws++;
    a.srandom(8);
    for (i = 0; i < 4; i++) begin k = a.randomize(); s3[i] = a.payload; end
    changed_by_object_seed = 0;
    for (i = 0; i < 4; i++) if (s1[i] != s3[i]) changed_by_object_seed = 1;
    $display("object: seeded 7 and randomized between draws of the thread and of another object, four randomize agree in %0d of 4; seeded 8 they differ: %0d",
             untouched_by_draws, changed_by_object_seed);
    $finish;
  end
endmodule
