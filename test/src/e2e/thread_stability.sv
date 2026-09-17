// IEEE 1800-2023 §18.14.2: the values $urandom and $urandom_range return, the
// scope randomize() and shuffle() draw, and the branches randcase and
// randsequence select, are independent of thread execution order. The
// clause's fork of three threads -- one seeding itself with 100 before
// drawing x, one drawing y before seeding itself with 200, one drawing z as
// the sum of two values -- shows thread locality, x, y and z being
// independent of the order the threads run in, and hierarchical seeding, each
// thread's random state being initialized with the next random value of the
// parent thread as a seed. So the fork run again with its threads delayed
// into another order returns the same x, y and z; x is the first value of a
// thread seeded with 100, and y and z are what threads seeded by hand with
// the parent's second and third next values return. And the root of a thread
// execution subtree determines the seeding of its children, so a subtree
// whose root seeds itself draws alike from wherever in the parent it is
// forked.
module thread_stability;
  process p;
  integer x, y, z, x2, y2, z2, x100;
  int unsigned s1, s2, s3, a1, a2, a3, a4, b1, b2, b3, b4;
  int i, k, locality, first_of_100, seeded_by_hand, subtree_moved;

  initial begin
    p = process::self();
    p.srandom(5);
    fork
      begin
        process pvar;
        pvar = process::self();
        pvar.srandom(100);
        x = $urandom;
      end
      begin
        process pvar;
        pvar = process::self();
        y = $urandom;
        pvar.srandom(200);
      end
      begin
        z = $urandom + $urandom;
      end
    join
    p.srandom(5);
    fork
      begin
        process pvar;
        pvar = process::self();
        pvar.srandom(100);
        #2 x2 = $urandom;
      end
      begin
        process pvar;
        pvar = process::self();
        #1 y2 = $urandom;
        pvar.srandom(200);
      end
      begin
        z2 = $urandom + $urandom;
      end
    join
    locality = 0;
    if (x == x2) locality++;
    if (y == y2) locality++;
    if (z == z2) locality++;
    $display("locality: x, y and z of the clause's fork agree with the fork run with its threads delayed into another order in %0d of 3",
             locality);

    p.srandom(100);
    x100 = $urandom;
    first_of_100 = x == x100;
    p.srandom(5);
    s1 = $urandom;
    s2 = $urandom;
    s3 = $urandom;
    fork
      begin
        process q;
        q = process::self();
        q.srandom(s2);
        y2 = $urandom;
      end
      begin
        process q;
        q = process::self();
        q.srandom(s3);
        z2 = $urandom + $urandom;
      end
    join
    seeded_by_hand = 0;
    if (y == y2) seeded_by_hand++;
    if (z == z2) seeded_by_hand++;
    $display("seeding: x is the first value of a thread seeded with 100: %0d, y and z agree with threads seeded by hand with the parent's second and third next values in %0d of 2",
             first_of_100, seeded_by_hand);

    p.srandom(5);
    fork
      begin
        process r;
        r = process::self();
        r.srandom(77);
        fork
          a1 = $urandom;
          a2 = $urandom_range(100);
          a3 = $urandom;
        join
        a4 = $urandom;
      end
    join
    for (i = 0; i < 7; i++) k = $urandom;
    fork
      begin
        process r;
        r = process::self();
        r.srandom(77);
        fork
          b1 = $urandom;
          b2 = $urandom_range(100);
          b3 = $urandom;
        join
        b4 = $urandom;
      end
    join
    subtree_moved = 0;
    if (a1 == b1) subtree_moved++;
    if (a2 == b2) subtree_moved++;
    if (a3 == b3) subtree_moved++;
    if (a4 == b4) subtree_moved++;
    $display("subtree: a subtree whose root seeds itself with 77 draws alike from two places of the parent in %0d of 4",
             subtree_moved);
    $finish;
  end
endmodule
