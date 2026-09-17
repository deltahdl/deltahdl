// IEEE 1800-2023 §18.13.3: srandom(int seed) seeds an object's RNG with the
// given seed, and the RNG associated with a process is seeded with the
// srandom() method of the process (§9.7). An object's RNG is its own
// (§18.14), so seeding an object and drawing from it leaves the process's
// sequence untouched, and two objects seeded alike draw alike.
module srandom_method;
  class Packet;
    rand bit [15:0] payload;
    rand bit [3:0] kind;
  endclass

  Packet a, b;
  process p;
  int i, k;
  bit [19:0] seq_a[4], seq_b[4], seq_c[4];
  int unsigned u_a[4], u_b[4];
  int replayed, by_expression, diverged, alike;
  int proc_replayed, proc_diverged, untouched;

  initial begin
    a = new;
    b = new;
    // The same seed on the same object replays its draws; an expression of
    // equal value is the same seed; another seed selects another sequence.
    a.srandom(7);
    for (i = 0; i < 4; i++) begin k = a.randomize(); seq_a[i] = {a.kind, a.payload}; end
    a.srandom(7);
    for (i = 0; i < 4; i++) begin k = a.randomize(); seq_b[i] = {a.kind, a.payload}; end
    replayed = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_b[i]) replayed++;
    a.srandom(3 + 4);
    for (i = 0; i < 4; i++) begin k = a.randomize(); seq_b[i] = {a.kind, a.payload}; end
    by_expression = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_b[i]) by_expression++;
    a.srandom(8);
    for (i = 0; i < 4; i++) begin k = a.randomize(); seq_b[i] = {a.kind, a.payload}; end
    diverged = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] != seq_b[i]) diverged = 1;
    // Two objects seeded alike draw alike.
    b.srandom(7);
    for (i = 0; i < 4; i++) begin k = b.randomize(); seq_c[i] = {b.kind, b.payload}; end
    alike = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_c[i]) alike++;
    $display("object: replayed by 7 in %0d of 4, by 3 + 4 in %0d, changed by 8: %0d, a second object seeded 7 agrees in %0d",
             replayed, by_expression, diverged, alike);

    // The process's own RNG, seeded through the process; an object seeded
    // and drawn from in between leaves the process's sequence as it was.
    p = process::self();
    p.srandom(55);
    for (i = 0; i < 4; i++) u_a[i] = $urandom;
    p.srandom(55);
    a.srandom(9);
    for (i = 0; i < 4; i++) k = a.randomize();
    for (i = 0; i < 4; i++) u_b[i] = $urandom;
    proc_replayed = 0;
    for (i = 0; i < 4; i++) if (u_a[i] == u_b[i]) proc_replayed++;
    p.srandom(56);
    for (i = 0; i < 4; i++) u_b[i] = $urandom;
    proc_diverged = 0;
    for (i = 0; i < 4; i++) if (u_a[i] != u_b[i]) proc_diverged = 1;
    $display("process: replayed by 55 in %0d of 4 with an object seeded and drawn between, changed by 56: %0d",
             proc_replayed, proc_diverged);
    $finish;
  end
endmodule
