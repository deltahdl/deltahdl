// IEEE 1800-2023 §18.14.1: random stability has four properties. Each module
// instance has an initialization RNG seeded with the default seed, used to
// seed its static processes, each with the RNG's next value, and the objects
// its static declaration initializers create; so the first static process of
// two instances of one module draws alike, so does the object each creates,
// and two static processes of one instance differ. A new dynamic thread's RNG
// is seeded with the next random value of its parent thread (hierarchical
// seeding), so a thread seeded by hand with the value the parent would have
// drawn next draws as one the fork seeded, and threads added at the end of a
// fork leave the earlier ones agreeing. An object created with new is seeded
// with the next random value of the creating thread, so an object seeded by
// hand with that value draws as one new seeded, and objects created after it
// leave its draws agreeing. Every noninitialization RNG can be seeded by hand,
// and with hierarchical seeding one seed at the root thread defines the whole
// subtree, so the root seeded again replays two forked threads that each
// create and draw from an object.
// The instantiating module is written last, because a run that names no top
// module elaborates the last module of the source.
module stable_leaf;
  class Item;
    rand bit [15:0] payload;
  endclass
  Item sp = new;
  int unsigned first, second;
  bit [15:0] sp_payload;
  int k;
  initial first = $urandom;
  initial second = $urandom;
  initial begin k = sp.randomize(); sp_payload = sp.payload; end
endmodule

module random_stability_properties;
  class Packet;
    rand bit [15:0] payload;
  endclass

  stable_leaf u1();
  stable_leaf u2();

  Packet a, b, c, d;
  process p;
  int i, k;
  int unsigned seedv, c_auto[4], c_manual[4], f1, f2, g1, g2, g3, m1[4], m2[4];
  bit [15:0] s_auto[4], s_manual[4], a1, a2;
  int same_first, same_static_object, distinct, seeded_alike, added_after;
  int object_seeded_alike, created_after, subtree_replayed;

  initial begin
    #1;
    same_first = u1.first == u2.first;
    same_static_object = u1.sp_payload == u2.sp_payload;
    distinct = u1.first != u1.second;
    $display("initialization: the first static process of two instances draws alike: %0d, so does the object their declarations create: %0d, two static processes of one instance differ: %0d",
             same_first, same_static_object, distinct);

    p = process::self();
    p.srandom(21);
    fork
      begin
        for (int j = 0; j < 4; j++) c_auto[j] = $urandom;
      end
    join
    p.srandom(21);
    seedv = $urandom;
    fork
      begin
        process q = process::self();
        q.srandom(seedv);
        for (int j = 0; j < 4; j++) c_manual[j] = $urandom;
      end
    join
    seeded_alike = 0;
    for (i = 0; i < 4; i++) if (c_auto[i] == c_manual[i]) seeded_alike++;
    p.srandom(21);
    fork
      f1 = $urandom;
      f2 = $urandom;
    join
    p.srandom(21);
    fork
      g1 = $urandom;
      g2 = $urandom;
      g3 = $urandom;
    join
    added_after = 0;
    if (f1 == g1) added_after++;
    if (f2 == g2) added_after++;
    $display("thread: a forked thread seeded by hand with the parent's next value draws as one the fork seeded in %0d of 4, a thread added at the end of a fork leaves the earlier two agreeing in %0d of 2",
             seeded_alike, added_after);

    p.srandom(33);
    a = new;
    for (i = 0; i < 4; i++) begin k = a.randomize(); s_auto[i] = a.payload; end
    p.srandom(33);
    seedv = $urandom;
    b = new;
    b.srandom(seedv);
    for (i = 0; i < 4; i++) begin k = b.randomize(); s_manual[i] = b.payload; end
    object_seeded_alike = 0;
    for (i = 0; i < 4; i++) if (s_auto[i] == s_manual[i]) object_seeded_alike++;
    p.srandom(33);
    a = new;
    c = new;
    d = new;
    k = a.randomize();
    created_after = a.payload == s_auto[0];
    $display("object: an object seeded by hand with the thread's next value draws as one new seeded in %0d of 4, objects created after it leave its draw agreeing: %0d",
             object_seeded_alike, created_after);

    p.srandom(44);
    fork
      begin
        Packet o = new;
        k = o.randomize();
        m1[0] = o.payload;
        m1[1] = $urandom;
      end
      begin
        Packet o = new;
        k = o.randomize();
        m1[2] = o.payload;
        m1[3] = $urandom;
      end
    join
    p.srandom(44);
    fork
      begin
        Packet o = new;
        k = o.randomize();
        m2[0] = o.payload;
        m2[1] = $urandom;
      end
      begin
        Packet o = new;
        k = o.randomize();
        m2[2] = o.payload;
        m2[3] = $urandom;
      end
    join
    subtree_replayed = 0;
    for (i = 0; i < 4; i++) if (m1[i] == m2[i]) subtree_replayed++;
    $display("manual: the root thread seeded with 44 again replays two forked threads each creating and drawing from an object in %0d of 4",
             subtree_replayed);
    $finish;
  end
endmodule
