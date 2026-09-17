// 18.5.13: soft constraints, the clause's Packet whose default size and
// mode are preferences the solver discards where a hard constraint
// contradicts them, beside the same size as a hard constraint, which fails
// the call instead, and a preference that a discarded soft constraint has
// no effect on the distribution.
class Packet;
  rand bit mode;
  rand int length;
  constraint deflt {
    soft length inside {32, 1024};
    soft mode -> length == 1024;
  }
endclass

// The clause's size constraint not defined as soft.
class Strict;
  rand bit mode;
  rand int length;
  constraint sizes { length inside {32, 1024}; }
endclass

class Preferred;
  rand bit [3:0] v;
  constraint pref { soft v == 3; }
endclass

module soft_constraints;
  Packet p;
  Strict s;
  Preferred q;
  int ok, legal, implied, zeros, ones, narrow, held, distinct, i, j;
  bit [15:0] seen;

  initial begin
    // Absent any other constraint both preferences hold: every packet is of
    // a legal size, a packet in mode 1 is of length 1024, and the draws
    // range over the legal combinations, both modes and the size 32 among
    // them.
    p = new;
    ok = 0;
    legal = 0;
    implied = 0;
    zeros = 0;
    ones = 0;
    narrow = 0;
    for (i = 0; i < 64; i++) begin
      if (p.randomize()) ok++;
      if (p.length == 32 || p.length == 1024) legal++;
      if (!p.mode || p.length == 1024) implied++;
      if (p.mode) ones++;
      else zeros++;
      if (p.length == 32) narrow++;
    end
    $display("default packets: solved %0d of 64, legal %0d, mode 1 at 1024 in %0d, both modes drawn: %0d, 32 drawn: %0d",
             ok, legal, implied, (zeros > 0) && (ones > 0), narrow > 0);

    // The clause's first call: length == 1512 contradicts the soft size,
    // which is discarded, while the soft implication still holds, so mode
    // randomizes to 0.
    ok = 0;
    zeros = 0;
    held = 0;
    for (i = 0; i < 64; i++) begin
      if (p.randomize() with { length == 1512; }) ok++;
      if (p.length == 1512) held++;
      if (!p.mode) zeros++;
    end
    $display("length 1512: solved %0d of 64, length held in %0d, mode 0 in %0d",
             ok, held, zeros);

    // The clause's second call: mode == 1 contradicts the soft implication
    // as well, so both preferences are discarded and mode randomizes to 1.
    ok = 0;
    ones = 0;
    held = 0;
    for (i = 0; i < 64; i++) begin
      if (p.randomize() with { length == 1512; mode == 1; }) ok++;
      if (p.length == 1512) held++;
      if (p.mode) ones++;
    end
    $display("length 1512 and mode 1: solved %0d of 64, length held in %0d, mode 1 in %0d",
             ok, held, ones);

    // The size constraint not defined as soft: the call with length == 1512
    // fails, where the call without it solves.
    s = new;
    ok = s.randomize() with { length == 1512; };
    legal = s.randomize();
    $display("the hard size against 1512: randomize returns %0d, alone: %0d",
             ok, legal);

    // A soft constraint alone is honored, and a discarded one is replaced by
    // true: overridden by v != 3 it has no effect on the distribution, so
    // the draws spread over the other values.
    q = new;
    held = 0;
    for (i = 0; i < 64; i++) begin
      void'(q.randomize());
      if (q.v == 3) held++;
    end
    $display("the preference alone: v is 3 in %0d of 64", held);
    held = 0;
    seen = 0;
    for (i = 0; i < 64; i++) begin
      void'(q.randomize() with { v != 3; });
      if (q.v == 3) held++;
      seen = seen | (16'd1 << q.v);
    end
    distinct = 0;
    for (j = 0; j < 16; j++) if (seen[j]) distinct++;
    $display("the preference overridden: v is 3 in %0d of 64, distinct values at least 8: %0d",
             held, distinct >= 8);
    $finish;
  end
endmodule
