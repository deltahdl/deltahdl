// IEEE 1800-2023 §18.13: the random number system functions and methods.
// §18.13.1 $urandom returns a new unsigned 32-bit number on each call and the
// same sequence for the same seed; §18.13.2 $urandom_range returns an unsigned
// integer within maxval ... minval, minval defaulting to 0 and reversed
// arguments being swapped; §18.13.3 srandom seeds the RNG of an object or of a
// process; §18.13.4 get_randstate retrieves that RNG's state as a string and
// §18.13.5 set_randstate installs it again.
module random_number_functions;
  class Packet;
    rand bit [15:0] payload;
  endclass

  bit [64:1] addr;
  bit [3:0] number;
  int unsigned seq_a[4];
  int unsigned seq_b[4];
  bit [15:0] pay_a[4];
  bit [15:0] pay_b[4];
  int i, k, replayed, high_seen, upper_seen, low_number;
  int in_range, in_range_omitted, in_range_reversed, zero_seen, seven_seen;
  int obj_seeded, proc_seeded, obj_state, proc_state;
  int unsigned r;
  Packet pkt;
  process p;
  string st;

  initial begin
    // §18.13.1: the same seed yields the same sequence.
    seq_a[0] = $urandom(254);
    for (i = 1; i < 4; i++) seq_a[i] = $urandom;
    seq_b[0] = $urandom(254);
    for (i = 1; i < 4; i++) seq_b[i] = $urandom;
    replayed = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_b[i]) replayed++;

    // §18.13.1: the clause's example seeds the generator once, then takes a
    // 64-bit value from two calls and a 4-bit one from a masked call. The
    // number is unsigned and 32 bits wide, so over 32 further unseeded draws
    // its top bit is set in some and the upper half of the concatenation is
    // nonzero in some; a seed inside the loop would replay one value instead.
    addr[32:1] = $urandom(254);
    high_seen = 0;
    upper_seen = 0;
    low_number = 0;
    for (i = 0; i < 32; i++) begin
      r = $urandom;
      if (r >= 32'h8000_0000) high_seen = 1;
      addr = {$urandom, $urandom};
      number = $urandom & 15;
      if (addr[64:33] != 0) upper_seen = 1;
      if (number < 16) low_number++;
    end
    $display("$urandom: replayed by its seed in %0d of 4, top bit seen: %0d, upper half of addr seen: %0d, number below 16 in %0d of 32",
             replayed, high_seen, upper_seen, low_number);

    // §18.13.2: within maxval ... minval, with minval omitted, and reversed.
    in_range = 0;
    in_range_omitted = 0;
    in_range_reversed = 0;
    zero_seen = 0;
    seven_seen = 0;
    for (i = 0; i < 256; i++) begin
      r = $urandom_range(7, 0);
      if (r <= 7) in_range++;
      if (r == 0) zero_seen = 1;
      if (r == 7) seven_seen = 1;
      r = $urandom_range(7);
      if (r <= 7) in_range_omitted++;
      r = $urandom_range(0, 7);
      if (r <= 7) in_range_reversed++;
    end
    $display("$urandom_range: within 0..7 in %0d, %0d and %0d of 256, both ends drawn: %0d",
             in_range, in_range_omitted, in_range_reversed, zero_seen & seven_seen);

    // §18.13.3: srandom seeds an object's RNG and a process's RNG.
    pkt = new;
    pkt.srandom(7);
    for (i = 0; i < 4; i++) begin
      k = pkt.randomize();
      pay_a[i] = pkt.payload;
    end
    pkt.srandom(7);
    for (i = 0; i < 4; i++) begin
      k = pkt.randomize();
      pay_b[i] = pkt.payload;
    end
    obj_seeded = 0;
    for (i = 0; i < 4; i++) if (pay_a[i] == pay_b[i]) obj_seeded++;
    p = process::self();
    p.srandom(55);
    for (i = 0; i < 4; i++) seq_a[i] = $urandom;
    p.srandom(55);
    for (i = 0; i < 4; i++) seq_b[i] = $urandom;
    proc_seeded = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_b[i]) proc_seeded++;
    $display("srandom: the object replays %0d of 4, the process replays %0d of 4",
             obj_seeded, proc_seeded);

    // §18.13.4 and §18.13.5: a state retrieved and set again replays.
    st = pkt.get_randstate();
    for (i = 0; i < 4; i++) begin
      k = pkt.randomize();
      pay_a[i] = pkt.payload;
    end
    pkt.set_randstate(st);
    for (i = 0; i < 4; i++) begin
      k = pkt.randomize();
      pay_b[i] = pkt.payload;
    end
    obj_state = 0;
    for (i = 0; i < 4; i++) if (pay_a[i] == pay_b[i]) obj_state++;
    st = p.get_randstate();
    for (i = 0; i < 4; i++) seq_a[i] = $urandom;
    p.set_randstate(st);
    for (i = 0; i < 4; i++) seq_b[i] = $urandom;
    proc_state = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_b[i]) proc_state++;
    $display("randstate: the object replays %0d of 4, the process replays %0d of 4",
             obj_state, proc_state);
    $finish;
  end
endmodule
