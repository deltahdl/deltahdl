// IEEE 1800-2023 §18.13.1: $urandom returns a new unsigned 32-bit random
// number on each call. Its optional seed, any integral expression, selects
// the sequence, and the same seed yields the same sequence every time; the
// generator is deterministic, so the sequence a program cycles through is the
// same on each execution. The clause's example seeds it once into a
// bit-select, concatenates two calls into a 64-bit value and masks one call
// to four bits.
module urandom_function;
  parameter int SEED = 254;
  bit [64:1] addr;
  bit [3:0] number;
  logic [63:0] wide;
  int unsigned seq_a[8];
  int unsigned seq_b[8];
  int i, replayed, by_expression, by_variable, diverged, advanced;
  int high_seen, upper_zero, upper_seen, low_number;
  int seed_var;
  int unsigned r, prev;

  initial begin
    // The same seed replays the sequence; the seed may be a literal, a
    // parameter, an expression or a variable of equal value.
    seq_a[0] = $urandom(254);
    for (i = 1; i < 8; i++) seq_a[i] = $urandom;
    seq_b[0] = $urandom(SEED);
    for (i = 1; i < 8; i++) seq_b[i] = $urandom;
    replayed = 0;
    for (i = 0; i < 8; i++) if (seq_a[i] == seq_b[i]) replayed++;
    seq_b[0] = $urandom(250 + 4);
    for (i = 1; i < 8; i++) seq_b[i] = $urandom;
    by_expression = 0;
    for (i = 0; i < 8; i++) if (seq_a[i] == seq_b[i]) by_expression++;
    seed_var = 254;
    seq_b[0] = $urandom(seed_var);
    for (i = 1; i < 8; i++) seq_b[i] = $urandom;
    by_variable = 0;
    for (i = 0; i < 8; i++) if (seq_a[i] == seq_b[i]) by_variable++;
    // A different seed selects a different sequence.
    seq_b[0] = $urandom(255);
    for (i = 1; i < 8; i++) seq_b[i] = $urandom;
    diverged = 0;
    for (i = 0; i < 8; i++) if (seq_a[i] != seq_b[i]) diverged = 1;
    $display("seeded: replayed by 254 in %0d of 8, by 250 + 4 in %0d, by a variable in %0d, changed by 255: %0d",
             replayed, by_expression, by_variable, diverged);

    // Each call returns a new number; it is unsigned and 32 bits wide, so an
    // assignment to a 64-bit variable zero-extends it whatever its top bit.
    advanced = 0;
    high_seen = 0;
    upper_zero = 0;
    prev = $urandom;
    for (i = 0; i < 32; i++) begin
      r = $urandom;
      if (r != prev) advanced++;
      prev = r;
      wide = $urandom;
      if (wide[63:32] == 0) upper_zero++;
      if (wide[31]) high_seen = 1;
    end
    $display("unsigned 32-bit: a new number in %0d of 32 calls, upper 32 bits zero in %0d of 32, top bit seen: %0d",
             advanced, upper_zero, high_seen);

    // The clause's example.
    addr[32:1] = $urandom(254);
    upper_seen = 0;
    low_number = 0;
    for (i = 0; i < 32; i++) begin
      addr = {$urandom, $urandom};
      number = $urandom & 15;
      if (addr[64:33] != 0) upper_seen = 1;
      if (number < 16) low_number++;
    end
    $display("the example: upper half of addr seen: %0d, number below 16 in %0d of 32",
             upper_seen, low_number);
    $finish;
  end
endmodule
