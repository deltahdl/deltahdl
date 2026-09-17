// 18.6.1: randomize(), the built-in virtual method every class has, which
// generates random values for all the active random variables of the object
// subject to its active constraints and returns 1 where it set them all to
// valid values and 0 otherwise.
class Packet;
  rand bit [7:0] kind;
  rand bit [7:0] size;
  constraint bounded { size < 64; }
endclass

// A derived packet adding a constraint over the base's variable, reached
// through a base handle: the virtual randomize() applies the constraints
// of the object's own class.
class Framed extends Packet;
  constraint even { size[0] == 0; }
endclass

// A derived packet whose constraint contradicts the base's, rendering a
// seemingly simple constraint set unsatisfiable.
class Oversized extends Packet;
  constraint large { size > 100; }
endclass

module randomize_method;
  Packet p, handle;
  Framed fr;
  Oversized ov;
  int success, held, evens, varied, kept, i, first_kind;

  initial begin
    // The plain call: every active random variable is set subject to the
    // active constraints, and the method returns 1.
    p = new;
    success = 0;
    held = 0;
    varied = 0;
    first_kind = -1;
    for (i = 0; i < 64; i++) begin
      if (p.randomize() == 1) success++;
      if (p.size < 64) held++;
      if (first_kind < 0) first_kind = p.kind;
      else if (p.kind != first_kind) varied = 1;
    end
    $display("Packet: success %0d of 64, size below 64 in %0d, kind varies: %0d",
             success, held, varied);

    // The virtual method through a base handle: the Framed's even holds
    // beside the base's bounded on every draw.
    fr = new;
    handle = fr;
    success = 0;
    held = 0;
    evens = 0;
    for (i = 0; i < 64; i++) begin
      if (handle.randomize()) success++;
      if (fr.size < 64) held++;
      if (fr.size[0] == 0) evens++;
    end
    $display("Framed through a Packet handle: success %0d of 64, size below 64 in %0d, even in %0d",
             success, held, evens);

    // An inactive random variable is not set: kind held at 7 by rand_mode(0)
    // keeps it across the draws while size is set.
    p.kind = 7;
    p.kind.rand_mode(0);
    kept = 0;
    success = 0;
    for (i = 0; i < 64; i++) begin
      if (p.randomize()) success++;
      if (p.kind == 7) kept++;
    end
    $display("kind inactive: success %0d of 64, kind kept at 7 in %0d", success,
             kept);

    // An inactive constraint block is not applied: with bounded turned off,
    // size reaches 64 and above in some draw.
    p.bounded.constraint_mode(0);
    held = 0;
    for (i = 0; i < 64; i++) begin
      void'(p.randomize());
      if (p.size >= 64) held++;
    end
    $display("bounded inactive: size at or above 64 in some: %0d", held > 0);

    // The constraints of a derived class can render the base's
    // unsatisfiable: the Oversized's call returns 0 and its size keeps the
    // value it had.
    ov = new;
    ov.size = 5;
    success = ov.randomize();
    $display("Oversized: randomize returns %0d, size kept: %0d", success,
             ov.size == 5);
    $finish;
  end
endmodule
