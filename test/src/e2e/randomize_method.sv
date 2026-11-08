class Packet;
  rand bit [7:0] kind;
  rand bit [7:0] size;
  constraint bounded { size < 64; }
endclass

class Framed extends Packet;
  constraint even { size[0] == 0; }
endclass

class Oversized extends Packet;
  constraint oversize { size > 100; }
endclass

module randomize_method;
  Packet p, handle;
  Framed fr;
  Oversized ov;
  int success, held, evens, varied, kept, i, first_kind;

  initial begin
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

    p.bounded.constraint_mode(0);
    held = 0;
    for (i = 0; i < 64; i++) begin
      void'(p.randomize());
      if (p.size >= 64) held++;
    end
    $display("bounded inactive: size at or above 64 in some: %0d", held > 0);

    ov = new;
    ov.size = 5;
    success = ov.randomize();
    $display("Oversized: randomize returns %0d, size kept: %0d", success,
             ov.size == 5);
    $finish;
  end
endmodule
