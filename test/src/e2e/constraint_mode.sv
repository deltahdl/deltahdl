// 18.9: controlling constraints with constraint_mode(): a block turned off
// is not considered by randomize(), all blocks are initially active, the
// call on the object alone applies to all of its blocks, the nonvoid form
// reports the state, and the clause's toggle_rand flips filter1 before
// each call.
class Packet;
  rand integer source_value;
  integer m = 100;
  constraint filter1 { source_value > 2 * m; }
  constraint ceiling { source_value < 1000; }
endclass

module constraint_mode;
  Packet p;
  integer toggled, i, above, wide;

  // The clause's toggle_rand: filter1 off where it was on and on where it
  // was off, then a new source_value.
  function integer toggle_rand(Packet p);
    if (p.filter1.constraint_mode())
      p.filter1.constraint_mode(0);
    else
      p.filter1.constraint_mode(1);
    toggle_rand = p.randomize();
  endfunction

  initial begin
    p = new;
    // All constraints are initially active.
    $display("initially: filter1 %0d, ceiling %0d", p.filter1.constraint_mode(),
             p.ceiling.constraint_mode());

    // Toggled from on, filter1 is off for the call, so over 32 calls
    // source_value is drawn below 1000 alone and falls at or below 200 in
    // some.
    above = 0;
    wide = 0;
    for (i = 0; i < 32; i++) begin
      p.filter1.constraint_mode(1);
      toggled = toggle_rand(p);
      if (p.source_value > 200 && p.source_value < 1000) above++;
      if (p.source_value <= 200) wide++;
    end
    $display("filter1 off: filter1 %0d, source_value between 200 and 1000 in %0d of 32, at or below 200 in some: %0d",
             p.filter1.constraint_mode(), above, wide > 0);

    // Toggled from off, filter1 is on for the call, so every call draws
    // source_value above 200 below 1000.
    above = 0;
    for (i = 0; i < 32; i++) begin
      p.filter1.constraint_mode(0);
      toggled = toggle_rand(p);
      if (p.source_value > 200 && p.source_value < 1000) above++;
    end
    $display("filter1 on: filter1 %0d, source_value between 200 and 1000 in %0d of 32",
             p.filter1.constraint_mode(), above);

    // The call on the object turns every block off: source_value ranges
    // over the whole integer, above 1000 or at or below 200 in some.
    p.constraint_mode(0);
    wide = 0;
    for (i = 0; i < 32; i++) begin
      void'(p.randomize());
      if (p.source_value >= 1000 || p.source_value <= 200) wide++;
    end
    $display("all off: filter1 %0d, ceiling %0d, source_value outside both in some: %0d",
             p.filter1.constraint_mode(), p.ceiling.constraint_mode(), wide > 0);
    $finish;
  end
endmodule
