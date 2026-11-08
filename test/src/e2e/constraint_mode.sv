class Packet;
  rand integer source_value;
  integer m = 100;
  constraint filter1 { source_value > 2 * m; }
  constraint ceiling { source_value < 1000; }
endclass

module constraint_mode;
  Packet p;
  integer toggled, i, above, wide;

  function integer toggle_rand(Packet p);
    if (p.filter1.constraint_mode())
      p.filter1.constraint_mode(0);
    else
      p.filter1.constraint_mode(1);
    toggle_rand = p.randomize();
  endfunction

  initial begin
    p = new;
    $display("initially: filter1 %0d, ceiling %0d", p.filter1.constraint_mode(),
             p.ceiling.constraint_mode());

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

    above = 0;
    for (i = 0; i < 32; i++) begin
      p.filter1.constraint_mode(0);
      toggled = toggle_rand(p);
      if (p.source_value > 200 && p.source_value < 1000) above++;
    end
    $display("filter1 on: filter1 %0d, source_value between 200 and 1000 in %0d of 32",
             p.filter1.constraint_mode(), above);

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
