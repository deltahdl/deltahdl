class CA;
  rand byte x, y;
  byte v, w;
  constraint c1 { x < v && y > w; }
endclass

class Cyclic;
  randc bit [1:0] k;
  bit flag;
endclass

class Vault;
  local rand byte secret;
  byte lid;
  constraint lidded { secret > lid; }
  function int draw_secret();
    return randomize(secret);
  endfunction
  function byte peek();
    return secret;
  endfunction
endclass

module inline_random_variable_control;
  CA a;
  Cyclic cy;
  Vault vault;
  int i, ok, moved, rounds, repeated, above;
  byte prev, k0, k1, k2, k3;
  bit prev_flag;

  initial begin
    a = new;
    a.v = 100;
    a.w = -100;
    ok = 0;
    for (i = 0; i < 32; i++) begin
      void'(a.randomize());
      if (a.x < 100 && a.y > -100 && a.v == 100 && a.w == -100) ok++;
    end
    $display("no arguments: x, y random and v, w state in %0d of 32", ok);

    a.y = 50;
    ok = 0;
    for (i = 0; i < 32; i++) begin
      void'(a.randomize(x));
      if (a.x < 100 && a.y == 50 && a.v == 100 && a.w == -100) ok++;
    end
    $display("x alone: x random, y held at 50 in %0d of 32", ok);

    a.x = -50;
    a.y = 50;
    ok = 0;
    moved = 0;
    prev = a.v;
    for (i = 0; i < 32; i++) begin
      void'(a.randomize(v, w));
      if (a.v > -50 && a.w < 50 && a.x == -50 && a.y == 50) ok++;
      if (a.v != prev) moved++;
      prev = a.v;
    end
    $display("v and w: v, w random and x, y held in %0d of 32, v moved in some: %0d",
             ok, moved > 0);

    a.v = 100;
    a.y = 50;
    ok = 0;
    for (i = 0; i < 32; i++) begin
      void'(a.randomize(w, x));
      if (a.x < 100 && a.w < 50 && a.y == 50 && a.v == 100) ok++;
    end
    $display("w and x: w, x random and y, v held in %0d of 32", ok);

    cy = new;
    rounds = 0;
    for (i = 0; i < 4; i++) begin
      void'(cy.randomize(k)); k0 = cy.k;
      void'(cy.randomize(k)); k1 = cy.k;
      void'(cy.randomize(k)); k2 = cy.k;
      void'(cy.randomize(k)); k3 = cy.k;
      if (k0 != k1 && k0 != k2 && k0 != k3 && k1 != k2 && k1 != k3 && k2 != k3)
        rounds++;
    end
    repeated = 0;
    void'(cy.randomize(flag));
    prev_flag = cy.flag;
    for (i = 0; i < 40; i++) begin
      void'(cy.randomize(flag));
      if (cy.flag == prev_flag) repeated++;
      prev_flag = cy.flag;
    end
    $display("cyclic: named randc draws all four in %0d of 4 rounds, named bit repeats in some of 40: %0d",
             rounds, repeated > 0);

    vault = new;
    vault.lid = 100;
    ok = 0;
    above = 0;
    for (i = 0; i < 32; i++) begin
      ok += vault.draw_secret();
      if (vault.peek() > 100) above++;
    end
    $display("local member: named within the class in %0d of 32, secret above the lid in %0d", ok, above);
    $finish;
  end
endmodule
