// 18.11: inline random variable control: randomize() called with no
// arguments assigns every rand and randc variable, and called with
// arguments those arguments are the complete set of random variables for
// the call, every other variable of the object a state variable, as if
// rand_mode() had enabled the named and disabled the rest. Naming a
// property not declared rand makes it random for the call; the cyclical
// mode is not changed either way. The arguments are properties of the
// calling object, and a local member can be named where the call has
// access to it, within its class.
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
    // No arguments: x and y are random, v and w state, the constraint
    // holding on every draw.
    a.v = 100;
    a.w = -100;
    ok = 0;
    for (i = 0; i < 32; i++) begin
      void'(a.randomize());
      if (a.x < 100 && a.y > -100 && a.v == 100 && a.w == -100) ok++;
    end
    $display("no arguments: x, y random and v, w state in %0d of 32", ok);

    // x alone: y is a state variable and keeps 50.
    a.y = 50;
    ok = 0;
    for (i = 0; i < 32; i++) begin
      void'(a.randomize(x));
      if (a.x < 100 && a.y == 50 && a.v == 100 && a.w == -100) ok++;
    end
    $display("x alone: x random, y held at 50 in %0d of 32", ok);

    // v and w: the properties not declared rand are random for the call
    // and the rand x and y are state, so v is drawn above x and w below
    // y, and v moves between calls.
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

    // w and x: one of each kind named, y and v held.
    a.v = 100;
    a.y = 50;
    ok = 0;
    for (i = 0; i < 32; i++) begin
      void'(a.randomize(w, x));
      if (a.x < 100 && a.w < 50 && a.y == 50 && a.v == 100) ok++;
    end
    $display("w and x: w, x random and y, v held in %0d of 32", ok);

    // The cyclical mode is not changed: a named randc still draws each of
    // its four values once per round, and a named nonrandom bit is not
    // cyclical, repeating consecutively in some of 40 calls.
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

    // A local member is named where the call has access to it, within the
    // class: draw_secret() succeeds and the secret lies above the lid.
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
