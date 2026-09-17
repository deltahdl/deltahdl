// 18.6.2: pre_randomize() and post_randomize(), which every class contains
// and randomize() calls before and after computing the new values, on the
// object and on its enabled random object members; a derived class without
// its own invokes the base's, one overriding them calls the base's through
// super or skips the base's steps, and through randomize() they appear
// virtual.
class Leaf;
  rand bit [7:0] v;
  int pre_calls = 0;
  int post_calls = 0;
  function void pre_randomize();
    pre_calls++;
  endfunction
  function void post_randomize();
    post_calls++;
  endfunction
endclass

class Base;
  rand bit [7:0] x;
  rand Leaf leaf;
  int step = 0;
  int pre_step = 0;
  int post_step = 0;
  int pre_x = 0;
  int post_x = 0;
  int base_pre = 0;
  int base_post = 0;
  function void pre_randomize();
    step++;
    pre_step = step;
    pre_x = x;
    base_pre++;
  endfunction
  function void post_randomize();
    step++;
    post_step = step;
    post_x = x;
    base_post++;
  endfunction
endclass

// No override: the base's methods are invoked.
class Inherits extends Base;
endclass

// Overrides calling the base's through super: both steps run.
class Chains extends Base;
  int own_pre = 0;
  int own_post = 0;
  function void pre_randomize();
    super.pre_randomize();
    own_pre++;
  endfunction
  function void post_randomize();
    super.post_randomize();
    own_post++;
  endfunction
endclass

// Overrides not calling the base's: the base's steps are skipped.
class Skips extends Base;
  int own_pre = 0;
  int own_post = 0;
  function void pre_randomize();
    own_pre++;
  endfunction
  function void post_randomize();
    own_post++;
  endfunction
endclass

module pre_post_randomize;
  Base b, handle;
  Inherits inh;
  Chains ch;
  Skips sk;
  int ok;

  initial begin
    // pre_randomize() runs before the new values are computed, seeing x as
    // it was, and post_randomize() after, seeing the new x; the enabled
    // random object member's methods run as well.
    b = new;
    b.leaf = new;
    b.x = 200;
    ok = b.randomize() with { x < 100; };
    $display("Base: solved %0d, pre at step %0d saw x %0d, post at step %0d saw the new x: %0d, leaf pre %0d post %0d",
             ok, b.pre_step, b.pre_x, b.post_step, b.post_x == b.x && b.x < 100,
             b.leaf.pre_calls, b.leaf.post_calls);

    // A random object member made inactive is not one of the enabled
    // members: its methods are not called.
    b.leaf.rand_mode(0);
    ok = b.randomize();
    $display("leaf inactive: solved %0d, leaf pre %0d post %0d", ok,
             b.leaf.pre_calls, b.leaf.post_calls);

    // A derived class with no implementation of its own invokes the base's.
    inh = new;
    ok = inh.randomize();
    $display("Inherits: solved %0d, base pre %0d post %0d", ok, inh.base_pre,
             inh.base_post);

    // An override calling super runs the base's step and its own; one not
    // calling super skips the base's.
    ch = new;
    ok = ch.randomize();
    $display("Chains: solved %0d, base pre %0d post %0d, own pre %0d post %0d",
             ok, ch.base_pre, ch.base_post, ch.own_pre, ch.own_post);
    sk = new;
    ok = sk.randomize();
    $display("Skips: solved %0d, base pre %0d post %0d, own pre %0d post %0d",
             ok, sk.base_pre, sk.base_post, sk.own_pre, sk.own_post);

    // Through a Base handle the Skips' own methods run: called by the
    // virtual randomize(), they behave as virtual.
    handle = sk;
    ok = handle.randomize();
    $display("Skips through a Base handle: solved %0d, base pre %0d post %0d, own pre %0d post %0d",
             ok, sk.base_pre, sk.base_post, sk.own_pre, sk.own_post);
    $finish;
  end
endmodule
