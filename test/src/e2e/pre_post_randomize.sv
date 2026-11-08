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

class Inherits extends Base;
endclass

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
    b = new;
    b.leaf = new;
    b.x = 200;
    ok = b.randomize() with { x < 100; };
    $display("Base: solved %0d, pre at step %0d saw x %0d, post at step %0d saw the new x: %0d, leaf pre %0d post %0d",
             ok, b.pre_step, b.pre_x, b.post_step, b.post_x == b.x && b.x < 100,
             b.leaf.pre_calls, b.leaf.post_calls);

    b.leaf.rand_mode(0);
    ok = b.randomize();
    $display("leaf inactive: solved %0d, leaf pre %0d post %0d", ok,
             b.leaf.pre_calls, b.leaf.post_calls);

    inh = new;
    ok = inh.randomize();
    $display("Inherits: solved %0d, base pre %0d post %0d", ok, inh.base_pre,
             inh.base_post);

    ch = new;
    ok = ch.randomize();
    $display("Chains: solved %0d, base pre %0d post %0d, own pre %0d post %0d",
             ok, ch.base_pre, ch.base_post, ch.own_pre, ch.own_post);
    sk = new;
    ok = sk.randomize();
    $display("Skips: solved %0d, base pre %0d post %0d, own pre %0d post %0d",
             ok, sk.base_pre, sk.base_post, sk.own_pre, sk.own_post);

    handle = sk;
    ok = handle.randomize();
    $display("Skips through a Base handle: solved %0d, base pre %0d post %0d, own pre %0d post %0d",
             ok, sk.base_pre, sk.base_post, sk.own_pre, sk.own_post);
    $finish;
  end
endmodule
