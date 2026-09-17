// 18.6: randomization methods, the built-in randomize() of the clause's
// SimpleSum, which generates values for the active random variables of an
// object subject to its active constraints and returns whether it set them
// all, and the pre_randomize() and post_randomize() it calls around them.
class SimpleSum;
  rand bit [7:0] x, y, z;
  constraint c { z == x + y; }
endclass

// A SimpleSum counting the calls made around its randomization, with a
// bound that a state variable can make infeasible.
class Counted extends SimpleSum;
  int floor = 0;
  int pre_calls = 0;
  int post_calls = 0;
  constraint bounded { z >= floor; }
  function void pre_randomize();
    pre_calls++;
  endfunction
  function void post_randomize();
    post_calls++;
  endfunction
endclass

module randomization_methods;
  SimpleSum p;
  Counted q;
  int success, held, varied, i, sum, first_x, kept_x, kept_z;

  initial begin
    // The clause's call: randomize() sets x, y and z to values that satisfy
    // z == x + y at the width of the variables, returning 1, and the values
    // differ across calls.
    p = new;
    success = 0;
    held = 0;
    varied = 0;
    first_x = -1;
    for (i = 0; i < 64; i++) begin
      if (p.randomize() == 1) success++;
      sum = (p.x + p.y) & 255;
      if (p.z == sum) held++;
      if (first_x < 0) first_x = p.x;
      else if (p.x != first_x) varied = 1;
    end
    $display("SimpleSum: success %0d of 64, z is x + y in %0d, x varies: %0d",
             success, held, varied);

    // pre_randomize() runs before and post_randomize() after each
    // successful call.
    q = new;
    success = 0;
    for (i = 0; i < 8; i++) if (q.randomize()) success++;
    $display("Counted: success %0d of 8, pre_randomize %0d, post_randomize %0d",
             success, q.pre_calls, q.post_calls);

    // A state variable makes the constraints infeasible, no 8-bit z lying
    // at or above 256: randomize() returns 0, the random variables retain
    // their previous values, and post_randomize() is not called while
    // pre_randomize() was.
    kept_x = q.x;
    kept_z = q.z;
    q.floor = 256;
    success = q.randomize();
    $display("infeasible: randomize returns %0d, x and z retained: %0d, pre_randomize %0d, post_randomize %0d",
             success, (q.x == kept_x) && (q.z == kept_z), q.pre_calls,
             q.post_calls);
    $finish;
  end
endmodule
