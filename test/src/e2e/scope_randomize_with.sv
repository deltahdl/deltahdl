// 18.12.1: adding constraints to scope variables: the with form of the
// scope randomize applies its constraint block to the local variables, the
// arguments of the call being the random variables and every other
// variable a state variable. The clause's stimulus task calls it twice:
// a, b and c with a below b and their sum below the task argument length,
// and then a and b alone with their difference above length.
module scope_randomize_with;
  int i, first_ok, first_held, second_ok, c_kept, c_moved;
  int c_first, c_second, prev_c;

  task stimulus(int length);
    int a, b, c, success;
    success = std::randomize(a, b, c) with { a < b; a + b < length; };
    first_ok += success;
    if (a < b && a + b < length) first_held++;
    if (c != prev_c) c_moved++;
    prev_c = c;
    c_first = c;
    success = std::randomize(a, b) with { b - a > length; };
    second_ok += success;
    if (b - a > length) c_kept += c == c_first;
  endtask

  initial begin
    first_ok = 0; first_held = 0; second_ok = 0; c_kept = 0; c_moved = 0;
    prev_c = 0;
    for (i = 0; i < 32; i++) stimulus(50);
    // The first call draws a, b and c, a below b and a + b below 50 on
    // every call, c drawn although no constraint names it.
    $display("first call: succeeds in %0d of 32, a < b and a + b < length in %0d, c moved in some: %0d",
             first_ok, first_held, c_moved > 0);
    // The second call draws a and b alone, b - a above 50, and c, no
    // argument of it, is a state variable keeping the first call's value.
    $display("second call: succeeds in %0d of 32, b - a > length with c kept in %0d",
             second_ok, c_kept);
    $finish;
  end
endmodule
