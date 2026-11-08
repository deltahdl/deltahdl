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
    $display("first call: succeeds in %0d of 32, a < b and a + b < length in %0d, c moved in some: %0d",
             first_ok, first_held, c_moved > 0);
    $display("second call: succeeds in %0d of 32, b - a > length with c kept in %0d",
             second_ok, c_kept);
    $finish;
  end
endmodule
