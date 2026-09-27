// §21.6: plusargs are the arguments "provided to the simulation" that start
// with +, and $test$plusargs and $value$plusargs search the ones "present on
// the command line". This case's .args gives +HELLO, +TEST=5 and +NAME=bob, so
// the queries below answer from the invocation itself, through a package
// function as well as directly.
package pa;
  function automatic int has(string s);
    return $test$plusargs(s);
  endfunction
  function automatic int val(string s, ref int v);
    return $value$plusargs(s, v);
  endfunction
endpackage

module plusargs_command_line;
  import pa::*;
  int v = 77, r1, r2;
  string sv = "keep", pat = "NAME=%s";

  initial begin
    r1 = has("HELLO");
    r2 = val("TEST=%d", v);
    $display("%0d %0d %0d", r1, r2, v);
    r1 = $test$plusargs("X");
    r2 = $value$plusargs(pat, sv);
    $display("%0d %0d %s", r1, r2, sv);
  end
endmodule
