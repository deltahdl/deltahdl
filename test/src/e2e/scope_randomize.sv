// 18.12: randomization of scope variables: std::randomize(), or the bare
// randomize() outside a class method, behaves as the class randomize
// method but over the variables of the current scope, its arguments the
// random variables; it returns 1 where it sets all of them to valid values
// and 0 otherwise, and called with no argument it changes no variable and
// checks its constraints, 0 where one is false and 1 otherwise. The
// clause's stim is run beside its class form, stimc.
class stimc;
  rand bit [15:0] addr;
  rand bit [31:0] data;
  rand bit rd_wr;
endclass

module scope_randomize;
  bit [15:0] addr;
  bit [31:0] data;
  bit [7:0] a, b;
  int i, calls, addr_moved, data_moved, reads, writes, copied, ok;
  bit [15:0] prev_addr;
  bit [31:0] prev_data;
  bit rd;
  stimc p;

  // The clause's gen_stim: addr and data of module scope and rd_wr local
  // to the function, all three assigned by the scope randomize.
  function bit gen_stim();
    bit success, rd_wr;
    success = randomize(addr, data, rd_wr);
    calls += success;
    return rd_wr;
  endfunction

  // The clause's class form of the same.
  function bit gen_stim_class(stimc p);
    bit [15:0] addr;
    bit [31:0] data;
    bit success;
    success = p.randomize();
    calls += success;
    addr = p.addr;
    data = p.data;
    copied += addr == p.addr && data == p.data;
    return p.rd_wr;
  endfunction

  initial begin
    // Each call sets all three: addr and data move between calls and both
    // values of rd_wr are seen over 32 calls.
    calls = 0; addr_moved = 0; data_moved = 0; reads = 0; writes = 0;
    for (i = 0; i < 32; i++) begin
      prev_addr = addr;
      prev_data = data;
      rd = gen_stim();
      if (addr != prev_addr) addr_moved++;
      if (data != prev_data) data_moved++;
      if (rd) reads++; else writes++;
    end
    $display("gen_stim: succeeds in %0d of 32, addr moved in some: %0d, data moved in some: %0d, rd_wr both seen: %0d",
             calls, addr_moved > 0, data_moved > 0, reads > 0 && writes > 0);

    p = new;
    calls = 0; copied = 0;
    for (i = 0; i < 32; i++) rd = gen_stim_class(p);
    $display("stimc: succeeds in %0d of 32, addr and data copied in %0d", calls, copied);

    // No argument: the constraints are checked on the current values and
    // no variable changes.
    a = 1; b = 2;
    ok = std::randomize() with { a < b; };
    $display("no argument, a < b: returns %0d, values kept: %0d", ok, a == 1 && b == 2);
    a = 3;
    ok = std::randomize() with { a < b; };
    $display("no argument, a > b: returns %0d, values kept: %0d", ok, a == 3 && b == 2);

    // A random variable that cannot be set to a valid value: 0, and a
    // keeps its value.
    ok = std::randomize(a) with { a > 300; };
    $display("unsatisfiable: returns %0d, value kept: %0d", ok, a == 3);
    $finish;
  end
endmodule
