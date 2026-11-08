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

  function bit gen_stim();
    bit success, rd_wr;
    success = randomize(addr, data, rd_wr);
    calls += success;
    return rd_wr;
  endfunction

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

    a = 1; b = 2;
    ok = std::randomize() with { a < b; };
    $display("no argument, a < b: returns %0d, values kept: %0d", ok, a == 1 && b == 2);
    a = 3;
    ok = std::randomize() with { a < b; };
    $display("no argument, a > b: returns %0d, values kept: %0d", ok, a == 3 && b == 2);

    ok = std::randomize(a) with { a > 300; };
    $display("unsatisfiable: returns %0d, value kept: %0d", ok, a == 3);
    $finish;
  end
endmodule
