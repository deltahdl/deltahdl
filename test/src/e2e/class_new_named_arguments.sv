class Packet;
  int command;
  int address;
  function new(int cmd, int addr = 7);
    command = cmd;
    address = addr;
  endfunction
endclass

module class_new_named_arguments;
  initial begin
    Packet p;
    p = new(.addr(3), .cmd(5));
    $display("%0d", p.command * 10 + p.address);
    p = new(9, .addr(4));
    $display("%0d", p.command * 10 + p.address);
    p = new(.addr(), .cmd(2));
    $display("%0d", p.command * 10 + p.address);
  end
endmodule
