// A.2.4 spells class_new `new [ ( list_of_arguments ) ]`, and A.8.2 lets a
// list_of_arguments bind its arguments by the formals' names, whether from its
// first element or after ordered ones. The first call below names both formals
// in the reverse of their order and the second names one after an ordered
// value, so a constructor that took them by position would print 35 and 49.
// This is the form uvm_factory.svh writes at line 1185 for every override.
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
