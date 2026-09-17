// 18.8: disabling random variables with rand_mode(): an inactive variable
// is not randomized and is a state variable to the solver, every variable
// is active to begin with, the call on the object alone affects all of
// its variables, an element of an unpacked array is named by its index,
// and the nonvoid form reports the state.
class Packet;
  rand integer source_value, dest_value;
  rand bit [7:0] arr[4];
  constraint follows { dest_value == source_value + 1; }
endclass

module rand_mode;
  Packet packet_a;
  int ret, i, held, moved, related, before_source, before_dest;

  initial begin
    packet_a = new;
    // All random variables are initially active.
    $display("initially: source_value %0d, dest_value %0d, arr[1] %0d",
             packet_a.source_value.rand_mode(), packet_a.dest_value.rand_mode(),
             packet_a.arr[1].rand_mode());

    // The clause's example: all variables turned off through the object,
    // then source_value alone turned on, and dest_value's state read.
    packet_a.rand_mode(0);
    packet_a.source_value.rand_mode(1);
    ret = packet_a.dest_value.rand_mode();
    $display("the example: source_value %0d, dest_value %0d, ret %0d",
             packet_a.source_value.rand_mode(), packet_a.dest_value.rand_mode(),
             ret);

    // An inactive variable is not randomized and is a state variable the
    // solver reads: with dest_value held at 41, source_value is drawn as 40
    // on every call, where before either was inactive the pair varied.
    packet_a.dest_value = 41;
    held = 0;
    for (i = 0; i < 32; i++) begin
      void'(packet_a.randomize());
      if (packet_a.dest_value == 41 && packet_a.source_value == 40) held++;
    end
    $display("dest_value inactive at 41: source_value drawn 40 with dest_value kept in %0d of 32",
             held);

    // Turned back on, dest_value varies with source_value and the
    // constraint still holds.
    packet_a.dest_value.rand_mode(1);
    moved = 0;
    related = 0;
    for (i = 0; i < 32; i++) begin
      void'(packet_a.randomize());
      if (packet_a.dest_value != 41) moved++;
      if (packet_a.dest_value == packet_a.source_value + 1) related++;
    end
    $display("dest_value active again: moved from 41 in some: %0d, the constraint held in %0d of 32",
             moved > 0, related);

    // An element of an unpacked array named by its index: arr[2] held at 9
    // keeps it while the other elements are drawn.
    packet_a.arr.rand_mode(1);
    packet_a.arr[2] = 9;
    packet_a.arr[2].rand_mode(0);
    held = 0;
    moved = 0;
    for (i = 0; i < 32; i++) begin
      void'(packet_a.randomize());
      if (packet_a.arr[2] == 9) held++;
      if (packet_a.arr[0] != 9 || packet_a.arr[1] != 9 || packet_a.arr[3] != 9)
        moved++;
    end
    $display("arr[2] inactive: arr[2] %0d, kept at 9 in %0d of 32, the others drawn in some: %0d",
             packet_a.arr[2].rand_mode(), held, moved > 0);
    $finish;
  end
endmodule
