// §38.36.1 (printed page 1133), §37.17 detail 14 (printed page 1026) of IEEE
// 1800-2023: cbStartOfFrame per task call, cbStartOfThread per thread,
// cbCreateObj per new(), cbSizeChange on a queue with the new size. The library
// vpi_acceptance_28_cb_frame_thread_obj_size.c, built beside the run and named
// by vpi_acceptance_28_cb_frame_thread_obj_size.args, is the VPI application
// under test (#4338).
`timescale 1ns/1ns
module top;
  class C; endclass
  C c;
  int q[$];
  task automatic t(); #0; endtask
  initial begin
    #1 q.push_back(7); q.push_back(8);
    #1 void'(q.pop_front());
    t(); t();
    fork #1; #1; join
    c = new; c = new; c = new;
  end
endmodule
