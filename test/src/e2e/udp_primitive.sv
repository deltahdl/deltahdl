// IEEE 1800-2023 §29.4: a combinational UDP's output state depends on nothing
// but the input states of the moment. Every combination this design drives has
// a row below, because §29.3.4 gives every input combination the table leaves
// out the default output state x.
primitive mux2 (mux, control, dataA, dataB);
  output mux;
  input control, dataA, dataB;
  table
    // control dataA dataB   mux
       0       0     0     : 0 ;
       0       0     1     : 0 ;
       0       1     0     : 1 ;
       0       1     1     : 1 ;
       1       0     0     : 0 ;
       1       0     1     : 1 ;
       1       1     0     : 0 ;
       1       1     1     : 1 ;
  endtable
endprimitive

module udp_primitive;
  logic control;
  logic dataA;
  logic dataB;
  wire mux_out;

  // §29.8: `udp_instance ::= [ name_of_instance ] ( output_terminal ,
  // input_terminal { , input_terminal } )`, and the terminals connect in the
  // order the UDP definition declares them, which is mux, control, dataA,
  // dataB.
  mux2 m1 (mux_out, control, dataA, dataB);

  initial begin
    control = 0;
    dataA = 1;
    dataB = 0;
    #1;
    $display("control=0 dataA=1 dataB=0 mux=%b", mux_out);

    control = 1;
    #1;
    $display("control=1 dataA=1 dataB=0 mux=%b", mux_out);

    dataB = 1;
    #1;
    $display("control=1 dataA=1 dataB=1 mux=%b", mux_out);

    control = 0;
    dataA = 0;
    #1;
    $display("control=0 dataA=0 dataB=1 mux=%b", mux_out);
  end
endmodule
