// IEEE 1800-2023 §29.4: in a combinational UDP "the output state is determined
// solely as a function of the current input states". Every combination this
// design drives has a row below, because §29.3.4 rules that "All combinations
// of input values that are not explicitly specified result in a default output
// state of x".
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
  // input_terminal { , input_terminal } )`, and "The terminal connection order
  // is as specified in the UDP definition", which is mux, control, dataA,
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
