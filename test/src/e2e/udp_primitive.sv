primitive mux2 (mux, control, dataA, dataB);
  output mux;
  input control, dataA, dataB;
  table
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
