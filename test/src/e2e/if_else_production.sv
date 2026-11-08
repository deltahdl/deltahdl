module if_else_production;
  int depth, nothing, generated;

  task do_push();
    $write("push ");
  endtask

  task do_pop();
    $write("pop ");
  endtask

  initial begin
    depth = 0;
    randsequence( main )
      main  : PP_OP PP_OP PP_OP PP_OP PP_OP ;
      PP_OP : if ( depth < 2 ) PUSH else POP ;
      PUSH  : { ++depth; do_push(); } ;
      POP   : { --depth; do_pop(); } ;
    endsequence
    $display("depth %0d", depth);

    nothing = 1;
    generated = 0;
    randsequence( main )
      main   : if ( depth > 5 ) MARK ;
      MARK   : { nothing = 0; } ;
    endsequence
    randsequence( main )
      main   : if ( depth == 1 && nothing ) MARK ;
      MARK   : { generated = 1; } ;
    endsequence
    $display("if without else and a false expression generates nothing: %0d, a true expression of two operands generates its production: %0d",
             nothing, generated);
    $finish;
  end
endmodule
