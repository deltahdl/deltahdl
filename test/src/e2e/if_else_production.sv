// IEEE 1800-2023 §18.17.2: a production is made conditional with an if-else
// production statement: the expression may be any expression evaluating to a
// Boolean value; when it is true the production after it is generated,
// otherwise the one after the optional else. The clause's PP_OP generates
// PUSH while depth is below 2 and POP otherwise, PUSH and POP moving depth
// in their code blocks, so five PP_OP from a depth of 0 generate push, push,
// pop, push, pop and leave depth at 1; and with no else a false expression
// generates nothing while a true expression of two operands generates its
// production.
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
