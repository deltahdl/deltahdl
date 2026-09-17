// IEEE 1800-2023 §18.17.6: break and return terminate a production
// prematurely and differ in the scope they exit. A break executed in a
// production code block jumps out of the randsequence block, so the clause's
// SETUP breaking when the fifo is full leaves COMMAND and DATA ungenerated
// and execution continues at the next statement, while a break inside a
// loop statement terminates the smallest enclosing loop as §12.8 has it. A
// return aborts the current production and generation continues with the
// next production, so the clause's TOP : P1 P2 displays A B C A B C with
// flag 0, A B C A with flag 1, P2 aborted after A, and A C A C with flag 2,
// B aborted twice.
module break_and_return;
  int flag, fifo_length, max_length, command, data, next, loop_ended, went_on, i, ungenerated, loop_only;

  initial begin
    for (flag = 0; flag < 3; flag++) begin
      $write("flag == %0d ==>", flag);
      randsequence()
        TOP : P1 P2 ;
        P1  : A B C ;
        P2  : A { if ( flag == 1 ) return; } B C ;
        A   : { $write( " A" ); } ;
        B   : { if ( flag == 2 ) return; $write( " B" ); } ;
        C   : { $write( " C" ); } ;
      endsequence
      $display("");
    end

    fifo_length = 4; max_length = 4; command = 0; data = 0; next = 0;
    randsequence()
      WRITE   : SETUP DATA ;
      SETUP   : { if ( fifo_length >= max_length ) break; } COMMAND ;
      COMMAND : { command = 1; } ;
      DATA    : { data = 1; } ;
    endsequence
    next = 1;
    loop_ended = 0; went_on = 0;
    randsequence()
      LOOP : { for (i = 0; i < 10; i++) begin if (i == 3) break; end loop_ended = i == 3; } AFTER ;
      AFTER : { went_on = 1; } ;
    endsequence
    ungenerated = command == 0 && data == 0;
    loop_only = loop_ended && went_on;
    $display("break: with the fifo full, COMMAND and DATA are not generated: %0d, the next statement runs: %0d; a break in a loop inside a code block ends the loop at 3 and generation goes on: %0d",
             ungenerated, next, loop_only);
    $finish;
  end
endmodule
