// IEEE 1800-2023 §18.17.7: data is passed down to a production with the
// syntax of a task call, its formal arguments declared as a task's and
// available throughout the production, so the clause's gen(string s =
// "done") prints what each of five productions passes and its default when
// main passes nothing; a production with a return type returns a value with
// return, read in the code blocks of the production that generated it
// through an implicit variable named after it, an array indexed from 1 when
// it appears more than once in the rule with elements assigned in syntactic
// order, so in the clause's Example 1 value[1] and value[2] hold the two
// values in order and operator holds the string; in Example 2 B[1] holds the
// count after the first B, C the count after the five repeated Cs, B[2] the
// count after the second B, and D[1] holds D(5) when cond is true and D[2]
// holds D(20) when it is false; and a whole sequence can be generated into a
// queue for later processing, as the clause's GenQueue does, bounded by its
// arguments at both ends with every item within them.
module value_passing;
  int i, p, cnt, cond, first_ok, second_ok, third_ok, every, b1, c_after, b2, d1, d2, low, high;
  int b1_range, c_five, b2_range, d_true, d_false, bounded, in_bounds, sized, op_ok;
  int q[$];

  initial begin
    every = 1;
    for (i = 0; i < 200; i++) begin
      p = 0; first_ok = 0; second_ok = 0; third_ok = 0;
      randsequence( main )
        main                       : first second gen ;
        first                      : add | dec ;
        second                     : pop | push ;
        add                        : gen("add") ;
        dec                        : gen("dec") ;
        pop                        : gen("pop") ;
        push                       : gen("push") ;
        gen( string s = "done" )   : { if (p == 0) first_ok = s == "add" || s == "dec";
                                       if (p == 1) second_ok = s == "pop" || s == "push";
                                       if (p == 2) third_ok = s == "done";
                                       p++; } ;
      endsequence
      if (!(first_ok && second_ok && third_ok && p == 3)) every = 0;
    end
    $display("arguments: 200 runs of the clause's gen each print a first word, a second word and the default done: %0d", every);

    cnt = 0;
    randsequence( bin_op )
      void bin_op    : value operator value
                       { op_ok = operator == "+" || operator == "-" || operator == "*";
                         $display("example 1: operator is one of the three strings: %0d, value[1] is the first value drawn: %0d, value[2] the second: %0d", op_ok, value[1], value[2]); }
                       ;
      bit [7:0] value : { cnt++; return cnt; } ;
      string operator : { return "+" ; }
                      | { return "-" ; }
                      | { return "*" ; }
                      ;
    endsequence

    for (cond = 0; cond < 2; cond++) begin
      randsequence( A )
        void A  : A1 A2 ;
        void A1 : { cnt = 1; } B repeat(5) C B
                  { b1 = B[1]; c_after = C; b2 = B[2]; }
                  ;
        void A2 : if (cond) D(5) else D(20)
                  { if (cond) d1 = D[1]; else d2 = D[2]; }
                  ;
        int B   : C { return C; }
                | C C { return C[2]; }
                | C C C { return C[3]; }
                ;
        int C   : { cnt = cnt + 1; return cnt; } ;
        int D (int prm) : { return prm; } ;
      endsequence
      if (cond == 0) begin
        b1_range = b1 >= 2 && b1 <= 4;
        c_five = c_after == b1 + 5;
        b2_range = b2 >= c_after + 1 && b2 <= c_after + 3;
      end
    end
    d_true = d1 == 5;
    d_false = d2 == 20;
    $display("example 2: b1 is the count after one to three Cs: %0d, c is b1 + 5 after the five repeated Cs: %0d, b2 is c plus one to three: %0d, with cond D[1] is D(5): %0d, without cond D[2] is D(20): %0d",
             b1_range, c_five, b2_range, d_true, d_false);

    low = 3; high = 9;
    randsequence()
      TOP       : BOUND(low) LIST BOUND(high) ;
      LIST      : LIST ITEM := 8 { q = { q, ITEM }; }
                | ITEM := 2 { q = { q, ITEM }; }
                ;
      int ITEM  : { return $urandom_range( low, high ); } ;
      BOUND(int b) : { q = { q, b }; } ;
    endsequence
    bounded = q[0] == low && q[q.size() - 1] == high;
    in_bounds = 1;
    for (i = 0; i < q.size(); i++) if (q[i] < low || q[i] > high) in_bounds = 0;
    sized = q.size() >= 3;
    $display("queue: the generated queue starts at low and ends at high: %0d, every item is within them: %0d, it holds three or more: %0d",
             bounded, in_bounds, sized);
    $finish;
  end
endmodule
