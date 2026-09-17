// IEEE 1800-2023 §18.17: a randsequence grammar is composed of productions,
// each a name and production items, terminals being code blocks and
// nonterminals decomposed into them; a production list streams its items in
// sequence and lists separated by | are choices the generator makes at
// random, so the clause's example, main : first second done with first
// choosing add or dec and second pop or push, yields one of add pop done,
// add push done, dec pop done and dec push done, each of which 200 runs
// reach. As each production is generated the side effects of its code block
// produce the stimulus; the statement creates no loop of itself but a
// recursive production will loop, so a production naming itself runs one or
// more times and stops; the statement is an automatic scope and each code
// block an anonymous automatic scope, a static variable needing the static
// prefix, so a static counter in a code block sees every activation while an
// automatic one starts afresh each time; and the production named in the
// parentheses is the top-level one, the first production when none is named,
// so randsequence(second) runs only the second production.
module randsequence_statement;
  int i, f, s, d, n, sv, av;
  int seen[4], every, finite, only_second, from_first;

  initial begin
    for (i = 0; i < 4; i++) seen[i] = 0;
    every = 1;
    for (i = 0; i < 200; i++) begin
      f = 0; s = 0; d = 0;
      randsequence( main )
        main   : first second done ;
        first  : add | dec ;
        second : pop | push ;
        done   : { d = 1; } ;
        add    : { f = 1; } ;
        dec    : { f = 2; } ;
        pop    : { s = 1; } ;
        push   : { s = 2; } ;
      endsequence
      if (f == 1 && s == 1 && d == 1) seen[0] = 1;
      else if (f == 1 && s == 2 && d == 1) seen[1] = 1;
      else if (f == 2 && s == 1 && d == 1) seen[2] = 1;
      else if (f == 2 && s == 2 && d == 1) seen[3] = 1;
      else every = 0;
    end
    $display("example: 200 runs produced add pop done, add push done, dec pop done and dec push done: %0d %0d %0d %0d, every run one of the four: %0d",
             seen[0], seen[1], seen[2], seen[3], every);

    n = 0;
    randsequence( chain )
      chain : { n++; } | { n++; } chain ;
    endsequence
    finite = n >= 1;
    $display("recursion: a production naming itself ran one or more times and stopped: %0d", finite);

    randsequence( main )
      main  : count count count ;
      count : { static int total = 0; int fresh = 0; total++; fresh++; sv = total; av = fresh; } ;
    endsequence
    $display("scope: a code block's static variable counted the activations: %0d, its automatic variable started afresh each time: %0d", sv, av);

    f = 0; s = 0; d = 0;
    randsequence( second )
      main   : first second done ;
      first  : { f = 1; } ;
      second : { s = 1; } ;
      done   : { d = 1; } ;
    endsequence
    only_second = f == 0 && s == 1 && d == 0;
    f = 0; s = 0; d = 0;
    randsequence()
      main   : first second done ;
      first  : { f = 1; } ;
      second : { s = 1; } ;
      done   : { d = 1; } ;
    endsequence
    from_first = f == 1 && s == 1 && d == 1;
    $display("top: randsequence(second) ran only the second production: %0d, unnamed it started at the first: %0d", only_second, from_first);
    $finish;
  end
endmodule
