// IEEE 1800-2023 §18.17.5: rand join randomly interleaves two or more
// production sequences while keeping the relative order of each, so the
// clause's TOP : rand join S1 S2 with S1 : A B and S2 : C D produces one of
// A B C D, A C B D, A C D B, C D A B, C A B D and C A D B on every run and
// all six over many; the optional real expression in 0.0 to 1.0 is the
// degree to which the length of the sequences still to be interleaved
// affects the choice, 0.0 giving the shortest remaining sequences priority
// (A B C D and C D A B), 1.0 the longest (the four interleaved ones), and
// the default 0.5 prioritizing no length, so each of the six is near a sixth
// of the runs; and nonterminals are interleaved to a depth of 1, so the two
// items of a nonterminal inside S1 stay adjacent.
module rand_join;
  int i, p, code, seq[4], counts[6], codes[6];
  int every, all_six, near_sixth, shortest_first, longest_first, adjacent;

  function automatic int index_of(int c);
    int k;
    for (k = 0; k < 6; k++) if (codes[k] == c) return k;
    return -1;
  endfunction

  initial begin
    codes[0] = 1234; codes[1] = 1324; codes[2] = 1342;
    codes[3] = 3412; codes[4] = 3124; codes[5] = 3142;
    for (i = 0; i < 6; i++) counts[i] = 0;
    every = 1;
    for (i = 0; i < 600; i++) begin
      p = 0;
      randsequence( TOP )
        TOP : rand join S1 S2 ;
        S1  : A B ;
        S2  : C D ;
        A   : { seq[p] = 1; p++; } ;
        B   : { seq[p] = 2; p++; } ;
        C   : { seq[p] = 3; p++; } ;
        D   : { seq[p] = 4; p++; } ;
      endsequence
      code = seq[0] * 1000 + seq[1] * 100 + seq[2] * 10 + seq[3];
      if (index_of(code) < 0) every = 0;
      else counts[index_of(code)]++;
    end
    all_six = 1; near_sixth = 1;
    for (i = 0; i < 6; i++) begin
      if (counts[i] == 0) all_six = 0;
      if (counts[i] < 50 || counts[i] > 150) near_sixth = 0;
    end
    $display("example: 600 runs each produce one of the six orders keeping A before B and C before D: %0d, all six seen: %0d, each near a sixth: %0d",
             every, all_six, near_sixth);

    for (i = 0; i < 6; i++) counts[i] = 0;
    for (i = 0; i < 600; i++) begin
      p = 0;
      randsequence( TOP )
        TOP : rand join (0.0) S1 S2 ;
        S1  : A B ;
        S2  : C D ;
        A   : { seq[p] = 1; p++; } ;
        B   : { seq[p] = 2; p++; } ;
        C   : { seq[p] = 3; p++; } ;
        D   : { seq[p] = 4; p++; } ;
      endsequence
      code = seq[0] * 1000 + seq[1] * 100 + seq[2] * 10 + seq[3];
      if (index_of(code) >= 0) counts[index_of(code)]++;
    end
    shortest_first = counts[0] + counts[3] > 300;
    for (i = 0; i < 6; i++) counts[i] = 0;
    for (i = 0; i < 600; i++) begin
      p = 0;
      randsequence( TOP )
        TOP : rand join (1.0) S1 S2 ;
        S1  : A B ;
        S2  : C D ;
        A   : { seq[p] = 1; p++; } ;
        B   : { seq[p] = 2; p++; } ;
        C   : { seq[p] = 3; p++; } ;
        D   : { seq[p] = 4; p++; } ;
      endsequence
      code = seq[0] * 1000 + seq[1] * 100 + seq[2] * 10 + seq[3];
      if (index_of(code) >= 0) counts[index_of(code)]++;
    end
    longest_first = counts[1] + counts[2] + counts[4] + counts[5] > 300;
    $display("expression: with 0.0 A B C D and C D A B take more than half of 600: %0d, with 1.0 the four interleaved orders take more than half: %0d",
             shortest_first, longest_first);

    adjacent = 1;
    for (i = 0; i < 100; i++) begin
      p = 0;
      randsequence( TOP )
        TOP : rand join S1 S2 ;
        S1  : A ;
        S2  : C D ;
        A   : A1 A2 ;
        A1  : { seq[p] = 1; p++; } ;
        A2  : { seq[p] = 2; p++; } ;
        C   : { seq[p] = 3; p++; } ;
        D   : { seq[p] = 4; p++; } ;
      endsequence
      if (!((seq[0] == 1 && seq[1] == 2) || (seq[1] == 1 && seq[2] == 2) || (seq[2] == 1 && seq[3] == 2))) adjacent = 0;
    end
    $display("depth: the two items of a nonterminal inside S1 stay adjacent in all of 100: %0d", adjacent);
    $finish;
  end
endmodule
