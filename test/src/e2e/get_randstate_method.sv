// IEEE 1800-2023 §18.13.4: get_randstate() retrieves the current internal
// state of an object's RNG as a string, of a length and format the
// implementation chooses; the state of the RNG associated with a process is
// retrieved with the get_randstate() method of the process (§9.7). The
// retrieval is a read: two retrievals with no draw between them agree, a draw
// moves the state, two objects seeded alike hold the same state, and a state
// retrieved and installed again with set_randstate() replays the draws that
// followed its retrieval.
module get_randstate_method;
  class Packet;
    rand bit [15:0] payload;
  endclass

  Packet a, b;
  process p;
  string s1, s2, s3;
  int i, k;
  bit [15:0] seq_a[4], seq_b[4];
  int unsigned u_a[4], u_b[4];
  int has_length, agree, alike, moved, kept, replayed, proc_replayed;

  initial begin
    a = new;
    b = new;
    a.srandom(7);
    b.srandom(7);
    s1 = a.get_randstate();
    s2 = a.get_randstate();
    s3 = b.get_randstate();
    has_length = s1.len() > 0;
    agree = s1 == s2;
    alike = s1 == s3;
    $display("object: a string of length above 0: %0d, two reads agree: %0d, an object seeded alike agrees: %0d",
             has_length, agree, alike);
    for (i = 0; i < 4; i++) begin k = a.randomize(); seq_a[i] = a.payload; end
    s2 = a.get_randstate();
    moved = s1 != s2;
    s2 = b.get_randstate();
    kept = s3 == s2;
    $display("object: moved by four draws: %0d, the other object's state kept: %0d", moved, kept);
    a.set_randstate(s1);
    for (i = 0; i < 4; i++) begin k = a.randomize(); seq_b[i] = a.payload; end
    replayed = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_b[i]) replayed++;
    $display("object: the retrieved state installed again replays %0d of 4", replayed);

    p = process::self();
    s1 = p.get_randstate();
    s2 = p.get_randstate();
    has_length = s1.len() > 0;
    agree = s1 == s2;
    $display("process: a string of length above 0: %0d, two reads agree: %0d", has_length, agree);
    for (i = 0; i < 4; i++) u_a[i] = $urandom;
    s2 = p.get_randstate();
    moved = s1 != s2;
    p.set_randstate(s1);
    for (i = 0; i < 4; i++) u_b[i] = $urandom;
    proc_replayed = 0;
    for (i = 0; i < 4; i++) if (u_a[i] == u_b[i]) proc_replayed++;
    $display("process: moved by four draws: %0d, the retrieved state installed again replays %0d of 4",
             moved, proc_replayed);
    $finish;
  end
endmodule
