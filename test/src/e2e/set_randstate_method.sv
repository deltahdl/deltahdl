// IEEE 1800-2023 §18.13.5: set_randstate() sets the internal state of an
// object's RNG with the given value, a string obtained from get_randstate();
// the state of the RNG associated with a process is set with the
// set_randstate() method of the process (§9.7). The install is what the RNG
// draws from next: a state read from an object and installed on it again
// replays the draws that followed the read, installed on another object it
// makes that object continue the stream from the same place, the installed
// state reads back, and an object not installed on keeps its own state; a
// process is set the same way, a forked thread given the state continues the
// stream, and the install on the thread does not set the parent process: the
// fork seeds the thread with the parent's next value (§18.14.1), so the parent
// is left where a fork without the install leaves it.
module set_randstate_method;
  class Packet;
    rand bit [15:0] payload;
  endclass

  Packet a, b, c;
  process p;
  string s, t, t2;
  int i, k;
  bit [15:0] seq_a[4], seq_r[4], seq_b[4];
  int unsigned u_a[4], u_r[4], u_c[4];
  int replayed, continued, reads_back, kept, proc_replayed, thread_continued, proc_kept;

  initial begin
    a = new;
    b = new;
    c = new;
    a.srandom(3);
    b.srandom(8);
    c.srandom(8);
    for (i = 0; i < 2; i++) k = a.randomize();
    s = a.get_randstate();
    for (i = 0; i < 4; i++) begin k = a.randomize(); seq_a[i] = a.payload; end
    a.set_randstate(s);
    for (i = 0; i < 4; i++) begin k = a.randomize(); seq_r[i] = a.payload; end
    replayed = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_r[i]) replayed++;
    for (i = 0; i < 2; i++) k = b.randomize();
    for (i = 0; i < 2; i++) k = c.randomize();
    t = c.get_randstate();
    b.set_randstate(s);
    for (i = 0; i < 4; i++) begin k = b.randomize(); seq_b[i] = b.payload; end
    continued = 0;
    for (i = 0; i < 4; i++) if (seq_a[i] == seq_b[i]) continued++;
    $display("object: the state installed again replays %0d of 4, installed on another object it continues the stream in %0d of 4",
             replayed, continued);
    b.set_randstate(s);
    reads_back = b.get_randstate() == s;
    kept = c.get_randstate() == t;
    $display("object: the installed state reads back: %0d, a third object's state kept: %0d", reads_back, kept);

    p = process::self();
    for (i = 0; i < 2; i++) k = $urandom;
    s = p.get_randstate();
    for (i = 0; i < 4; i++) u_a[i] = $urandom;
    p.set_randstate(s);
    for (i = 0; i < 4; i++) u_r[i] = $urandom;
    proc_replayed = 0;
    for (i = 0; i < 4; i++) if (u_a[i] == u_r[i]) proc_replayed++;
    t = p.get_randstate();
    fork
      begin
        process q = process::self();
        q.set_randstate(s);
        for (int j = 0; j < 4; j++) u_c[j] = $urandom;
      end
    join
    thread_continued = 0;
    for (i = 0; i < 4; i++) if (u_a[i] == u_c[i]) thread_continued++;
    t2 = p.get_randstate();
    p.set_randstate(t);
    fork
      begin
        for (int j = 0; j < 4; j++) k = $urandom;
      end
    join
    proc_kept = p.get_randstate() == t2;
    $display("process: the state installed again replays %0d of 4, installed on a forked thread it continues the stream in %0d of 4, the parent left where a fork without the install leaves it: %0d",
             proc_replayed, thread_continued, proc_kept);
    $finish;
  end
endmodule
